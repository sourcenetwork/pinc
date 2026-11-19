//! How commands reach a TPM: the Linux kernel resource manager or a simulator socket.
//!
//! Invariants: one `transmit` is exactly one command and its one response; a response is returned whole or the
//! call fails. Neither transport interprets the TPM message.

use std::fs::{File, OpenOptions};
use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::vec;
use std::vec::Vec;

/// The largest response a TPM can send (`TPM_MAX_COMMAND_SIZE`), with room for the kernel's own limit.
const MAX_RESPONSE: usize = 8192;

/// The Microsoft simulator command that carries a TPM command on the command port.
const TPM_SEND_COMMAND: u32 = 8;
/// Platform port: apply power.
const TPM_SIGNAL_POWER_ON: u32 = 1;
/// Platform port: make NV memory available.
const TPM_SIGNAL_NV_ON: u32 = 11;

/// A link that carries one TPM command at a time and returns its response.
pub trait Transport: Send {
    /// Send `command` and return the complete response.
    ///
    /// # Errors
    /// Any I/O failure, or a response the link itself cannot frame.
    fn transmit(&mut self, command: &[u8]) -> io::Result<Vec<u8>>;
}

/// A TPM character device, normally the kernel resource manager `/dev/tpmrm0`.
#[derive(Debug)]
pub struct DeviceTransport(File);

impl DeviceTransport {
    /// The kernel resource manager, which virtualizes handles so many users can share one TPM.
    pub const RESOURCE_MANAGER: &'static str = "/dev/tpmrm0";

    /// Open the device at `path`.
    ///
    /// # Errors
    /// Any failure to open it, such as a missing device or a lack of permission.
    pub fn open(path: &str) -> io::Result<Self> {
        OpenOptions::new().read(true).write(true).open(path).map(Self)
    }
}

impl Transport for DeviceTransport {
    fn transmit(&mut self, command: &[u8]) -> io::Result<Vec<u8>> {
        // The kernel takes one command per write and returns one response per read.
        if self.0.write(command)? != command.len() {
            return Err(io::ErrorKind::WriteZero.into());
        }
        let mut buf = vec![0u8; MAX_RESPONSE];
        let n = self.0.read(&mut buf)?;
        buf.truncate(n);
        Ok(buf)
    }
}

/// A simulator reached over TCP in the Microsoft simulator protocol (what `swtpm` speaks on its server port).
///
/// A command goes out as `TPM_SEND_COMMAND`, a locality byte and a length, each big-endian; the response is a
/// length, the TPM response and a zero acknowledgement.
#[derive(Debug)]
pub struct SimTransport {
    command: TcpStream,
    locality: u8,
}

impl SimTransport {
    /// Connect to the command port at `command`.
    ///
    /// # Errors
    /// Any connection failure.
    pub fn connect(command: impl ToSocketAddrs) -> io::Result<Self> {
        let command = TcpStream::connect(command)?;
        command.set_nodelay(true)?;
        Ok(Self { command, locality: 0 })
    }

    /// Power on a simulator that has a separate platform port (the Microsoft reference simulator): `power_on`
    /// then `NV_ON` on the platform port at `platform`, then connect to the command port at `command`.
    ///
    /// A simulator without a platform port (`swtpm`) is started by its own flags; use [`SimTransport::connect`].
    ///
    /// # Errors
    /// Any connection failure, or a platform port that does not acknowledge a signal.
    pub fn power_on(command: impl ToSocketAddrs, platform: impl ToSocketAddrs) -> io::Result<Self> {
        let mut plat = TcpStream::connect(platform)?;
        for signal in [TPM_SIGNAL_POWER_ON, TPM_SIGNAL_NV_ON] {
            plat.write_all(&signal.to_be_bytes())?;
            let mut ack = [0u8; 4];
            plat.read_exact(&mut ack)?;
            if ack != [0; 4] {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "platform port refused a signal",
                ));
            }
        }
        Self::connect(command)
    }
}

impl Transport for SimTransport {
    fn transmit(&mut self, command: &[u8]) -> io::Result<Vec<u8>> {
        let len = u32::try_from(command.len()).map_err(|_| io::ErrorKind::InvalidInput)?;
        let mut frame = Vec::with_capacity(command.len() + 9);
        frame.extend_from_slice(&TPM_SEND_COMMAND.to_be_bytes());
        frame.push(self.locality);
        frame.extend_from_slice(&len.to_be_bytes());
        frame.extend_from_slice(command);
        self.command.write_all(&frame)?;

        let mut size = [0u8; 4];
        self.command.read_exact(&mut size)?;
        let size = usize::try_from(u32::from_be_bytes(size)).map_err(|_| io::ErrorKind::InvalidData)?;
        if size > MAX_RESPONSE {
            return Err(io::ErrorKind::InvalidData.into());
        }
        let mut response = vec![0u8; size];
        self.command.read_exact(&mut response)?;
        let mut ack = [0u8; 4];
        self.command.read_exact(&mut ack)?;
        if ack != [0; 4] {
            return Err(io::ErrorKind::InvalidData.into());
        }
        Ok(response)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing)]
mod tests {
    use std::net::TcpListener;
    use std::thread;

    use super::*;

    #[test]
    fn platform_port_gets_power_on_then_nv_on_and_frames_follow_the_protocol() {
        let plat = TcpListener::bind("127.0.0.1:0").unwrap();
        let cmd = TcpListener::bind("127.0.0.1:0").unwrap();
        let (plat_addr, cmd_addr) = (plat.local_addr().unwrap(), cmd.local_addr().unwrap());
        let server = thread::spawn(move || {
            let (mut p, _) = plat.accept().unwrap();
            let mut seen = Vec::new();
            for _ in 0..2 {
                let mut sig = [0u8; 4];
                p.read_exact(&mut sig).unwrap();
                seen.push(u32::from_be_bytes(sig));
                p.write_all(&[0; 4]).unwrap();
            }
            let (mut c, _) = cmd.accept().unwrap();
            let mut head = [0u8; 9];
            c.read_exact(&mut head).unwrap();
            let mut body = vec![0u8; u32::from_be_bytes([head[5], head[6], head[7], head[8]]) as usize];
            c.read_exact(&mut body).unwrap();
            c.write_all(&2u32.to_be_bytes()).unwrap();
            c.write_all(&[0xAA, 0xBB]).unwrap();
            c.write_all(&[0; 4]).unwrap();
            (seen, head, body)
        });
        let mut t = SimTransport::power_on(cmd_addr, plat_addr).unwrap();
        assert_eq!(t.transmit(&[1, 2, 3]).unwrap(), vec![0xAA, 0xBB]);
        let (seen, head, body) = server.join().unwrap();
        assert_eq!(seen, [1, 11]);
        assert_eq!(head, [0, 0, 0, 8, 0, 0, 0, 0, 3]);
        assert_eq!(body, [1, 2, 3]);
    }
}
