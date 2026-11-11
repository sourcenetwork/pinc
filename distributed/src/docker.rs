//! The Docker command line, as the container backend uses it: start, inspect, run a program in, pause and remove
//! containers by name and label. The job user is in the `docker` group, so nothing here needs root.

use std::process::Stdio;

use crate::error::{Error, Result};
use crate::plan::LABEL;

/// Run `docker` with `args` and return what it printed.
///
/// # Errors
/// Docker is missing or the command failed.
pub async fn docker(args: &[&str]) -> Result<String> {
    let out = tokio::process::Command::new("docker")
        .args(args)
        .stdin(Stdio::null())
        .output()
        .await
        .map_err(|e| Error::Host(format!("docker did not start ({e}); install Docker and add this user to the docker group")))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(Error::Command {
            cmd: format!("docker {}", args.join(" ")),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        })
    }
}

/// Every container carrying the harness's label, any run: (name, run id).
///
/// # Errors
/// Docker failed.
pub async fn labelled() -> Result<Vec<(String, String)>> {
    let filter = format!("label={LABEL}");
    let fmt = format!("{{{{.Names}}}}\t{{{{.Label \"{LABEL}\"}}}}");
    let out = docker(&["ps", "-a", "--filter", &filter, "--format", &fmt]).await?;
    Ok(out
        .lines()
        .filter_map(|l| {
            let (n, r) = l.split_once('\t')?;
            Some((n.to_owned(), r.to_owned()))
        })
        .collect())
}

/// What `docker inspect` says about a running container.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Info {
    /// The full id.
    pub id: String,
    /// The process id of its first process on the host.
    pub pid: u32,
}

/// Inspect containers by name, in order.
///
/// # Errors
/// Docker failed, or a container is not running.
pub async fn inspect(names: &[String]) -> Result<Vec<Info>> {
    if names.is_empty() {
        return Ok(Vec::new());
    }
    let mut args = vec!["inspect", "--format", "{{.Id}} {{.State.Pid}}"];
    args.extend(names.iter().map(String::as_str));
    let out = docker(&args).await?;
    let infos: Vec<Info> = out
        .lines()
        .filter_map(|l| {
            let (id, pid) = l.split_once(' ')?;
            Some(Info {
                id: id.to_owned(),
                pid: pid.trim().parse().ok().filter(|p| *p > 0)?,
            })
        })
        .collect();
    if infos.len() == names.len() {
        Ok(infos)
    } else {
        Err(Error::Host("a container stopped right after it started; see `docker logs`".into()))
    }
}

/// Remove containers by name, whatever their state.
///
/// # Errors
/// Docker failed.
pub async fn remove(names: &[String]) -> Result<()> {
    for chunk in names.chunks(64) {
        let mut args = vec!["rm", "-f"];
        args.extend(chunk.iter().map(String::as_str));
        docker(&args).await?;
    }
    Ok(())
}

/// The image's id, pulling it when it is not here.
///
/// # Errors
/// The image is neither here nor pullable.
pub async fn ensure_image(image: &str) -> Result<String> {
    if let Ok(id) = docker(&["image", "inspect", "--format", "{{.Id}}", image]).await {
        return Ok(id.trim().to_owned());
    }
    docker(&["pull", "--quiet", image]).await?;
    Ok(docker(&["image", "inspect", "--format", "{{.Id}}", image]).await?.trim().to_owned())
}
