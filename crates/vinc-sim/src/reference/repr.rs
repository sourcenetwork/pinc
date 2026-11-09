//! Python's `repr` for the value types the reference harness hashes: ints, floats, strings, bytes, booleans, `None`
//! and tuples. The seed derivation hashes the text of `repr(tuple)`, so the text must match CPython character for
//! character.
//!
//! Invariant: `Py::repr` equals CPython's `repr` of the same value. One approximation: a non-ASCII character is
//! escaped when it is a control, separator or format character in the common ranges listed in `printable`;
//! unassigned code points are not detected and stay as they are.

use std::fmt::Write;

/// A Python value that can be hashed through its `repr`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Py<'a> {
    /// `None`.
    None,
    /// `True` or `False`.
    Bool(bool),
    /// An integer.
    Int(i128),
    /// A float.
    Float(f64),
    /// A string.
    Str(&'a str),
    /// A bytes object.
    Bytes(&'a [u8]),
    /// A tuple.
    Tuple(&'a [Py<'a>]),
}

impl Py<'_> {
    /// The text `repr(value)` gives.
    pub fn repr(&self) -> String {
        let mut s = String::new();
        self.write(&mut s);
        s
    }

    fn write(&self, out: &mut String) {
        match self {
            Py::None => out.push_str("None"),
            Py::Bool(b) => out.push_str(if *b { "True" } else { "False" }),
            Py::Int(i) => {
                let _ = write!(out, "{i}");
            }
            Py::Float(f) => float_repr(*f, out),
            Py::Str(s) => str_repr(s, out),
            Py::Bytes(b) => bytes_repr(b, out),
            Py::Tuple(items) => {
                out.push('(');
                for (i, p) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    p.write(out);
                }
                if items.len() == 1 {
                    out.push(',');
                }
                out.push(')');
            }
        }
    }
}

/// The shortest round-trip digits and the exponent, laid out as CPython's `repr(float)` does: scientific notation
/// when the decimal point position is at most -4 or above 16.
fn float_repr(f: f64, out: &mut String) {
    if f.is_nan() {
        out.push_str("nan");
        return;
    }
    if f.is_sign_negative() {
        out.push('-');
    }
    if f.is_infinite() {
        out.push_str("inf");
        return;
    }
    let sci = format!("{:e}", f.abs());
    let (mant, exp) = sci.split_once('e').unwrap_or((&sci, "0"));
    let digits: String = mant.chars().filter(char::is_ascii_digit).collect();
    let decpt = exp.parse::<i32>().unwrap_or(0) + 1;
    let n = digits.len() as i32;
    if decpt <= -4 || decpt > 16 {
        out.push_str(&digits[..1]);
        if n > 1 {
            out.push('.');
            out.push_str(&digits[1..]);
        }
        let e = decpt - 1;
        let _ = write!(out, "e{}{:02}", if e < 0 { '-' } else { '+' }, e.abs());
    } else if decpt <= 0 {
        out.push_str("0.");
        out.extend(std::iter::repeat_n('0', (-decpt) as usize));
        out.push_str(&digits);
    } else if decpt >= n {
        out.push_str(&digits);
        out.extend(std::iter::repeat_n('0', (decpt - n) as usize));
        out.push_str(".0");
    } else {
        out.push_str(&digits[..decpt as usize]);
        out.push('.');
        out.push_str(&digits[decpt as usize..]);
    }
}

/// Whether Python's `str.isprintable` is true for a non-ASCII character, in the common ranges.
fn printable(c: char) -> bool {
    !matches!(c as u32,
        0x80..=0xa0 | 0xad | 0x1680 | 0x2000..=0x200f | 0x2028..=0x202f | 0x205f..=0x206f | 0x3000
        | 0xd800..=0xf8ff | 0xfeff | 0xfff9..=0xfffb | 0xe0000..=0xe0fff | 0xf0000..=0x10ffff)
}

fn quote_for(has_single: bool, has_double: bool) -> char {
    if has_single && !has_double { '"' } else { '\'' }
}

fn str_repr(s: &str, out: &mut String) {
    let q = quote_for(s.contains('\''), s.contains('"'));
    out.push(q);
    for c in s.chars() {
        match c {
            c if c == q || c == '\\' => {
                out.push('\\');
                out.push(c);
            }
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            c if c.is_ascii() || printable(c) => out.push(c),
            c if (c as u32) < 0x100 => {
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            c if (c as u32) < 0x10000 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => {
                let _ = write!(out, "\\U{:08x}", c as u32);
            }
        }
    }
    out.push(q);
}

fn bytes_repr(b: &[u8], out: &mut String) {
    let q = quote_for(b.contains(&b'\''), b.contains(&b'"'));
    out.push('b');
    out.push(q);
    for &c in b {
        match c {
            c if c as char == q || c == b'\\' => {
                out.push('\\');
                out.push(c as char);
            }
            b'\t' => out.push_str("\\t"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            0x20..=0x7e => out.push(c as char),
            c => {
                let _ = write!(out, "\\x{c:02x}");
            }
        }
    }
    out.push(q);
}
