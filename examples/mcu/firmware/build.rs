//! Puts `memory.x` where the linker finds it and asks for the Cortex-M runtime's link script.
use std::{env, fs, path::PathBuf};

fn main() {
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("cargo sets OUT_DIR"));
    fs::copy("memory.x", out.join("memory.x")).expect("memory.x is copied");
    println!("cargo:rustc-link-search={}", out.display());
    println!("cargo:rustc-link-arg-bins=-Tlink.x");
    println!("cargo:rustc-link-arg-bins=--nmagic");
    println!("cargo:rerun-if-changed=memory.x");
}
