//! The nodes' base image: with no `--image` it is the build host's own distribution, so the C library the bound
//! binary links is in it, and an image with an older glibc than the host's is recognised.
#![allow(missing_docs, clippy::unwrap_used)]

use vinc_distributed::backend::containers::{FALLBACK_IMAGE, glibc, image_for};

const UBUNTU_2404: &str = r#"PRETTY_NAME="Ubuntu 24.04.3 LTS"
NAME="Ubuntu"
VERSION_ID="24.04"
VERSION="24.04.3 LTS (Noble Numbat)"
VERSION_CODENAME=noble
ID=ubuntu
ID_LIKE=debian
"#;

const DEBIAN_12: &str =
    "PRETTY_NAME=\"Debian GNU/Linux 12 (bookworm)\"\nNAME=\"Debian GNU/Linux\"\nVERSION_ID=\"12\"\nID=debian\n";

const ARCH: &str = "NAME=\"Arch Linux\"\nID=arch\nBUILD_ID=rolling\n";

#[test]
fn the_default_image_is_the_build_hosts_distribution() {
    // The image the agents kept retagging by hand: an Ubuntu 24.04 host (glibc 2.39) needs ubuntu:24.04, not the
    // glibc 2.36 debian:bookworm-slim the default used to be.
    assert_eq!(image_for(UBUNTU_2404).as_deref(), Some("ubuntu:24.04"));
    assert_ne!(image_for(UBUNTU_2404).as_deref(), Some(FALLBACK_IMAGE));
    assert_eq!(image_for(DEBIAN_12).as_deref(), Some("debian:12"));
    assert_eq!(image_for(ARCH).as_deref(), Some("archlinux:latest"));
    // ID_LIKE is not ID, and a release is needed where the distribution has one.
    assert_eq!(image_for("ID_LIKE=debian\nVERSION_ID=\"1\"\n"), None);
    assert_eq!(image_for("ID=fedora\n"), None);
}

#[test]
fn glibc_versions_order_by_major_then_minor() {
    assert_eq!(glibc("glibc 2.39\n"), Some((2, 39)));
    assert_eq!(glibc("glibc 2.36"), Some((2, 36)));
    assert_eq!(glibc("glibc 2.41.9000"), Some((2, 41)));
    assert_eq!(glibc("musl"), None);
    assert_eq!(glibc(""), None);
    assert!(glibc("glibc 2.36").unwrap() < glibc("glibc 2.39").unwrap());
    assert!(glibc("glibc 2.9").unwrap() < glibc("glibc 2.10").unwrap());
}
