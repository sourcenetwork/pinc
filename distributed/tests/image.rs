//! The nodes' base image: with no `--image` it is the build host's own distribution, so the C library the bound
//! binary links is in it, and an image with an older glibc than the host's is recognised.
#![allow(missing_docs, clippy::unwrap_used)]

use vinc_distributed::backend::containers::{FALLBACK_IMAGE, glibc, image_for, refusal};

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

const ARCH_LIKE: &str = "NAME=\"CachyOS Linux\"\nID=cachyos\nID_LIKE=arch\nBUILD_ID=rolling\n";

const UBUNTU_LIKE: &str =
    "NAME=\"Linux Mint\"\nVERSION_ID=\"21.3\"\nID=linuxmint\nID_LIKE=\"ubuntu debian\"\nUBUNTU_CODENAME=jammy\n";

#[test]
fn the_default_image_is_the_build_hosts_distribution() {
    // The image the agents kept retagging by hand: an Ubuntu 24.04 host (glibc 2.39) needs ubuntu:24.04, not the
    // glibc 2.36 debian:bookworm-slim the default used to be.
    assert_eq!(image_for(UBUNTU_2404).as_deref(), Some("ubuntu:24.04"));
    assert_ne!(image_for(UBUNTU_2404).as_deref(), Some(FALLBACK_IMAGE));
    assert_eq!(image_for(DEBIAN_12).as_deref(), Some("debian:12-slim"));
    assert_eq!(image_for(ARCH).as_deref(), Some("archlinux:latest"));
    // ID_LIKE is not ID, and a release is needed where the distribution has one.
    assert_eq!(image_for("ID_LIKE=debian\nVERSION_ID=\"1\"\n"), None);
    assert_eq!(image_for("ID=fedora\n"), None);
}

#[test]
fn a_derivative_gets_the_image_of_what_it_is_built_on_and_an_unknown_distribution_none() {
    // A derivative's own name and release are not an image: its base's image has its C library.
    assert_eq!(image_for(ARCH_LIKE).as_deref(), Some("archlinux:latest"));
    assert_eq!(image_for(UBUNTU_LIKE).as_deref(), Some("ubuntu:jammy"));
    // A derivative of Ubuntu that does not name the codename, and a distribution with no image here, get the fallback.
    assert_eq!(
        image_for("ID=pop\nID_LIKE=\"ubuntu debian\"\nVERSION_ID=\"22.04\"\n"),
        None
    );
    assert_eq!(image_for("ID=opensuse-leap\nVERSION_ID=\"15.6\"\n"), None);
    assert_eq!(image_for("ID=rhel\nVERSION_ID=\"9.4\"\n"), None);
}

#[test]
fn a_refused_image_is_told_both_versions_and_never_to_pass_itself() {
    let told = refusal("debian:bookworm-slim", (2, 36), (2, 39), Some("ubuntu:24.04"));
    assert!(
        told.contains("glibc 2.36") && told.contains("this host's 2.39"),
        "{told}"
    );
    assert!(
        told.contains("--image ubuntu:24.04 (this host's distribution)"),
        "{told}"
    );
    // The host's own image was the one refused, or the host names no distribution with an image: only the version.
    for own in [Some("debian:bookworm-slim"), None] {
        let told = refusal("debian:bookworm-slim", (2, 36), (2, 42), own);
        assert!(!told.contains("this host's distribution"), "{told}");
        assert!(
            told.ends_with("pass --image an image with glibc 2.42 or newer"),
            "{told}"
        );
    }
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
