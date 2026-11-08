//! The official BLAKE3 test vectors (`keyed_hash` and `derive_key`), first 32 output bytes, for a subset of lengths.
//
// Source: https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json. The input of length `n` is
// the bytes `i % 251` for `i in 0..n`.
#![allow(missing_docs)]

pub(crate) const KEY: &str = "whats the Elvish word for friend";
pub(crate) const CONTEXT: &str = "BLAKE3 2019-12-27 16:29:52 test vectors context";

/// `(input_len, keyed_hash, derive_key)`, each the first 32 bytes in hex.
pub(crate) const CASES: &[(usize, &str, &str)] = &[
    (
        0,
        "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26",
        "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d",
    ),
    (
        1,
        "6d7878dfff2f485635d39013278ae14f1454b8c0a3a2d34bc1ab38228a80c95b",
        "b3e2e340a117a499c6cf2398a19ee0d29cca2bb7404c73063382693bf66cb06c",
    ),
    (
        63,
        "bb1eb5d4afa793c1ebdd9fb08def6c36d10096986ae0cfe148cd101170ce37ae",
        "b6451e30b953c206e34644c6803724e9d2725e0893039cfc49584f991f451af3",
    ),
    (
        64,
        "ba8ced36f327700d213f120b1a207a3b8c04330528586f414d09f2f7d9ccb7e6",
        "a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e",
    ),
    (
        65,
        "c0a4edefa2d2accb9277c371ac12fcdbb52988a86edc54f0716e1591b4326e72",
        "51fd05c3c1cfbc8ed67d139ad76f5cf8236cd2acd26627a30c104dfd9d3ff8a8",
    ),
    (
        1023,
        "c951ecdf03288d0fcc96ee3413563d8a6d3589547f2c2fb36d9786470f1b9d6e",
        "74a16c1c3d44368a86e1ca6df64be6a2f64cce8f09220787450722d85725dea5",
    ),
    (
        1024,
        "75c46f6f3d9eb4f55ecaaee480db732e6c2105546f1e675003687c31719c7ba4",
        "7356cd7720d5b66b6d0697eb3177d9f8d73a4a5c5e968896eb6a689684302706",
    ),
    (
        1025,
        "357dc55de0c7e382c900fd6e320acc04146be01db6a8ce7210b7189bd664ea69",
        "effaa245f065fbf82ac186839a249707c3bddf6d3fdda22d1b95a3c970379bcb",
    ),
    (
        2049,
        "9f29700902f7c86e514ddc4df1e3049f258b2472b6dd5267f61bf13983b78dd5",
        "2ea477c5515cc3dd606512ee72bb3e0e758cfae7232826f35fb98ca1bcbdf273",
    ),
    (
        8192,
        "dc9637c8845a770b4cbf76b8daec0eebf7dc2eac11498517f08d44c8fc00d58a",
        "ad01d7ae4ad059b0d33baa3c01319dcf8088094d0359e5fd45d6aeaa8b2d0c3d",
    ),
    (
        31744,
        "efa53b389ab67c593dba624d898d0f7353ab99e4ac9d42302ee64cbf9939a419",
        "39772aef80e0ebe60596361e45b061e8f417429d529171b6764468c22928e28e",
    ),
];
