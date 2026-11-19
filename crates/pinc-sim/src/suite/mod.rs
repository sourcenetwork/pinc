//! The scenario suite: the reference harness's twelve scenarios, its gates and its metrics, run against the real
//! `pinc-core` endpoint with real cryptography.
//!
//! Modules: [`world`] generates a scenario's world bit-exactly from a seed; [`crypto`] is the instrumented crypto
//! provider that decides the security gates on the real keys; [`proto`] holds the application and the harness
//! protocols; [`node`] adapts an endpoint to the simulator's node contract; [`rec`] is the recorder every node
//! reports to; [`grade`] decides the gates, computes the terms and scores them; [`run`] builds the network, runs a world and
//! reports it.
pub mod crypto;
pub mod grade;
pub mod node;
pub mod proto;
pub mod rec;
pub mod run;
pub mod world;
