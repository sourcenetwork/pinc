//! S2, S3, S5 and S11: the scenarios built directly on the shared builder (`scenarios.generate`).

use super::WorldError;
use super::build::{Builder, below, blank_world, finish, sort_world};
use super::large::large_values;
use super::mixed::mixed;
use super::model::{Params, World};
use super::params::ParamsExt;

/// Generates S2, S3, S5 or S11 from the merged parameters.
pub(super) fn generate(id: &str, p: Params, seed: u64) -> Result<World, WorldError> {
    let mut w = blank_world(id, &p, seed)?;
    let mut b = Builder::new(p, seed);
    let mut clouds = Vec::new();
    for r in 0..b.p.count("n_cloud")? {
        clouds.push(b.add_cloud(&mut w, r % 3)?);
    }
    let down =
        b.p.contains_key("home_down_bps")
            .then(|| b.p.int("home_down_bps"))
            .transpose()?;
    let up =
        b.p.contains_key("home_up_bps")
            .then(|| b.p.int("home_up_bps"))
            .transpose()?;
    let mut homes = Vec::new();
    for _ in 0..b.p.count("n_home")? {
        let region = below(&mut b.rng, 3, "regions")?;
        homes.push(b.add_home(&mut w, region, down.map(|x| x as u64), up.map(|x| x as u64))?);
    }
    let mut mobiles = Vec::new();
    for _ in 0..b.p.count("n_mobile")? {
        let region = below(&mut b.rng, 3, "regions")?;
        mobiles.push(b.add_mobile(&mut w, region)?);
    }
    finish(&mut w, clouds, homes, mobiles);
    if id == "S11" {
        large_values(&mut w, &mut b)?;
    } else {
        mixed(&mut w, &mut b)?;
    }
    sort_world(&mut w);
    Ok(w)
}
