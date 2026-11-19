//! The hidden adversary of every run (`add_adversary`): replay and bit flips on victims' access links, garbage
//! floods, spoofed-source amplification probes against the public servers, a long-term key compromise and, for S12,
//! eclipse bursts at one victim.
//!
//! Invariant: the adversary draws from its own generator seeded `seed * 7919 + 17`, so adding it never moves a draw
//! of the world generator, and its action list is sorted by `(time, name, node)` like the reference's tuple sort.

use super::WorldError;
use super::build::{choice, sample};
use super::model::{AdvKind, Adversary, World};
use crate::reference::PyRandom;

/// The adversary's intensity.
#[derive(Clone, Debug, PartialEq)]
pub struct AdversaryCfg {
    /// Share of the nodes that are victims of replay and modification.
    pub victim_share: f64,
    /// Replay probability per inbound datagram at a victim.
    pub replay: f64,
    /// Modification probability per inbound datagram at a victim.
    pub modify: f64,
    /// Garbage floods.
    pub floods: u32,
    /// Amplification probes.
    pub amp_probes: u32,
    /// A long-term key leaks (forward secrecy check).
    pub compromise: bool,
    /// Eclipse bursts at one victim (S12).
    pub eclipse: u32,
}

/// The adversary of scenario `id`: the common one, raised for S12.
pub fn adversary_for(id: &str) -> AdversaryCfg {
    if id == "S12" {
        AdversaryCfg {
            victim_share: 0.3,
            replay: 0.03,
            modify: 0.01,
            floods: 12,
            amp_probes: 8,
            compromise: true,
            eclipse: 3,
        }
    } else {
        AdversaryCfg {
            victim_share: 0.15,
            replay: 0.01,
            modify: 0.005,
            floods: 4,
            amp_probes: 3,
            compromise: true,
            eclipse: 0,
        }
    }
}

/// Adds the adversary to a generated world.
///
/// # Errors
/// [`WorldError::Empty`] when the world has no node to attack or no cloud to probe.
pub fn add_adversary(world: &mut World, cfg: &AdversaryCfg, seed: u64) -> Result<(), WorldError> {
    let mut rng = PyRandom::from_seed(u128::from(seed) * 7919 + 17);
    let n = world.nodes.len();
    let cands: Vec<usize> = (0..n).filter(|i| !world.denied.contains(i)).collect();
    let k = ((cfg.victim_share * n as f64) as usize).max(1);
    let mut victims = sample(&mut rng, &cands, k.min(cands.len()), "adversary victims")?;
    victims.sort_unstable();
    world.adversary = Some(Adversary {
        victims: victims.clone(),
        replay: cfg.replay,
        modify: cfg.modify,
    });
    let dur = world.duration_ns;
    let at =
        |rng: &mut PyRandom, lo: f64, hi: f64| rng.randrange((lo * dur as f64) as i64, (hi * dur as f64) as i64) as u64;
    let mut env = Vec::new();
    for _ in 0..cfg.floods {
        let t = at(&mut rng, 0.1, 0.7);
        env.push((t, AdvKind::Garbage, choice(&mut rng, &victims, "adversary victims")?));
    }
    for _ in 0..cfg.amp_probes {
        let t = at(&mut rng, 0.3, 0.7);
        env.push((t, AdvKind::Amplify, choice(&mut rng, &world.clouds, "clouds")?));
    }
    env.sort_unstable();
    world.adversary_env = env;
    if cfg.compromise {
        let pool: Vec<usize> = cands.iter().copied().filter(|i| !world.clouds.contains(i)).collect();
        let pool = if pool.is_empty() { cands } else { pool };
        let target = choice(&mut rng, &pool, "compromise candidates")?;
        world.compromise = vec![((0.6 * dur as f64) as u64, target)];
        if let Some(fixed) = world.compromise_node {
            world.compromise = vec![fixed];
        }
    }
    if cfg.eclipse > 0 {
        let v = world
            .eclipse_victim
            .or_else(|| victims.first().copied())
            .ok_or(WorldError::Empty("adversary victims"))?;
        for _ in 0..cfg.eclipse {
            let t = at(&mut rng, 0.2, 0.6);
            world.adversary_env.push((t, AdvKind::Eclipse, v));
        }
        world.adversary_env.sort_unstable();
    }
    Ok(())
}
