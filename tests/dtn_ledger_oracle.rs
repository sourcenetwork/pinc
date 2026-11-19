//! A reference ledger for the delay-tolerant trace tests: the behaviour of `pinc_dtn::store::Ledger` written from its
//! documented rules, sharing no code with it. It is stated the way the proofs state it: after the expired items left,
//! an admission is accepted exactly when the custody items leave room for it in bytes (summed in 128 bits, so nothing
//! saturates) and in slots; it then evicts transit items, oldest admission first, only as many as needed. The order of
//! the checks is the documented one: the expired items leave first, then a key still kept is a duplicate, then an item
//! that is itself expired (`exp <= now`) is refused, then the room test. Every refusal reports the expired items.
#![allow(dead_code, missing_docs, unreachable_pub)]

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ent {
    pub space: u8,
    pub id: u8,
    pub bytes: u64,
    pub custody: bool,
    pub exp: u64,
    pub seq: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    Dup,
    Expired,
    Custody,
    Full,
}

#[derive(Clone, Debug)]
pub struct Oracle {
    pub n: usize,
    pub budget: u64,
    pub next: u64,
    pub slots: Vec<Option<Ent>>,
}

impl Oracle {
    pub fn new(n: usize, budget: u64) -> Self {
        Self {
            n,
            budget,
            next: 0,
            slots: vec![None; n],
        }
    }

    pub fn ents(&self) -> Vec<Ent> {
        self.slots.iter().flatten().copied().collect()
    }

    pub fn used(&self) -> u128 {
        self.ents().iter().map(|e| u128::from(e.bytes)).sum()
    }

    pub fn contains(&self, space: u8, id: u8) -> bool {
        self.ents().iter().any(|e| e.space == space && e.id == id)
    }

    pub fn expire(&mut self, now: u64) -> Vec<Ent> {
        let mut out = vec![];
        for s in &mut self.slots {
            if s.is_some_and(|e| e.exp <= now) {
                out.extend(s.take());
            }
        }
        out
    }

    pub fn admit(
        &mut self,
        space: u8,
        id: u8,
        bytes: u64,
        custody: bool,
        exp: u64,
        now: u64,
    ) -> (Result<(), Refusal>, Vec<Ent>) {
        let mut ev = self.expire(now);
        if self.contains(space, id) {
            return (Err(Refusal::Dup), ev);
        }
        if exp <= now {
            return (Err(Refusal::Expired), ev);
        }
        let hard: Vec<Ent> = self.ents().into_iter().filter(|e| e.custody).collect();
        let hard_bytes: u128 = hard.iter().map(|e| u128::from(e.bytes)).sum();
        if hard_bytes + u128::from(bytes) > u128::from(self.budget) || hard.len() >= self.n {
            return (Err(if custody { Refusal::Custody } else { Refusal::Full }), ev);
        }
        while u128::from(self.budget) - self.used() < u128::from(bytes) || self.ents().len() == self.n {
            let at = (0..self.n)
                .filter(|&i| self.slots[i].is_some_and(|e| !e.custody))
                .min_by_key(|&i| self.slots[i].map(|e| e.seq))
                .expect("a transit item exists when the custody items leave room");
            ev.extend(self.slots[at].take());
        }
        let at = self.slots.iter().position(Option::is_none).unwrap();
        self.slots[at] = Some(Ent {
            space,
            id,
            bytes,
            custody,
            exp,
            seq: self.next,
        });
        self.next += 1;
        (Ok(()), ev)
    }

    pub fn release(&mut self, space: u8, id: u8) -> Option<Ent> {
        let at = self
            .slots
            .iter()
            .position(|s| s.is_some_and(|e| e.space == space && e.id == id))?;
        self.slots[at].take()
    }

    pub fn reclass(&mut self, space: u8, id: u8, custody: bool) -> bool {
        match self.slots.iter_mut().flatten().find(|e| e.space == space && e.id == id) {
            Some(e) => {
                e.custody = custody;
                true
            }
            None => false,
        }
    }
}

/// The JSON object of an entry, without the admission number (it is not observable).
pub fn ent_json(e: &Ent) -> String {
    format!(
        r#"{{"s":{},"i":{},"b":{},"c":{},"x":{}}}"#,
        e.space,
        e.id,
        e.bytes,
        u8::from(!e.custody),
        e.exp
    )
}

pub fn ents_json(es: &[Ent]) -> String {
    format!("[{}]", es.iter().map(ent_json).collect::<Vec<_>>().join(","))
}
