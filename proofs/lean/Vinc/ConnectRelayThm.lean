import Vinc.ConnectRelay

/-!
# Theorems of the relay

Properties of the relay of `ConnectRelay.lean`, each stated on the functions of the model (the code's step functions),
for every state and every call.

* Authenticated peers only: `peer_unauth` (a frame from a node that is no peer is refused and changes nothing),
  `forward_peer` (a packet is forwarded only to a peer relay, never to this relay).
* No loop: `no_reforward` (a packet that came from a peer relay produces no frame for any relay).
* The reply route: `back_window` (it is used only within 30 s of its learning, never when it names this relay) and
  `back_expired` (after 30 s it is not), `fwdback_local` (a node that holds a carrier here is never learnt as forwarded).
* The byte quota: `charge_ok` (an accepted frame leaves the window total at most the quota), `charge_reset` (the window
  restarts only after the configured length), `charge_drop` (a frame over the quota is not counted).
* The release of held messages: `heard_idle` (a heard packet from a member that holds nothing emits nothing),
  `heard_unready_quiet` (from a member the host reports not ready it emits nothing and keeps the mailbox); routing
  starts no release, so `forwarded` (a packet from a carrier or a UDP session for a member that is not asleep, has no
  carrier and no ready route here and is homed at a peer relay is forwarded there, whatever its mailbox holds).
* The hub tunnel: `tunnel_spec` (a datagram goes down a UDP session only if it was heard less than 20 s ago and
  `35 + len <= 1452 - 28`), `tunnel_ready_spec` (and only if the host reports a validated direct route for the member),
  `spu_member` (an uploaded packet is accepted only from a validated member),
  `stale_copy` (the second copy goes out only if the carrier is silent for more than 15 s).
* The sleep notice: `sleep_spec` (accepted only within 10 s of the relay's clock, for a node it knows, from its own
  carrier), `close_asleep` (a close within 10 s after an accepted notice is a suspension).
-/

namespace Vinc.ConnectRelay

theorem peer_unauth (cf : CF) (r : RS) (now from_ : Nat) (f : List V) (h : isPeer r from_ = false) :
    peerFrame cf r now from_ f = fail r "unauth" from_ := by
  simp [peerFrame, h]

theorem forward_peer (cf : CF) (r : RS) (now src dst flag len : Nat) (h : (forward cf r now src dst flag len).res = "ok") :
    ∃ home, home ≠ cf.me ∧ isPeer r home = true ∧
      (forward cf r now src dst flag len).ef = [[.s "peer", .n home, .s "fwd", .n src, .n dst, .n flag, .n len],
        routedE src dst "peer" len] := by
  unfold forward at *
  generalize homeOf cf r now dst = home at *
  by_cases h1 : (home == 0 || home == cf.me) = true
  · simp [h1, fail] at h
  · by_cases h2 : (!isPeer r home) = true
    · simp [h1, h2, fail] at h
    · refine ⟨home, ?_, ?_, ?_⟩
      · simp at h1; exact h1.2
      · simpa using h2
      · simp [h1, h2, okOut]

private theorem noPeer_fail (r : RS) (w : String) (n : Nat) : ∀ e ∈ (fail r w n).ef, e.head? ≠ some (V.s "peer") := by
  intro e he; simp [fail, rejE] at he; subst he; simp

private theorem noPeer_local (a b c : Nat) : ∀ e ∈ localEf a b c, e.head? ≠ some (V.s "peer") := by
  intro e he; simp [localEf, routedE] at he; rcases he with rfl | rfl <;> simp

private theorem noPeer_tunnel (r : RS) (a b c d f : Nat) : ∀ e ∈ (tunnelDown r a b c d f).2, e.head? ≠ some (V.s "peer") := by
  intro e he; unfold tunnelDown at he
  by_cases hc : (!tunnelFresh r a b || !tunnelReady r b || f == 0 || decide (35 + f > maxTun)) = true
  · simp [hc] at he
  · simp [hc, routedE] at he; rcases he with rfl | rfl <;> simp

private theorem noPeer_deliver (cf : CF) (r : RS) (a b c d f : Nat) (sc : Bool) :
    ∀ e ∈ (deliverClient cf r a b c d f sc).2.2, e.head? ≠ some (V.s "peer") := by
  intro e he; unfold deliverClient at he
  by_cases hc : (!hasC cf r c) = true
  · simp [hc] at he
  · simp only [hc, Bool.false_eq_true, ite_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (rfl | rfl) | he
    · split <;> simp
    · simp [routedE]
    · by_cases hs : (sc && decide (a - (cget r c).lastRx > stale)) = true
      · simp only [hs, ite_true] at he; exact noPeer_tunnel _ _ _ _ _ _ e he
      · simp [hs] at he

private theorem noPeer_hold (cf : CF) (r : RS) (a b c d f : Nat) : ∀ e ∈ (hold cf r a b c d f).ef, e.head? ≠ some (V.s "peer") := by
  intro e he; unfold hold at he
  split at he <;> grind [okOut, routedE, rejE]

/-- A packet that arrived from a peer relay is never sent to a relay again: its routing produces no relay frame. -/
theorem no_reforward (cf : CF) (r : RS) (now src dst flag len : Nat) :
    ∀ e ∈ (route cf r now src dst flag len .peer).ef, e.head? ≠ some (V.s "peer") := by
  intro e he
  unfold route at he
  split at he
  · exact noPeer_local _ _ _ e he
  · split at he
    · exact noPeer_deliver cf r _ _ _ _ _ _ e (by simpa [okOut] using he)
    · split at he
      · exact noPeer_tunnel _ _ _ _ _ _ e (by simpa [okOut] using he)
      · split at he
        · exact noPeer_hold cf r _ _ _ _ _ e he
        · split at he
          · exact noPeer_fail r _ _ e he
          · simp at *

/-- The reply route is used within 30 s only, and never to this relay. -/
theorem back_window (cf : CF) (r : RS) (now dst : Nat) (h : backOf cf r now dst ≠ 0) :
    ∃ s : FB, r.fb.getD (r.bkf dst) ⟨0, 0, 0⟩ = s ∧ s.n = dst ∧ now - s.at_ < fwdBack ∧ s.rel ≠ cf.me ∧
      backOf cf r now dst = s.rel := by
  unfold backOf at *
  generalize r.fb.getD (r.bkf dst) ⟨0, 0, 0⟩ = s at *
  by_cases hc : (s.n == dst && decide (now - s.at_ < fwdBack) && s.rel != cf.me) = true
  · simp at hc
    exact ⟨s, rfl, hc.1.1, hc.1.2, hc.2, by simp [hc]⟩
  · simp [hc] at h

theorem back_expired (cf : CF) (r : RS) (now dst : Nat) (s : FB) (hs : r.fb.getD (r.bkf dst) ⟨0, 0, 0⟩ = s)
    (h : fwdBack ≤ now - s.at_) : backOf cf r now dst = 0 := by
  unfold backOf; rw [hs]
  have : ¬ now - s.at_ < fwdBack := by omega
  simp [this]

/-- A node that holds a carrier here is not learnt as forwarded: the frames are those of the routing alone, and the
reply routes are unchanged. -/
theorem fwdback_local (cf : CF) (r : RS) (now : Nat) (src dst flag len from_ : Nat) (hp : isPeer r from_ = true)
    (h : hasC cf r src = true) :
    (peerFrame cf r now from_ [.s "fwd", .n src, .n dst, .n flag, .n len]).ef = (route cf r now src dst flag len .peer).ef := by
  simp [peerFrame, hp, h]

/-- Any other source is learnt, and the learning is reported. -/
theorem fwdback_learnt (cf : CF) (r : RS) (now : Nat) (src dst flag len from_ : Nat) (hp : isPeer r from_ = true)
    (h : hasC cf r src = false) :
    (peerFrame cf r now from_ [.s "fwd", .n src, .n dst, .n flag, .n len]).ef.head? =
      some [.s "t", .s "fwdback", .n src, .n from_] := by
  simp [peerFrame, hp, h]

/-! ### The byte quota -/

theorem aget_aput_self {α : Type} (k : Nat) (v : α) : ∀ l : List (Nat × α), aget (aput l k v) k = some v := by
  intro l; induction l with
  | nil => simp [aput, aget]
  | cons p t ih =>
    obtain ⟨a, x⟩ := p
    by_cases h : (a == k) = true
    · simp [aput, aget, h]
    · simp [aput, aget, h] at *
      exact ih

theorem cget_setC (r : RS) (n : Nat) (c : Client) : cget (setC r n c) n = c := by
  simp [cget, setC, aget_aput_self]

/-- The window restarts only after its length has passed. -/
theorem charge_reset (cf : CF) (c : Client) (now : Nat) :
    (cf.window ≤ now - c.ws → (chargeC cf c now).wb = 0 ∧ (chargeC cf c now).ws = now) ∧
    (now - c.ws < cf.window → chargeC cf c now = c) := by
  unfold chargeC
  constructor
  · intro h; simp [h]
  · intro h; have : ¬ now - c.ws ≥ cf.window := by omega
    simp [this]

/-- A frame is accepted only if the window total stays within the quota, and the total is then the stored one. -/
theorem charge_ok (cf : CF) (r : RS) (now node bytes : Nat) (h : (charge cf r now node bytes).2.1 = true) :
    (chargeC cf (cget r node) now).wb + bytes ≤ cf.bytes ∧
    (cget (charge cf r now node bytes).1 node).wb = (chargeC cf (cget r node) now).wb + bytes := by
  unfold charge at *
  by_cases hc : (chargeC cf (cget r node) now).wb + bytes > cf.bytes
  · simp [hc] at h
  · simp only [hc, ite_false] at h ⊢
    exact ⟨by omega, by rw [cget_setC]⟩

/-- A frame over the quota is not counted: the stored total is the one before it (after a window restart, if due). -/
theorem charge_drop (cf : CF) (r : RS) (now node bytes : Nat) (h : (charge cf r now node bytes).2.1 = false) :
    cf.bytes < (chargeC cf (cget r node) now).wb + bytes ∧
    (cget (charge cf r now node bytes).1 node).wb = (chargeC cf (cget r node) now).wb := by
  unfold charge at *
  by_cases hc : (chargeC cf (cget r node) now).wb + bytes > cf.bytes
  · refine ⟨hc, ?_⟩
    simp only [hc, ite_true]
    rw [cget_setC]
  · simp [hc] at h

/-- The window total never exceeds the quota: if it was within the quota before a frame, it is after. -/
theorem charge_inv (cf : CF) (r : RS) (now node bytes : Nat) (h : (cget r node).wb ≤ cf.bytes) :
    (cget (charge cf r now node bytes).1 node).wb ≤ cf.bytes := by
  have hr : (chargeC cf (cget r node) now).wb ≤ cf.bytes := by
    unfold chargeC; by_cases hw : now - (cget r node).ws ≥ cf.window
    · simp [hw]
    · simp [hw]; exact h
  unfold charge
  by_cases hc : (chargeC cf (cget r node) now).wb + bytes > cf.bytes
  · simp only [hc, ite_true]; rw [cget_setC]; exact hr
  · simp only [hc, ite_false]; rw [cget_setC]; simp; omega

/-! ### The hub tunnel -/

/-- A datagram goes down a member's UDP session only if the session was heard less than 20 s ago and the packet fits
(`35 + len <= MTU - 28`). -/
theorem tunnel_spec (r : RS) (now dst src flag len : Nat) (h : (tunnelDown r now dst src flag len).1 = true) :
    (∃ heard, aget r.udp dst = some heard ∧ now - heard < fresh) ∧ 0 < len ∧ 35 + len ≤ 1452 - 28 := by
  unfold tunnelDown at h
  by_cases hc : (!tunnelFresh r now dst || !tunnelReady r dst || len == 0 || decide (35 + len > maxTun)) = true
  · simp [hc] at h
  · simp [Bool.or_eq_true] at hc
    obtain ⟨⟨⟨hf, _⟩, hl⟩, hm⟩ := hc
    refine ⟨?_, by omega, by simp [maxTun] at hm; omega⟩
    unfold tunnelFresh at hf
    cases hg : aget r.udp dst with
    | none => simp [hg] at hf
    | some t => simp [hg] at hf; exact ⟨t, rfl, hf⟩

/-- A datagram goes down a member's UDP session only if the host reports a validated direct route for it. -/
theorem tunnel_ready_spec (r : RS) (now dst src flag len : Nat) (h : (tunnelDown r now dst src flag len).1 = true) :
    tunnelReady r dst = true := by
  unfold tunnelDown at h
  by_cases hc : (!tunnelFresh r now dst || !tunnelReady r dst || len == 0 || decide (35 + len > maxTun)) = true
  · simp [hc] at h
  · simp [Bool.or_eq_true] at hc
    obtain ⟨⟨⟨_, hr⟩, _⟩, _⟩ := hc
    exact hr

/-- An uploaded packet (SPU) is accepted only from a validated member, and never for this relay. -/
theorem spu_member (cf : CF) (r : RS) (now m dst flag len : Nat) (h : (spu cf r now m dst flag len).res = "ok") :
    m ≠ 0 ∧ dst ≠ cf.me := by
  unfold spu at h
  by_cases h1 : (len == 0 || decide (35 + len > maxTun)) = true
  · simp [h1, fail] at h
  · by_cases h2 : m = 0
    · simp [h1, h2, fail] at h
    · by_cases h3 : dst = cf.me
      · simp [h1, h2, h3, fail, Out.after] at h
      · exact ⟨h2, h3⟩

/-! ### The release of held messages -/

/-- Hearing a member that holds nothing costs nothing: the time is stamped and no effect is emitted. -/
theorem heard_idle (cf : CF) (r : RS) (now node : Nat) (hn : cf.old = false) (hk : acan r.udp node cf.C = true)
    (h : pendingCount r.mb node = 0) :
    udpHeard cf r now node = okOut { r with udp := aput r.udp node now } [] := by
  simp [udpHeard, releaseHeld, hn, hk, h, okOut]

/-- Hearing a member the host reports not ready emits nothing and leaves the mailbox as it was: the messages are kept
for the next heard packet. -/
theorem heard_unready_quiet (cf : CF) (r : RS) (now node : Nat) (hn : cf.old = false) (hk : acan r.udp node cf.C = true)
    (h : tunnelReady r node = false) :
    (udpHeard cf r now node).ef = [] ∧ (udpHeard cf r now node).r.mb = r.mb := by
  have h' : r.nr.contains node = true := by simpa [tunnelReady] using h
  have h'' : node ∈ r.nr := by simpa using h'
  by_cases h0 : pendingCount r.mb node = 0
  · simp [udpHeard, releaseHeld, hn, hk, h0, okOut]
  · simp [udpHeard, releaseHeld, hn, hk, h0, tunnelReady, h', h'', okOut]

/-- Routing starts no release, so a packet for a member that is not asleep here, has no carrier and no ready route here
and is homed at a peer relay (and did not come from one) is forwarded to that relay, whatever its mailbox holds. -/
theorem forwarded (cf : CF) (r : RS) (now src dst flag len : Nat) (origin : Origin) (hd : dst ≠ cf.me)
    (hc : (deliverClient cf r now src dst flag len true).2.1 = false)
    (ht : (tunnelDown r now dst src flag len).1 = false) (hs : (aget r.sl dst).isSome = false) (ho : origin ≠ .peer)
    (h0 : homeOf cf r now dst ≠ 0) (hm : homeOf cf r now dst ≠ cf.me) (hp : isPeer r (homeOf cf r now dst) = true) :
    route cf r now src dst flag len origin =
      okOut r [[.s "peer", .n (homeOf cf r now dst), .s "fwd", .n src, .n dst, .n flag, .n len],
        routedE src dst "peer" len] := by
  unfold route
  simp [hd, hc, ht, hs, ho, forward, h0, hm, hp, okOut]

/-! ### The sleep notice -/

/-- A notice is accepted only if its clock is within 10 s of the relay's, the node is known (it holds a carrier or just
lost one), it arrived on its own carrier or over UDP, and it is validly signed for this relay. -/
theorem sleep_spec (cf : CF) (r : RS) (now k ts good sender : Nat) (h : (sleepNotice cf r now k ts good sender).res = "ok") :
    (sender = 0 ∨ sender = k) ∧ (now / 1000000).max ts - (now / 1000000).min ts < skewMs ∧
    (hasC cf r k = true ∨ (aget r.gone k).isSome = true) ∧ good ≠ 0 := by
  unfold sleepNotice at h
  by_cases h1 : (sender != 0 && sender != k) = true
  · simp [h1, fail] at h
  · by_cases h2 : skewed now ts = true
    · simp [h1, h2, fail] at h
    · by_cases h3 : (!(hasC cf r k || (aget r.gone k).isSome)) = true
      · simp [h1, h2, h3, fail] at h
      · by_cases h4 : (good == 0) = true
        · simp [h1, h2, h3, h4, fail] at h
        · refine ⟨?_, ?_, ?_, ?_⟩
          · simp at h1; omega
          · unfold skewed at h2; simpa using h2
          · cases hh : (hasC cf r k || (aget r.gone k).isSome) with
            | false => simp [hh] at h3
            | true => simpa [Bool.or_eq_true] using hh
          · simpa using h4

/-- A close is reported as a suspension only after an accepted notice at most 10 s before it ... -/
theorem close_asleep (cf : CF) (r : RS) (now node sid : Nat)
    (h : (carrierClosed cf r now node sid).ef = [[.s "t", .s "closed", .n node, .n 1]]) :
    ∃ s, aget r.sl node = some s ∧ now - sleepWin ≤ s.at_ := by
  unfold carrierClosed at h
  by_cases h0 : (!hasC cf r node || (cget r node).id != sid) = true
  · simp [h0, okOut] at h
  · simp only [h0, ite_false, okOut] at h
    cases hs : aget r.sl node with
    | none => simp [hs] at h
    | some s =>
      refine ⟨s, rfl, ?_⟩
      by_cases hw : s.at_ ≥ now - sleepWin
      · omega
      · simp [hs, hw] at h

/-- ... and a close within 10 s after a notice, of a node whose gone mark fits, is one. -/
theorem close_asleep_of (cf : CF) (r : RS) (now node sid : Nat) (s : Sl) (hc : hasC cf r node = true)
    (hid : (cget r node).id = sid) (hg : acan r.gone node cf.C = true) (hs : aget r.sl node = some s)
    (hw : now - sleepWin ≤ s.at_) :
    (carrierClosed cf r now node sid).ef = [[.s "t", .s "closed", .n node, .n 1]] := by
  unfold carrierClosed
  have h0 : ¬ ((!hasC cf r node || (cget r node).id != sid) = true) := by simp [hc, hid]
  simp only [h0, ite_false, okOut]
  have hput : (aget (aput r.gone node now) node).isSome = true := by rw [aget_aput_self]; rfl
  simp [hg, hs, hw, hput]

/-- The second copy of a packet goes down the UDP session only if the member's carrier was silent for more than 15 s. -/
theorem stale_copy (cf : CF) (r : RS) (now src dst flag len : Nat) (sc : Bool)
    (h : 2 < (deliverClient cf r now src dst flag len sc).2.2.length) :
    sc = true ∧ stale < now - (cget r dst).lastRx := by
  unfold deliverClient at h
  by_cases h0 : (!hasC cf r dst) = true
  · simp [h0] at h
  · simp only [h0, ite_false] at h
    by_cases hs : (sc && decide (now - (cget r dst).lastRx > stale)) = true
    · simp at hs; exact ⟨hs.1, hs.2⟩
    · simp [hs] at h

end Vinc.ConnectRelay
