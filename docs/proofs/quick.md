# Proofs: the quick profile

`just proofs` (the default, `scripts/proofs.sh`) checks a model that has a file under `proofs/tla/quick/` over the
smaller bounds of that file: the same specification and the same properties, only the bounds shrink. `just
proofs-deep` (`scripts/proofs.sh deep`) checks every model over the bounds [Properties](properties.md) states. A model
with no quick file runs its own config in both profiles. The table lists every quick file, from its first comment:
the bounds it changes and what the smaller bounds no longer reach.

| Config | Quick bounds and what they weaken |
|---|---|
| `Amp` | U 100 -> 25 (the least U at which a send allowed before validation still saturates tx) |
| `BroadcastAuth` | MaxPub 2 -> 1 |
| `BroadcastAuth_nobody` | MaxPub 2 -> 1 |
| `BroadcastAuth_noisb` | MaxPub 2 -> 1 |
| `BroadcastAuth_nomid` | MaxPub 2 -> 1 |
| `BroadcastAuth_notopic` | MaxPub 2 -> 1 |
| `BroadcastAuth_nots` | MaxPub 2 -> 1 |
| `BroadcastFloors` | Members {5, 6} -> {5} |
| `BroadcastFloors_cap1` | Hubs {1, 2} -> {1} |
| `BroadcastFloors_future` | Members {5, 6} -> {5} |
| `BroadcastFloors_top` | Origins {7, 8} -> {7} |
| `BroadcastLog` | Ring 6 -> 4, Cap 3 -> 2, MaxN 4 -> 2, Mids {1, 2, 3} -> {1, 2} (as many ids as the cap, as in the deep config; BroadcastLog_cap keeps one id more) |
| `BroadcastLog_big` | Ring 6 -> 4, Cap 3 -> 2, MaxN 7 -> 5 (still one more than the ring), Mids {1, 2, 3} -> {1, 2} (as many ids as the cap, as before) |
| `BroadcastLog_cap` | Ring 6 -> 4, Cap 3 -> 2, MaxN 4 -> 2, Mids {1, 2, 3, 4} -> {1, 2, 3} (still one id more than the cap) |
| `BroadcastMidMap` | Slots 8 -> 4, Cap 4 -> 2, Keys {0, 8, 16, 1, 9, 2, 7} -> {0, 4, 1, 3, 7} |
| `BroadcastMidMap_anyHash` | Vals {0, 1} -> {0} |
| `BroadcastMidMap_refuse` | Vals {0, 1} -> {0} |
| `BroadcastNode` | MaxNow 5 -> 3, Mids {1, 2} -> {1} |
| `BroadcastNode_ackById` | MaxNow 5 -> 4 |
| `BroadcastNode_ackEarly` | MaxNow 5 -> 4 |
| `BroadcastNode_compareAll` | MaxNow 4 -> 3 |
| `BroadcastNode_evict` | MaxNow 6 -> 5 |
| `BroadcastNode_evictCap` | Mids {1, 2, 3, 4} -> {1, 2, 3}, SeenCap 3 -> 2 (still one id more than the dedupe set holds) |
| `BroadcastNode_evictCap2x` | SeenCap 4 -> 2 and Mids {1, 2, 3, 4} -> {1, 2} (still one seen slot per mid, so the seen table never overflows, as in the deep run), Origins {1, 2} -> {2} (every message is asked for, so the answer is taken; the node's own messages are left out) |
| `BroadcastNode_floors` | Stamps {1, 2} -> {1}, MaxNow 5 -> 4; bounded by constraint: behaviours of at most 6 levels (BroadcastNode_floorsQuickBound) |
| `BroadcastNode_graft` | MaxNow 4 -> 1, Mids {1, 2} -> {1} A hub that also publishes its own messages: the id is recorded, and a message over the ring (size 5, ring 4) is refused by the log, which leaves the id known with no print held. A graft due an acknowledgement under such an id is answered IdTaken and not acknowledged (GraftTaken); a graft under a stored id is acknowledged as before (AckOnlyStored). Two ids, one origin, both sizes (the rival bodies are in BroadcastNode_taken and _retry). |
| `BroadcastNode_graftOld` | MaxNow 2 -> 1 |
| `BroadcastNode_heldDup` | MaxNow 5 -> 2, TTL 2 -> 1 (the id expires at 2 and the copy is held again), Mids {1, 2} -> {1} |
| `BroadcastNode_heldFull` | MaxNow 5 -> 4 |
| `BroadcastNode_hub` | MaxNow 4 -> 2, TTL 2 -> 1, AcpCap 2 -> 1, LogWin 3 -> 1, Mids {1, 2, 3} -> {1}, SeenCap 3 -> 2, LogRing 4 -> 2, LogCap 2 -> 1 |
| `BroadcastNode_hubcap` | CONSTRAINT EpochsLe3 -> EpochsLe3Quick (at most 2 epochs of an id instead of 3) |
| `BroadcastNode_retry` | Mids {1, 2, 3} -> {1, 2}, SeenCap 3 -> 2 (still room for every id), MaxNow 4 -> 1 A hub whose log holds one message: a second id evicts the first, which the dedupe set (room for all three ids) then remembers with its print. An exact retry of the evicted message is acknowledged (RetryAcked) and another message under the id (another body) is not (AckOnlyStored); one origin, three ids. The copy due no acknowledgement is in BroadcastNode_retryFan. |
| `BroadcastNode_retryFan` | MaxNow 4 -> 1, Mids {1, 2} -> {1} (one message retried at a time) A hub whose log holds one message (a second id evicts the first, which the dedupe set remembers with its print), with the paths PUB and FAN: a copy due no acknowledgement (FAN) is a plain duplicate and compares nothing (UndueDuplicate), beside the retry and the rival of BroadcastNode_retry (two ids; the three-id retry run is in that config). |
| `BroadcastNode_retryLost` | MaxNow 4 -> 1, Mids {1, 2, 3} -> {1, 2}, SeenCap 3 -> 2 (still room for every id) Witness: the print is read only while the id is logged (KeepPrint = FALSE, the rule before the fix). A retry of the message after the log let it go is a duplicate with no acknowledgement: RetryAcked fails, and the publisher gives up. |
| `BroadcastNode_taken` | MaxNow 5 -> 2, TTL 2 -> 1, LogWin 3 -> 1 (the log lets a message go at 2), Mids {1, 2} -> {1} |
| `BroadcastNode_two` | MaxNow 5 -> 1, TTL 2 -> 1, AcpCap 2 -> 1 (HeldMax 2 and FholdMax 2 kept) |
| `BroadcastPending` | MaxCalls 5 -> 4 |
| `BroadcastPending_drop` | MaxCalls 5 -> 4 |
| `BroadcastPublish` | MaxNow 9 -> 8 |
| `BroadcastPublish_batch1` | MaxNow 9 -> 8 |
| `BroadcastPublish_ceiling` | MaxNow 9 -> 8 |
| `BroadcastPublish_evict` | MaxNow 9 -> 8 |
| `BroadcastPublish_evictLost` | MaxNow 9 -> 8 |
| `BroadcastPublish_nohub` | MaxNow 9 -> 8 |
| `BroadcastPublish_nohub_batch1` | MaxNow 9 -> 8 |
| `BroadcastPublish_reach` | MaxNow 9 -> 8 |
| `BroadcastPublish_rival` | MaxNow 9 -> 8 |
| `BroadcastPublish_rivalById` | MaxNow 9 -> 8 |
| `BroadcastPublish_taken` | MaxNow 9 -> 8 |
| `BroadcastPush` | N 4 -> 3, LogCap 3 -> 2 (the log still evicts) |
| `BroadcastPush_away` | N 4 -> 2, LogCap 2 -> 1 (the log still evicts) |
| `BroadcastPush_getdrop` | N 3 -> 2 |
| `BroadcastPush_n6` | Subs {s1, s2} -> {s1}, LogCap 3 -> 2 (N = 6 kept; the log still evicts) |
| `BroadcastPush_nocursor` | N 4 -> 3 |
| `BroadcastPush_noforgot` | N 4 -> 3 |
| `BroadcastPush_nogettell` | N 4 -> 3 |
| `BroadcastPush_noguard` | LogCap 2 -> 1 |
| `BroadcastPush_noresume` | N 3 -> 2 |
| `BroadcastPush_noresume_live` | N 3 -> 2, LogCap 3 -> 2 |
| `BroadcastPush_nosubtell` | N 4 -> 3 |
| `BroadcastPush_notell` | LogCap 2 -> 1 |
| `BroadcastPush_repair` | N 3 -> 2, LogCap 3 -> 2 (as in the deep config, the log never evicts) |
| `BroadcastReach` | N 3 -> 2, TableBytes 12 -> 6 (still no table can overflow) |
| `BroadcastReach_bytes` | TableBytes 5 -> 4 |
| `BroadcastReach_evict` | MaxExpire 2 -> 1 |
| `BroadcastReach_expire` | N 3 -> 2, TableBytes 12 -> 6 (still no table can overflow), MaxExpire 2 -> 1 |
| `BroadcastReach_forget` | MaxExpire 2 -> 1 |
| `BroadcastReach_full` | TableBytes 2 -> 1 |
| `BroadcastReach_hubs3` | bounded by constraint: runs of at most 8 steps (BroadcastReach_hubs3QuickBound); every constant kept |
| `BroadcastReach_liar` | N 3 -> 2, Liars {3} -> {2}, TableBytes 12 -> 6 (still no table can overflow) |
| `BroadcastReach_onesided` | TableBytes 12 -> 10 |
| `BroadcastReach_perevent` | TableBytes 6 -> 5 |
| `BroadcastReach_reopen` | TableBytes 2 -> 1 |
| `BroadcastReach_reopened` | TableBytes 4 -> 3 |
| `BroadcastReach_repair` | TableBytes 6 -> 5 |
| `BroadcastReach_silent` | TableBytes 2 -> 1 |
| `BroadcastReach_table` | MaxExpire 2 -> 1; bounded by constraint: runs of at most 8 steps (BroadcastReach_tableQuickBound); TableBytes 7 as deep (a record is refused while two members hold an edge) |
| `BroadcastRepair` | MaxTime 45 -> 30, Mids {1, 2, 3} -> {1, 2}, LogCap 2 -> 1 (two messages over a log of one: a push still evicts) |
| `BroadcastRepair_ae` | MaxTime 45 -> 36 (the frame logged at 30 and the GAP_AE at 35 that covers it) |
| `BroadcastRepair_gapmark` | MaxTime 45 -> 40 |
| `BroadcastRepair_have` | MaxTime 45 -> 40 |
| `BroadcastRepair_quiet` | MaxTime 45 -> 40 |
| `BroadcastSubs` | Topics {1, 2} -> {1} |
| `BroadcastSubsDelta` | MaxSteps 8 -> 4 |
| `BroadcastSubsDelta_nocap` | Hinted {1, 2} -> {1}, MaxLives 2 -> 1 |
| `BroadcastSubsDelta_nofrom` | Hinted {1, 2} -> {2}, MaxLives 2 -> 1 |
| `BroadcastSubsDelta_nogap` | Hinted {1, 2} -> {1}, MaxLives 2 -> 1 |
| `BroadcastSubsDelta_nohint` | MaxSteps 8 -> 6 |
| `BroadcastSubsDelta_three` | MaxSteps 8 -> 4 |
| `BroadcastSystem` | MaxFlips 3 -> 2 |
| `BroadcastSystem_fb` | MaxFlips 3 -> 2 |
| `BroadcastSystem_live` | MaxFlips 3 -> 2 |
| `BroadcastWire` | AllBytes -> AllBytesQuick: the message id byte held at 0 past the first byte; MaxLen 10 as deep (a head with a public key, tag 1, parses) |
| `BuilderBytes` | Seeds -> SeedsQuick: group sizes {1, 2, 4} -> {1, 2}, lengths up to 4 groups + 1 -> 3 groups + 1, KiB groups {1024, 2048} -> {1024}, arith j 0..54 -> {0, 1, 32, 54} |
| `Cc` | KMAX 3 -> 2 (a loss then an acknowledgement in congestion avoidance) |
| `Cc_pacer` | KMAX 8 -> 5 (one full burst of 3 and two packets of the next: the rate and burst-start checks apply from the 4th packet) |
| `Cc_pacer_limited` | DELAYS {0, 2, 30} -> {0, 30} |
| `Cc_pacer_strict` | DELAYS {0, 2, 30} -> {0, 30} |
| `Cid` | KMAX 9 -> 6, IDXMAX 9 -> 4 (an eviction at index 4; six calls reach a claim of the window again) |
| `Cid_coll` | KMAX 9 -> 5, IDXMAX 9 -> 6 (indices 1 and 4 with the first id are both passed over by the refills) |
| `Cid_collevict` | KMAX 9 -> 5, IDXMAX 9 -> 8 (install and authentications at 2, 4, 6, 8 reach the refill of index 9 and the eviction after it) Index 9 has the id of index 1, at the code's 8 slots: the refill that reaches index 9 makes the entry of index 1 stand for it too, so it is kept while index 9 may be used (the rule before #398 lost it: Cid_skipevict.cfg). |
| `Cid_collmany` | KMAX 9 -> 6, IDXMAX 9 -> 7 (every colliding index, up to 6, is reached by the refills) Indices 1, 3 and 5 share one id, indices 2 and 4 another, and index 6 has the first id. |
| `Cid_collwin` | KMAX 9 -> 5, IDXMAX 9 -> 5 (index 3 with the id of index 2 is reached by the first refills) Index 3 has the id of index 2: the entry of index 2 stands for index 3 too and is kept while index 3 may be used, below the highest index seen as well (the rule before #398 lost it: Cid_skipwin.cfg). |
| `Cid_dupid` | KMAX 9 -> 8 |
| `Cid_firstlag` | KMAX 9 -> 8 |
| `Cid_overlate` | KMAX 9 -> 8 |
| `Cid_overstate` | KMAX 9 -> 8 |
| `Cid_reuse` | KMAX 9 -> 8 |
| `Cid_skipevict` | KMAX 9 -> 8 |
| `Cid_skipwin` | KMAX 9 -> 8 |
| `Cid_slots` | KMAX 9 -> 8 |
| `Cid_stale` | KMAX 9 -> 8 |
| `ConnectCarrier` | MAXF 2 -> 1, JunkLens {0, 2, 4} -> {0, 4}, ReadSizes {1, 5} -> {5} |
| `ConnectCarrier_limits` | WMAX 8 -> 6 |
| `ConnectCarrier_open` | WMAX 8 -> 6, SMAX 2 -> 1 |
| `ConnectCarrier_pn` | WMAX 8 -> 6 |
| `ConnectCarrier_reach` | MAXF 2 -> 1, JunkLens {0, 2, 4} -> {0, 4}, ReadSizes {1, 5} -> {5} (WMAX 10 kept: the witness needs both handshake flights and a record in the window) |
| `ConnectCarrier_w_max` | JunkLens {0, 1, 3} -> {0, 3} |
| `ConnectClient_lookups` | Times {0, 100000, 300001, 2000000, 2300001} -> {0, 300001}, Peers {1, 2, 3} -> {1, 2}, plus ConnectClient_lookupsQuickBound (behaviours of at most 3 calls) |
| `ConnectClient_net` | DoNet -> DoNetQuick (probes sent at 0 only, answers carry address 1 only), CONSTRAINT Bounded (counters to threshold + 1) -> BoundedQuick (to the threshold), plus ConnectClient_netQuickBound (behaviours of at most 4 calls) |
| `ConnectCodec` | the mutation values Vals {0, 2, 13, 32, 255} -> ValsQuick {0, 13, 255}, the frames of the canonical-form check Small (up to 80 bytes) -> SmallQuick (up to 40 bytes) |
| `ConnectDuty` | T 130 -> 65 (two steady beacons, at 5 and 65, after a burst cut short by a step of 4 s), RS {0, 2, 5, 64} -> {2} (a restart in the burst, and after the steady beacons once the clock stepped back to 2) |
| `ConnectDuty_sat` | TOP = T 68 -> 9 (a burst restarted at 5 whose last deadline is the clock's last instant, and probe deadlines that land on it), RS {0, 2, 5, 64} -> {5} |
| `ConnectLink` | Steps StepsC {7 s, 30 s} -> StepsCQuick {30 s}, Horizon 90 s -> 120 s (the lease is learned at 120 s) |
| `ConnectLink_lease` | Horizon 75 s -> 40 s |
| `ConnectLink_restart` | Horizon 6 s -> 2.4 s |
| `ConnectLink_rides` | Horizon 70 s -> 20 s |
| `ConnectLink_ridesHome` | Steps StepsF {3 s, 30 s} -> StepsFQuick {30 s}, Horizon 40 s -> 90 s (time points 0..39 s by 3 -> 0, 30, 60, 90: a keepalive check at 30 s, the reset that learns at 60 s, the ridden check's reset at 90 s) |
| `ConnectMailbox` | MaxSeq 3 -> 2, Times {0, 2, 4} -> {0, 4}, MaxPkt 2 -> 1, B 7 -> 5 (two packets still overflow a member), plus ConnectMailboxQuickBound (behaviours of at most 5 calls) |
| `ConnectMailbox_drain` | Times {0, 2, 4} -> {0, 4}, MaxPkt 2 -> 1, B 7 -> 5, plus ConnectMailbox_drainQuickBound (behaviours of at most 3 calls) |
| `ConnectOwn` | home relays Relays {1, 2} -> {1}, nonces Nonces {1, 2} -> {1} |
| `ConnectOwn_nocap` | addresses Addrs {1, 2, 3} -> {1, 2}, cap Cap 2 -> 1, home relays Relays {1, 2} -> {1}, nonces Nonces {1, 2} -> {1}, wall clocks Walls {1, 2} -> {1} |
| `ConnectOwn_refldup` | addresses Addrs {1, 2, 3} -> {1, 2}, home relays Relays {1, 2} -> {1}, nonces Nonces {1, 2} -> {1}, wall clocks Walls {1, 2} -> {1} |
| `ConnectRecords` | MaxCalls 4 -> 2 |
| `ConnectRecords_own` | MaxCalls 4 -> 2 |
| `ConnectRelay` | Depth 6 -> 3, Times {0, 16, 31} -> {0, 31}, window quota cf.Bytes 3 -> 1 (cfQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) |
| `ConnectRelay_full` | Depth 6 -> 4, Times {0, 16, 31} -> {0, 31}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) The UDP table starts full of other nodes (3 and 4, two slots): an uploaded packet from member 1 finds no room for its stamp, which is no refusal, and the datagram goes on. |
| `ConnectRelay_fwd` | Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) A member that holds mail is no longer asleep, has no route, and is homed at peer relay 5: its packets are forwarded. Peer 5 is present from the start and is the home of node 2's record; the mail comes from a sleep, a close, an SPU packet and the return of the member. |
| `ConnectRelay_long` | Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {1} (ClQuick1), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) A held message too long for the tunnel (1400 bytes, from a peer relay) stands before a short one; a heard member keeps the long one and gets the short one. Mailbox quota 1600 so that both fit. |
| `ConnectRelay_ready` | Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) Readiness and the return of a member are inputs: held messages are kept when the hand-over is refused. |
| `ConnectRelay_refused` | Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) Witness: a refused hand-over of a held message is reachable, so CallsOk's refusal clause is exercised. |
| `ConnectRelay_sleep` | Depth 6 -> 5, Times {0, 16, 31} -> {0, 31}, MaxNs 2 -> 1, MBytes 120 -> 53 (one message fills a mailbox), carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) |
| `ConnectRelay_wfwd` | Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) Witness: with the withdrawn rule (a packet for a member that holds mail is held behind it) the packet of the member homed at peer relay 5 is held and not forwarded, so Forwarded is violated at the 6th call (open 2, sleep, close, SPU 1 to 2, return of 2, SPU 1 to 2). |
| `ConnectRelay_wheard` | Depth 6 -> 5 (the violation is at the 5th call), Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {2} (ClQuick2), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) Witness: with the old rule (nothing is released) a heard member that is ready still holds messages that fit, so HeardDelivers is violated at the 5th call (open 2, sleep, close, SPU 1 to 2, heard 2). |
| `ConnectRelay_wstop` | Times {0, 16, 31} -> {0}, MaxNs 2 -> 1, carrier nodes {1, 2} -> {1} (ClQuick1), peers {5, 6} -> {5} (PeersQuick), MAX_PEERS and ALIAS_MAX 32 -> 2 and 4 (MAXPEERSQuick, AMQuick: the tables never hold more) Witness: with the first round's pass (it stops at the first message that does not fit) the short message behind a long one is not handed over, so StepsOver is violated at the 6th call (open 1, sleep, close, long, short from peer 5, heard 1). |
| `ConnectSleep_beacon` | Times {1, 2, 9} -> {1, 9} (the clocks of ConnectSleep.cfg: a call before every deadline and one at the clock's last instant; no call lands between the first deadline and a later one with beacons on) |
| `ConnectTable` | N 3 -> 2, KeySet {1, 2, 3, 4} -> {1, 2, 3} |
| `ConnectTable_cache` | N 3 -> 2, KeySet {1, 2, 3, 4, 5} -> {1, 2, 3} |
| `ConnectTable_n4` | KeySet {1, 2, 3, 4} -> {1, 2} |
| `ConnectWs_forms` | NF 2 -> 1 (plans of one descriptor) |
| `ConnectWs_ops` | FLs {14000000, 14000002} -> {14000002} (a payload of 2 bytes) |
| `CoreState` | Lives -> LivesQuick (endpoints 3 -> 2: the full one left out), Positions -> PositionsQuick (middle bytes every 7th -> every 21st) |
| `CoreTable` | N 3 -> 2, KeySet {1, 2, 3} -> {1, 2} |
| `CoreTable_chain` | N 3 -> 2, KeySet {1, 2, 3} -> {1, 2} |
| `CoreTable_evict` | N 3 -> 2, KeySet {1, 2, 3, 4} -> {1, 2, 3} |
| `CryptoIdentity` | Flags -> FlagsQuick: verifier flag vectors 16 -> 6 (all on, each off alone, all off) |
| `DgramSize` | the input domain Inputs (1587600 inputs) -> InputsQuick (20736): path 3 -> 2 sizes, interface 5 -> 2, buffer 7 -> 3, amplification 5 -> 3, flight 6 -> 4, handshake 7 -> 4, application 6 -> 3 |
| `DgramSize_noguard` | the input domain Inputs (1587600 inputs) -> InputsQuick (20736): path 3 -> 2 sizes, interface 5 -> 2, buffer 7 -> 3, amplification 5 -> 3, flight 6 -> 4, handshake 7 -> 4, application 6 -> 3 |
| `DgramSize_noiface` | the input domain Inputs (1587600 inputs) -> InputsQuick (20736): path 3 -> 2 sizes, interface 5 -> 2, buffer 7 -> 3, amplification 5 -> 3, flight 6 -> 4, handshake 7 -> 4, application 6 -> 3 |
| `DialReport` | the time scaled down with the flights: Flights 4 -> 1, Promise 30 -> 2, Limit 32 -> 3, MaxNow 36 -> 5 |
| `DialReport_countheld` | the time scaled down with the flights: Flights 4 -> 2 (the early end after 2 + 4 = 6 ticks instead of 30), Promise 30 -> 6, Limit 32 -> 8, MaxNow 36 -> 12 |
| `DialReport_fixed` | the time scaled down with the flights: Flights 4 -> 2 (the early end after 2 + 4 = 6 ticks instead of 30), Promise 30 -> 6, Limit 32 -> 8, MaxNow 36 -> 12, FixedBound 8 -> 4 (four first delays -> two, the flights) |
| `DialReport_floor` | the time scaled down with the flights: Flights 4 -> 2 (the early end after 2 + 4 = 6 ticks instead of 30), Promise 30 -> 6, Limit 32 -> 8, MaxNow 36 -> 12 |
| `DialReport_nobound` | the time scaled down with the flights: Flights 4 -> 2 (the early end after 2 + 4 = 6 ticks instead of 30), Promise 30 -> 6, Limit 32 -> 8, MaxNow 36 -> 12 |
| `DialReport_noreset` | the time scaled down with the flights: Flights 4 -> 2 (the early end after 2 + 4 = 6 ticks instead of 30), Promise 30 -> 6, Limit 32 -> 8, MaxNow 36 -> 12 |
| `DialReport_thin` | the time scaled down with the flights: Flights 4 -> 2 (the early end after 2 + 4 = 6 ticks instead of 30), Promise 30 -> 6, Limit 32 -> 8, MaxNow 36 -> 12 |
| `DtnCodec` | Cases -> CasesQuick (head cases 16 -> 8: word values and layouts paired, not crossed), Positions -> PositionsQuick (post-quantum stride 97 -> 291), Truncs -> TruncsQuick (post-quantum stride 211 -> 633) |
| `DtnCustody` | Budget 3 -> 2, MaxNx 2 -> 1, ByteVals {1,2} -> {1}, ExpVals {1,2} -> {2}, NowVals {0,1,2} -> {0,2} |
| `DtnCustody_deep` | Budget 4 -> 2, MaxSeq 4 -> 3 |
| `DtnForward` | MaxTime 2 -> 1, ExpVals {2} -> {1} (a bundle still expires at the last clock value); T 1 as deep (the transfer table fills) |
| `DtnForwardNet` | T (transfer slots per node) 2 -> 1 |
| `DtnForwardNet_loss` | T (transfer slots per node) 2 -> 1 |
| `DtnForwardNet_over` | Budget 4 -> 3, MaxMsgs 4 -> 2 |
| `DtnForwardNet_replay` | MaxMsgs 3 -> 2, T (transfer slots per node) 2 -> 1 |
| `DtnForward_l1` | T (transfer slots) 2 -> 1, MaxTime 2 -> 1 |
| `DtnGf` | Init -> InitQuick: rows 0..255 -> the 10 of Spread; AllSeqs -> AllSeqsQuick: kernel slices up to length 3 -> 2 |
| `DtnLayout` | Seeds -> SeedsQuick: 10 (k, m) pairs -> 3 (k = 0, k + m = 255 and 256), logs {0, 3, 4, 5} -> {4, 5} |
| `DtnRs_a` | Vals {0, 1, 255} -> {0, 255} |
| `DtnRs_b` | Vals {0, 1, 255} -> {0, 255} |
| `DtnRs_c` | Vals {0, 29, 255} -> {0, 29} |
| `DtnRs_mds` | Mds -> MdsQuick: the Cauchy minors up to 4 x 4 -> 3 x 3 |
| `DtnScenario_chain` | MaxMsgs 2 -> 1 |
| `DtnScenario_contacts` | MaxMsgs 2 -> 1 |
| `DtnScenario_live_relay` | MaxMsgs 2 -> 1 |
| `DtnScenario_replay` | MaxTime 3 -> 1, Exp 3 -> 1 (Exp = MaxTime: a replay is tried before and at the expiry), MaxMsgs 2 -> 1 |
| `DtnScenario_spray` | MaxMsgs 2 -> 1, Budget 4 -> 3 |
| `DtnScenario_tight` | MaxMsgs 2 -> 1, Budget 4 -> 3 |
| `DtnSeal` | MaxB 2 -> 1 (one bundle; the leak sets over 12 -> 10 items, 86016 -> 5120 states) |
| `DtnSeal_decap` | Pays {1, 2} -> {1} |
| `DtnStore` | N 3 -> 2, Budget 4 -> 2, ByteVals {0,1,2,3,5} -> {1,2}, NowVals {0,1,2} -> {0,1} |
| `Early` | packets KMAX 5 -> 3; RecvStep -> RecvStepQuick: datagram lengths 1..2 -> {1} |
| `Early_cap3` | packets KMAX 5 -> 4; RecvStep -> RecvStepQuick: datagram lengths 1..2 -> {1} |
| `Encoder` | WalkK 8 -> 3, Seeds -> SeedsQuick (the powers of two 0..64 -> 13 around the edges, the big logs {0, 10, 20} -> {0, 20}, the overflow multiples 0..30 -> {0, 1, 2, 30}, the encoded multiples 0..4 -> 0..2) |
| `ExtIn` | CAP 3 -> 2, PMAX 9 -> 5 |
| `FacadeAcpForget` | bounded by constraint: behaviours of depth 8 (FacadeAcpForgetQuickBound); one peer and two listed protocols are what it is about The code as built, one peer and two listed protocols taken either way, any hook to start with (the host may edit it). Revoke, unrevoke and admission_changed drop both answers of the peer, a dial to a revoked peer is refused before anything is sent, each session is decided on its own protocol and direction, the endpoint is told whether the peer is allowed any of the questions it is asked about, its own sessions and dials among them, and a dial the gate allows drops a refusal held for its peer. |
| `FacadeAcpForget_two` | bounded by constraint: behaviours of depth 5 (FacadeAcpForget_twoQuickBound) |
| `FacadeRecords` | MaxSeq 3 -> 2 |
| `FacadeRelayCarriers_end` | MAXH 2 -> 1 (one stream accepted in all: a full handshake or carrier table is not reached over the end of a run; the deep FacadeRelayCarriers.cfg reaches them with 3) |
| `FacadeRelayKeep` | TMAX 3 -> 2, CLOCKS {0, 1, 3} -> {0, 2} (a restart at 0 or later, back in time or ahead), SEQS 2 -> 1 (one record per node, no higher seq), PMAX 3 -> 1 and MBP 2 -> 1 (one packet held; FacadeRelayKeep_mailq keeps the mailbox bounds) |
| `FacadeRelayKeep_fail` | TMAX 3 -> 2, CLOCKS {0, 1, 3} -> {0, 2} (a restart at 0 or later, back in time or ahead), SEQS 2 -> 1 (one record per node, no higher seq), PMAX 3 -> 1 and MBP 2 -> 1 (one packet held; FacadeRelayKeep_mailq keeps the mailbox bounds), TORN {noverify, prefix} -> {} (a restart loses the write out or lands it whole; the torn writes are the quick FacadeRelayKeep and _rerun profiles') |
| `FacadeRelayKeep_rerun` | TMAX 3 -> 2, CLOCKS {0, 1, 3} -> {0, 2} (a restart at 0 or later, back in time or ahead), SEQS 2 -> 1 (one record per node, no higher seq), PMAX 3 -> 1 and MBP 2 -> 1 (one packet held; FacadeRelayKeep_mailq keeps the mailbox bounds) |
| `FacadeRelayKeep_sweep` | TMAX 3 -> 2, CLOCKS {0, 1, 3} -> {0, 2} (a restart at 0 or later, back in time or ahead), SEQS 2 -> 1 (one record per node, no higher seq), PMAX 3 -> 1 and MBP 2 -> 1 (one packet held; FacadeRelayKeep_mailq keeps the mailbox bounds) |
| `FacadeRevoke` | Peers {p1, p2} -> {p1}, Slots {1, 2} -> {1} |
| `FacadeRevoke_nobackstop` | Peers {p1, p2} -> {p1}, Slots {1, 2} -> {1} |
| `FacadeStandby` | tickets held LIVE 3 -> 2, handed out AMAX 7 -> 4 |
| `FacadeStandby_wrap` | wakers W {1, 2} -> {1} |
| `FacadeTurn` | F {1, 2, 3} -> {1, 2} |
| `FacadeTurn_live` | F {1, 2, 3} -> {1, 2} |
| `FacadeTurn_role` | F {1, 2, 3} -> {1, 2} |
| `FacadeTurn_two` | STARTS 3 -> 2, DMAX 3 -> 1, DRAIN 2 -> 1 |
| `FacadeTurn_wrap` | bounded by constraint: the owner starts at most once (FacadeTurn_wrapQuickBound), STARTS = 6 kept for the other future |
| `FacadeTurn_wrapfew` | STARTS 4 -> 2 |
| `Frame` | the frames: Frames (545) -> FramesQuick (177), the 130-byte payload in 7 frames instead of 81 |
| `FramePack` | Normal -> NormalQuick (41472 -> 544 normal cases: every source together, every switch apart), Other -> OtherQuick (rooms {24, 40, 64} -> {24, 64}, ACKs 3 -> 2, streams 4 -> 3) |
| `FramePack_modes` | Normal -> NormalQuick (41472 -> 544 normal cases: every source together, every switch apart), Other -> OtherQuick (rooms {24, 40, 64} -> {24, 64}, ACKs 3 -> 2, streams 4 -> 3) |
| `Frame_acks` | MAXPN 5 -> 2, the range lists: every list of up to MAXRANGES ranges and 16 of MAXRANGES + 1 (RangeListsQuick) |
| `Frame_bytes` | Strings -> StringsQuick: strings of up to 4 bytes -> 3, ack bytes after the type 5 -> 4 |
| `Frame_nonminimal` | Strings -> StringsQuick: strings of up to 4 bytes -> 3, ack bytes after the type 5 -> 4 |
| `Frame_off` | Strings -> StringsQuick: strings of up to 4 bytes -> 3, ack bytes after the type 5 -> 4 |
| `HalfOpen` | LIFE = HOLD 2 -> 1 (still a thin node), TMAX 4 -> 2, LENS {0, 1, 2, 3} -> {0, 3} |
| `HalfOpen_answer` | TMAX 4 -> 3 (an answered session still reaches its end, created + HOLD + 1) |
| `HalfOpen_gone` | TMAX 2 -> 0, LENS {0, 1, 2, 3} -> {3} |
| `HalfOpen_half` | TMAX 1 -> 0 |
| `HalfOpen_held` | TMAX 3 -> 0, LENS {0, 1, 2, 3} -> {3} (no session reaches its end by the clock: that end is met by the deep config, TMAX 3; a timer call still frees a connection that ended) GREEN: the bound on the holders of one id at three slots and a cap of two, every length of every type, one id. |
| `HalfOpen_noroom` | TMAX 2 -> 0, LENS {0, 1, 2, 3} -> {3} |
| `HalfOpen_owedest` | TMAX 2 -> 0, LENS {0, 1, 2, 3} -> {3} |
| `HalfOpen_rejfill` | TMAX 4 -> 0, LENS {0, 1, 2, 3} -> {3} |
| `HalfOpen_room` | TMAX 3 -> 1, LENS {0, 1, 2, 3} -> {3} (no session reaches its end by the clock: that end is met by the deep config, TMAX 3) |
| `HalfOpen_room2` | TMAX 3 -> 0, LENS {0, 1, 2, 3} -> {3} (no session reaches its end by the clock: that end is met by the deep config, TMAX 3; a timer call still frees a connection that ended) |
| `HalfOpen_sub` | TMAX 2 -> 0, LENS {0, 1, 2, 3} -> {3} |
| `Handshake` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: at most 3 messages sent (HandshakeQuickBound) |
| `Handshake_kbroken` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: at most 3 messages sent and 6 levels (Handshake_kbrokenQuickBound) |
| `Handshake_late` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: behaviours of at most 6 levels (Handshake_lateQuickBound) |
| `Handshake_pskleak` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: behaviours of at most 6 levels (Handshake_pskleakQuickBound) |
| `Handshake_resume` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: at most 3 messages sent (Handshake_resumeQuickBound) |
| `Handshake_stores` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: behaviours of at most 8 levels (Handshake_storesQuickBound) |
| `Handshake_stores_xbroken` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: behaviours of at most 8 levels (Handshake_stores_xbrokenQuickBound) |
| `Handshake_xbroken` | byte budgets RB 9 -> 4, LB 30 -> 3; bounded by constraint: at most 3 messages sent and 6 levels (Handshake_xbrokenQuickBound) |
| `Hdr` | the byte alphabet Alpha (7 bytes) -> AlphaQuick (5), the pieces of the cat case Pieces (9) -> PiecesQuick (6) |
| `HdrBody` | Next -> NextQuick (the handshake cases 3 x 3 ids x 19 x 19 words x 4 lengths = 12996 -> 7 id pairs x 22 word pairs x 3 lengths = 462, the reassembly totals 7 -> 6, offsets 9 -> 7 and lengths 5 -> 4, the byte strings up to 6 -> up to 3 bytes) |
| `HeaderProt` | FirstSet 0..255 -> 0..31 and 224..255 (every pattern of the 5 bits the mask can touch, under the 3 high bits all clear and all set) |
| `HeaderProt_pn` | field and mask bytes Smp {0,165,255} -> {0,165} |
| `Heap` | N 5 -> 4, T 2 -> 1 |
| `Held` | ring CAP 3 -> 2, pushes PMAX 9 -> 6 |
| `HubCodec_snap` | Snaps -> SnapsQuick: snapshot entries up to 3 -> 2 |
| `HubCodec_snapn` | MutPos -> MutPosQuick, CutPos -> CutPosQuick (entry boundaries mutated and cut: all 64 or 65 entries -> the first 3 and the last 3) |
| `Incarnation` | MaxSteps 4 -> 3 |
| `Incarnation_hlc` | MaxSteps 5 -> 4 |
| `IntegrationCodecs` | the IPv6 relay addresses Addrs (all 390625 over 0..4) -> AddrsQuick (1600: each segment over the values relay_parts tells apart) |
| `IntegrationCodecs_sid` | Addrs, Built and TagStrs (billions of values) -> UnreadQuick ({}) and the properties RelayRT, RelayInv, RelayNone, TagAll and TagBoundary (2 * 256 * 65536 cases for RelayRT) -> UncheckedQuick (TRUE): none is read by the sid properties, TLC evaluates them at start; the stream ids Wd 14 widths -> WdQuick 6, the old ids Olds 7 -> OldsQuick 3 (of 1, 2 and 9 bytes), the rests SRests 15 -> SRestsQuick 9 (around where a new id stops fitting) |
| `IntegrationCodecs_tag64` | the bounds are those of the deep config; the definitions cTagBoundary does not read, which TLC evaluates at start (RelayRT alone is 2 * 256 * 65536 cases, Addrs, Built and TagStrs billions of values, SRests and Bodies sequences of up to 1217 bytes), are substituted: the properties by UncheckedQuick (TRUE), the sets by UnreadQuick ({}) |
| `IntegrationCodecs_w_nobound` | the IPv6 relay addresses Addrs (all 390625 over 0..4) -> AddrsQuick (1600: each segment over the values relay_parts tells apart) |
| `IntegrationCodecs_w_nocap` | Addrs, Built and TagStrs (billions of values) -> UnreadQuick ({}) and the properties RelayRT, RelayInv, RelayNone, TagAll and TagBoundary (2 * 256 * 65536 cases for RelayRT) -> UncheckedQuick (TRUE): none is read by the sid properties, TLC evaluates them at start; the stream ids Wd 14 widths -> WdQuick 6, the old ids Olds 7 -> OldsQuick 3 (of 1, 2 and 9 bytes), the rests SRests 15 -> SRestsQuick 9 (around where a new id stops fitting) |
| `IntegrationCodecs_w_readpast` | the IPv6 relay addresses Addrs (all 390625 over 0..4) -> AddrsQuick (1600: each segment over the values relay_parts tells apart) |
| `IntegrationCodecs_w_sidskip` | Addrs, Built and TagStrs (billions of values) -> UnreadQuick ({}) and the properties RelayRT, RelayInv, RelayNone, TagAll and TagBoundary (2 * 256 * 65536 cases for RelayRT) -> UncheckedQuick (TRUE): none is read by the sid properties, TLC evaluates them at start; the stream ids Wd 14 widths -> WdQuick 6, the old ids Olds 7 -> OldsQuick 3 (of 1, 2 and 9 bytes), the rests SRests 15 -> SRestsQuick 9 (around where a new id stops fitting) |
| `IntegrationCodecs_w_tagzero` | the IPv6 relay addresses Addrs (all 390625 over 0..4) -> AddrsQuick (1600: each segment over the values relay_parts tells apart) |
| `IntegrationCodecs_w_wlong` | the IPv6 relay addresses Addrs (all 390625 over 0..4) -> AddrsQuick (1600: each segment over the values relay_parts tells apart) |
| `Keepalive` | times NOWS {0, 20, 100, 110} -> {100, 110}, TXS {0, 95, 100} -> {0, 95}, RXS {0, 100} -> {0}, APPS {0, 85, 100} -> {0, 85} |
| `KeyRoll` | MaxPn 2 -> 1, MaxTime 2 -> 1 |
| `KeyRoll_collide` | MaxPn 2 -> 1 (both requests, the answer and a packet under the new key still fit); bounded by constraint: behaviours of at most 8 levels (KeyRoll_collideQuickBound) |
| `KeyRoll_forge` | MaxTime 2 -> 1, Sat 2 -> 1; bounded by constraint: behaviours of at most 8 levels (KeyRoll_forgeQuickBound) |
| `KeyRoll_gate` | MaxPn 2 -> 1 (a request, its resend and the answer still fit) |
| `KeyRoll_good` | MaxPn 2 -> 1, MaxTime 2 -> 1, Sat 2 -> 1 (one roll in all: Cap0 = Cap1 = 1) |
| `KeyRoll_stale` | MaxPn 2 -> 1, MaxTime 2 -> 1 |
| `KeyRoll_two` | MaxPn 2 -> 1 |
| `KeystoreSealed` | the alteration symbols Syms (of the blobs of both keys) -> SymsQuick (of the blobs of key k1), the representatives Reps 8 -> RepsQuick 4 (the one-symbol header) |
| `KeystoreStore` | steps MaxSteps 6 -> 3 (MaxSteps <- MaxStepsQuick) |
| `Layout` | SmallLen 2100 -> 150, PreN 24 -> 9, Seeds -> SeedsQuick (every family over fewer values, the boundary ones kept) |
| `MembershipConv` | Init -> InitQuick: the second view's starts 9 -> 1 (the empty view; 6561 -> 729 initial states) |
| `MembershipSys_complete` | MaxSec 190 -> 186 (Aware4 applies only when now - crash (at 40) > 145 s, so MaxSec must exceed 185) |
| `MembershipSys_complete33` | MaxSec 190 -> 186 (Aware4 applies only when now - crash (at 40) > 145 s, so MaxSec must exceed 185) |
| `MembershipSys_direct` | MaxSec 90 -> 70 |
| `MembershipSys_healwait` | MaxSec 120 -> 100 |
| `MembershipSys_live_complete` | MaxSec 400 -> 100 |
| `MembershipSys_live_heal` | MaxSec 400 -> 155 |
| `MembershipSys_live_lease` | MaxSec 400 -> 160 |
| `MembershipSys_live_leave` | MaxSec 250 -> 60 |
| `MembershipSys_live_return` | MaxSec 250 -> 80 |
| `MembershipSys_live_stale` | MaxSec 700 -> 280 |
| `MembershipSys_live_w_never` | MaxSec 250 -> 60 |
| `MembershipSys_live_w_stale` | MaxSec 700 -> 280 |
| `MembershipSys_lostprobe` | MaxSec 90 -> 70 |
| `MembershipSys_move` | MaxSec 60 -> 50 |
| `MembershipSys_partition` | MaxSec 260 -> 200 |
| `MembershipSys_primary` | MaxSec 160 -> 80, Script ScrPrimaryHyst -> ScrPrimaryHystQuick (the drop to 40 ms at 20 s, not 100 s) |
| `MembershipSys_revoke` | MaxSec 60 -> 50 |
| `MembershipSys_steady` | MaxSec 200 -> 100 |
| `MembershipSys_w_clockback` | MaxSec 120 -> 70 |
| `MembershipSys_w_confirm` | MaxSec 60 -> 50 |
| `MembershipSys_w_direct` | MaxSec 90 -> 60 |
| `MembershipSys_w_down` | MaxSec 190 -> 60 |
| `MembershipSys_w_finished` | MaxSec 400 -> 155 |
| `MembershipSys_w_healseen` | MaxSec 120 -> 85 |
| `MembershipSys_w_healwait` | MaxSec 120 -> 95 |
| `MembershipSys_w_leavelost` | MaxSec 90 -> 50 |
| `MembershipSys_w_left` | MaxSec 60 -> 50 |
| `MembershipSys_w_lefttimer` | MaxSec 60 -> 45 |
| `MembershipSys_w_lostprobe_susp` | MaxSec 60 -> 45 |
| `MembershipSys_w_refused` | MaxSec 90 -> 60 |
| `MembershipSys_w_restart` | MaxSec 100 -> 70 |
| `MembershipSys_w_restore` | MaxSec 100 -> 60 |
| `MembershipSys_w_revoked` | MaxSec 60 -> 45 |
| `MembershipSys_w_susp` | MaxSec 190 -> 50 |
| `MembershipSys_w_switch` | MaxSec 160 -> 70, Script ScrPrimaryHyst -> ScrPrimaryHystQuick (the drop to 40 ms at 20 s, not 100 s) |
| `Mtu` | KMAX 5 -> 4 (the drop to the floor takes four calls) |
| `NodeBackoff` | TIMES {0, 70 s, u64::MAX} -> {0, u64::MAX} (TimesDefQuick); bounded by constraint: behaviours of at most 4 levels (NodeBackoffQuickBound) |
| `NodeBackoff_denymax` | PEERS {1, 2} -> {1} (the hub), TIMES {0, 70 s, u64::MAX} -> {0, u64::MAX} (TimesDefQuick) |
| `NodeValues` | NMAX 3 -> 2 (at most 2 streams added in a behaviour), SIDS {1, 2, 3} -> {1, 2} (a hung-up session and its redial) |
| `NodeSets` | SIDS {1, 2, 3} -> {1, 2} (a dial, a filler's session, and the endpoint refusing a third), NSTARTS 2 -> 1 (one round in all: a start refused Busy is not reached, NodeSets_busy is its witness) |
| `NodeSets_cancel` | SIDS {1, 2, 3} -> {1, 2} (a dial, a filler's session, and the endpoint refusing a third), NSTARTS 2 -> 1 (one round in all: a start refused Busy is not reached, NodeSets_busy is its witness) |
| `NodeSets_two` | SIDS {1, 2} -> {1} (one session at a time: two rounds share it, or the other peer's dial is refused), ATTEMPTS 2 -> 1 (a round ends Exhausted at its first failure; the retries are the quick NodeSets profile's), TMAX 1 -> 0 (no saturated clock; the quick NodeSets profile keeps it) |
| `NodeSets_way` | SIDS {1, 2, 3} -> {1, 2} (a dial, a filler's session, and the endpoint refusing a third), NSTARTS 2 -> 1 (one round in all: a start refused Busy is not reached, NodeSets_busy is its witness) |
| `Orphan` | the time scaled down: LIFE 2 -> 1, TAKE_LIFE 2 -> 1, TMAX 4 -> 2; MAX 2 -> 1, HMAX 4 -> 3 |
| `PortMapLease` | last tick MaxT 7 -> 4, tries Tries 2 -> 1; bounded by constraint: behaviours of depth 14 (PortMapLeaseQuickBound) |
| `PrekeyCache` | MaxClock 6 -> 4 (the cache fills, a get refreshes the older entry, the next insert evicts the least recently used) |
| `PrekeyCache_n3` | MaxClock 6 -> 3 (the cache fills; the invariants insert into the full cache) |
| `Queue` | PMAX 7 -> 4 |
| `Queue_wrap` | PMAX 8 -> 5, CL {1, 2, 3, 5} -> {1} (four pushes of one class and four pops wrap the head of the ring of CAP 4) |
| `Reach` | N 3 -> 2, S 4 -> 3, PMAX 9 -> 6 |
| `Reconcile` | UniMax 5 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `ReconcileWire` | BLen 3 -> 2, RAlpha {0, 1, 2, 3} -> {0, 1, 2}, RLen 5 -> 3; Seeds <- SeedsQuick and Expand <- ExpandQuick (smaller literal case domains, see ReconcileWire.tla) |
| `ReconcileWire_cap1` | BLen 3 -> 2, RAlpha {0, 1, 2, 3} -> {0, 1, 2}, RLen 5 -> 3; Seeds <- SeedsQuick and Expand <- ExpandQuick (smaller literal case domains, see ReconcileWire.tla) |
| `Reconcile_cap` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_cold` | UniMax 6 -> 4; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_collide` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_dense` | UniMax 6 -> 4; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_frames` | UniMax 5 -> 4; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_garbage` | UniMax 3 -> 0; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_garbage3` | UniMax 3 -> 0; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_liar` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_never` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_real` | UniMax 585 -> 60 (A has items 5..59, B lacks 40 and 41); the same values, built without the byte XOR table, the sort of every word and SUBSET of the universe (Xor8, XorTab, SubSets, UniSeq, AllSeq, IdxOf <- their Quick twins) |
| `Reconcile_real_big` | UniMax 585 -> 100 (A has items 5..99, B lacks 40 and 41); the same values, built without the byte XOR table, the sort of every word and SUBSET of the universe (Xor8, XorTab, SubSets, UniSeq, AllSeq, IdxOf <- their Quick twins) |
| `Reconcile_real_cold` | UniMax 585 -> 45 (the cold sides of 4 items against 42, and 0 against 45); the same values, built without the byte XOR table, the sort of every word and SUBSET of the universe (Xor8, XorTab, SubSets, UniSeq, AllSeq, IdxOf <- their Quick twins) |
| `Reconcile_real_dense` | UniMax 585 -> 147 (every word under the first byte 1 is still in the universe); the same values, built without the byte XOR table, the sort of every word and SUBSET of the universe (Xor8, XorTab, SubSets, UniSeq, AllSeq, IdxOf <- their Quick twins) |
| `Reconcile_real_swap` | UniMax 585 -> 60 (B has items 5..59, A lacks 40 and 41); the same values, built without the byte XOR table, the sort of every word and SUBSET of the universe (Xor8, XorTab, SubSets, UniSeq, AllSeq, IdxOf <- their Quick twins) |
| `Reconcile_real_varlen` | UniMax 585 -> 50 (A has 25 items, B 40); the same values, built without the byte XOR table, the sort of every word and SUBSET of the universe (Xor8, XorTab, SubSets, UniSeq, AllSeq, IdxOf <- their Quick twins) |
| `Reconcile_reset` | UniMax 3 -> 2; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_varlen` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_chunk` | UniMax 5 -> 4; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_cold` | UniMax 5 -> 4; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_done` | UniMax 4 -> 2; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_exhausted` | UniMax 3 -> 2; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_held` | bounds unchanged (UniMax 4 does not reach the witness); Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes), so the 65536-entry table is not built at start-up |
| `Reconcile_w_mismatch` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_miss` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Reconcile_w_refused` | bounds unchanged (UniMax 2 does not reach the witness); Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes), so the 65536-entry table is not built at start-up |
| `Reconcile_w_tmr` | bounds unchanged (UniMax 4 does not reach the witness); Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes), so the 65536-entry table is not built at start-up |
| `Reconcile_w_toolarge` | UniMax 4 -> 3; Xor8 <- Xor8Quick and XorTab <- XorTabQuick (the byte XOR from a 16 x 16 table of half bytes) |
| `Record` | MaxPn 3 -> 2, AesLimit 2 -> 1, ChachaLimit 2 -> 1, MaxGen 3 -> 2, Sat 3 -> 2 |
| `Record_chacha` | MaxPn 3 -> 1, AesLimit 2 -> 1, ChachaLimit 2 -> 1, Sat 3 -> 2 |
| `Recovery` | PNMAX 2 -> 1, SIZES {1, 2} -> {1}, PMAX 1 -> 0, HOR 90 -> 45 (KMAX 4 kept: a probe firing needs send, ack, send, timeout) |
| `Recovery_asleep` | PNMAX 2 -> 1, SIZES {1, 2} -> {1}, PMAX 1 -> 0, HOR 90 -> 45 (KMAX 4 kept: a probe firing needs send, ack, send, timeout) |
| `Recovery_asleep_w` | SIZES {1, 2} -> {1}, PMAX 1 -> 0 (the time-threshold loss on a timeout while asleep is still found) |
| `Recovery_flags` | PNMAX 2 -> 1, HOR 90 -> 45, LATEN 2 -> 1 |
| `Recovery_flushdown` | PNMAX 2 -> 1, SIZES {1, 2} -> {1}, PMAX 1 -> 0, HOR 90 -> 45, LATEN 2 -> 1 (KMAX 4 kept: a probe firing needs send, ack, send, timeout) |
| `RekeyCodec` | Shares -> SharesQuick: 3 shares -> 1 |
| `ReplyPath` | NP 4 -> 2 places, Ids {1..5} -> {1, 2, 3} (one more than the places, so a full table meets a new path), HDMAX 2 -> 1 |
| `Rtt` | CAP 2 -> 1, PEERS {1, 2, 3} -> {1, 2} (one peer past a full table still), DEPTH 4 -> 3 |
| `Rx` | KMAX 4 -> 3, SENTN 2 -> 1, CONFN 2 -> 1, HOR 400 -> 30 (three calls still overflow CAP 2 and fill both tables) |
| `Rx_wide` | SENTN 3 -> 1, CONFN 2 -> 1, HOR 300 -> 0 (KMAX 4 kept: four packets overflow CAP 3) |
| `Streams` | HOR 3 -> 1, LMAX 2 -> 1, MAXOFF 8 -> 5, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps, the same behaviours); one byte of data and one grant (limit 4 -> 5); no window grows: that needs 3 bytes read in one round trip (HOR 3) |
| `Streams_cap` | Next -> NextQuick (no stuttering calls, the same behaviours); bounded by constraint: behaviours of at most 5 levels (Streams_capQuickBound) |
| `Streams_caps` | HOR 2 -> 1, Next -> NextQuick (Next without its stuttering steps) |
| `Streams_early` | Next -> NextQuick (no stuttering calls, the same behaviours); bounded by constraint: behaviours of at most 5 levels (Streams_earlyQuickBound) |
| `Streams_early_ctl` | Next -> NextQuick (Next without its stuttering steps), OpenBound kept; bounded by constraint: behaviours of at most 5 levels (Streams_early_ctlQuickBound) |
| `Streams_ext` | HOR 2 -> 1, LMAX 2 -> 1, MAXOFF 6 -> 5, EXTMAX 3 -> 2, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps) |
| `Streams_held` | HOR 2 -> 1, MAXOFF 12 -> 5, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps) |
| `Streams_held_w` | HOR 2 -> 1, MAXOFF 8 -> 5, Next -> NextQuick (Next without its stuttering steps, the same behaviours) (stream 4 held back while stream 0 holds the one slot, admitted once it is freed) |
| `Streams_lazy_ledger` | HOR 3 -> 1, LMAX 2 -> 1, MAXOFF 12 -> 5, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps, the same behaviours); one byte of data and one grant (limit 4 -> 5); no window grows: that needs 3 bytes read in one round trip (HOR 3) |
| `Streams_ledger` | HOR 3 -> 1, LMAX 2 -> 1, MAXOFF 12 -> 5, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps, the same behaviours); one byte of data and one grant (limit 4 -> 5); no window grows: that needs 3 bytes read in one round trip (HOR 3) |
| `Streams_live` | HOR 4 -> 1, LMAX 2 -> 1, MAXOFF 12 -> 5, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps, the same behaviours) |
| `Streams_live_ext` | HOR 2 -> 1, LMAX 2 -> 1, MAXOFF 6 -> 5, EXTMAX 2 -> 1, DT 1 -> 0 (one byte of data and one grant; the clock is held, as HOR 1 lets no window grow from the meter); SWC 2 -> 1 (the initial window within HOR 1, so a reader can drain it and be Blocked at its limit) |
| `Streams_live_mid` | HOR 3 -> 1, LMAX 2 -> 1, MAXOFF 6 -> 5, DT 1 -> 0 (one byte of data and one grant; the clock is held, as HOR 1 lets no window grow from the meter); SWC 2 -> 1 (the initial window within HOR 1, so a reader can drain it and be Blocked at its limit) |
| `Streams_local` | MAXOFF 6 -> 4, Next -> NextQuick (Next without its stuttering steps); bounded by constraint: behaviours of at most 4 levels (Streams_localQuickBound) |
| `Streams_local_ctl` | MAXOFF 6 -> 5, Next -> NextQuick (Next without its stuttering steps, the same behaviours) |
| `Streams_mark` | Next -> NextQuick (Next without its stuttering steps); bounded by constraint: behaviours of at most 5 levels (Streams_markQuickBound) |
| `Streams_meter_w` | B 4 -> 3, Next -> NextQuick (Next without its stuttering steps, the same behaviours) (stream 4 still takes twice the connection's rate) RED for METER (#159): one meter for the whole connection, as before the fix. Stream 0 reads its byte, and a round trip later its meter closes an epoch at a rate of 1; stream 4 then reads its first byte and, having drained nothing it could measure yet, takes twice the connection's rate (2) as its window where its own rate asks for the initial window (1). With sixteen streams on a real path the windows together asked the pool for sixteen times the credit the connection moved, so most grants were deferred and the last streams crawled at one window per round trip. TLC must find a violation of SizeFollowsOwnRate. |
| `Streams_release` | Next -> NextQuick (Next without its stuttering steps); bounded by constraint: behaviours of at most 5 levels (Streams_releaseQuickBound) |
| `Streams_stall` | HOR 4 -> 1, LMAX 2 -> 1, MAXOFF 12 -> 5, DT 1 -> 0, Next -> NextQuick (Next without its stuttering steps, the same behaviours) (a grant deferred while the other users hold 2 or more chunks is still found stuck) |
| `Streams_stop` | HOR 3 -> 2, LMAX 2 -> 1, MAXOFF 4 -> 3 (frames of one byte ending by offset 2: one window read and raised once still, to 3), Next -> NextQuick (Next without its stuttering steps, the same behaviours) |
| `Tickets` | ExpVals {1, 2} -> {1}, MaxClock 4 -> 3, Ids {1, 2, 3} -> {1} (the ids are drawn by a server only; NS = 0) |
| `Tickets_n3` | ExpVals {1, 2} -> {1} (live at now 1, expired at now 2), MaxClock 4 -> 3 (the store fills; the invariants insert into the full store), server-side Ids {1, 2, 3} -> {1} |
| `Tickets_server` | MaxClock 3 -> 2 (the store fills; the invariants issue into the full store), draw streams of 0..4 -> 0..3 ids (Streams <- StreamsDefQuick), client-side Peers {p1, p2, p3} -> {p1}, Alpns {a1, a2} -> {a1}, Ids {1, 2, 3} -> {1, 2} (a draw still collides with a stored id and a retry still finds a fresh one), ExpVals {1, 2} -> {1} |
| `Timers` | clock TMAX 5 -> 4, calls KMAX 4 -> 2, component deadlines CD {0, 4} -> {0} |
| `Transcript` | MaxFields 4 -> 3 |
| `ValuesPlan` | MaxLen 11 -> 7 |
| `ValuesPlanProofs` | MaxF 48 -> 4, LNs 6 -> 5 (4097 groups dropped), PfTos {0, 8G, l, l+5G} -> {0, 8G, l}, Offs {0, l/2, l, l+3G} -> {0, l/2, l+3G}, Wins {0, 64, 400} -> {0, 400} |
| `ValuesPlanServer` | Reqs (the 7 requests of at most 2 of 3 spans) -> {{<<0,1>>}, {<<3,1>>}} |
| `ValuesPlanSource` | MaxN 12 -> 6, the cases CaseSet (36) -> CaseSetQuick (9: one, two and three spans, no hole or one of two holes) |
| `ValuesPlan_tight` | MaxLen 11 -> 8 |
| `ValuesPlan_word` | MaxLen 20 -> 14 |
| `ValuesSchedList` | MAXU 7 -> 3; N 4 as deep (SplitOk splits an aligned one-span list) |
| `ValuesSched_liar` | NG 4 -> 2 |
| `ValuesSched_n2` | NG 4 -> 2 |
| `ValuesSched_n3` | NG 4 -> 2 |
| `ValuesSched_silent` | NG 4 -> 2 |
| `ValuesSched_tight` | NG 5 -> 4 (every span of WantsMix and every group of InitvTwo still lies in the value) |
| `ValuesSched_track` | NG 4 -> 2 |
| `ValuesSched_wants` | NG 5 -> 4 (every span of WantsA and every group of InitvA still lies in the value) |
| `ValuesSys_code` | G 6 -> 5, Want {0..5} -> {0..4} (still more groups than MinT 4, so the value is striped) |
| `ValuesSys_code_steal` | G 6 -> 5, Want {0..5} -> {0..4} (provider 1 still takes MinT 4 groups, at least SMIN 2 to steal) |
| `ValuesSys_loss` | G 3 -> 2, Want {0,1,2} -> {0,1} |
| `ValuesSys_mid` | G 3 -> 2, Want {0,1,2} -> {0,1} |
| `ValuesSys_n1` | G 3 -> 2, Want {0,1,2} -> {0,1} |
| `ValuesSys_n4` | Liars {2,3,4} kept; bounded by constraint: behaviours of at most 28 steps (ValuesSys_n4QuickBound) |
| `ValuesSys_slow` | G 3 -> 2, Want {0,1,2} -> {0,1} |
| `ValuesTime_dl` | MaxN 8 -> 3 |
| `ValuesTime_hold` | MaxN 10 -> 7, TimeSet {0,1,2,3} s -> {0,3} s |
| `ValuesTime_holdsmall` | NG 5 -> 4, WantG {0..4} -> {0..3}, MaxN 13 -> 4 |
| `ValuesTime_live` | MaxN 6 -> 3 |
| `ValuesTime_stall` | MaxN 6 -> 3, TimeSet {0,1,3,9,17,33,100} s -> {0,1,9,17} s |
| `ValuesTime_wbufreal` | MaxN 9 -> 7, TimeSet {0,1,2,3} s -> {0} s |
| `ValuesVerify` | the seed lengths -> fewer (NextQuick with MySeedsQuick: tiny 0..5 -> {0, 1, 3, 5}; small 0..7 and 0..13 -> {0, 3, 7} and {5, 13}; small_skip 0..5 -> {0, 1, 3, 5}) |
| `ValuesVerifyRx` | Genuine -> GenuineQuick: value lengths 0..7 (groups of 2) and 0..13 (groups of 4) -> {0, 1, 3, 5} and {5, 9} |
| `ValuesVerifyRx_nowhole` | Genuine -> GenuineQuick: value lengths 0..7 (groups of 2) and 0..13 (groups of 4) -> {0, 1, 3, 5} and {5, 9} |
| `ValuesVerify_real32` | the value lengths {g + 1, 3 g} -> {3 g} and the requested ranges {0..2, 1..2, 0..1} -> {0..2} (Next <- NextQuick) |
| `ValuesVerify_real64` | the value lengths {g + 1, 3 g} -> {3 g} and the requested ranges {0..2, 1..2, 0..1} -> {0..2} (Next <- NextQuick) |
| `ValuesVerify_skip` | the seed lengths -> fewer (NextQuick with MySeedsQuick: tiny 0..5 -> {0, 1, 3, 5}; small 0..7 and 0..13 -> {0, 3, 7} and {5, 13}; small_skip 0..5 -> {0, 1, 3, 5}) |
| `ValuesVerify_skip2` | the seed lengths -> fewer (NextQuick with MySeedsQuick: tiny 0..5 -> {0, 1, 3, 5}; small 0..7 and 0..13 -> {0, 3, 7} and {5, 13}; small_skip 0..5 -> {0, 1, 3, 5}) |
| `ValuesVerify_small` | the seed lengths -> fewer (NextQuick with MySeedsSmallQuick: 2-byte groups 0..7 -> {0, 3, 7}, 4-byte groups 0..13 -> {5}) |
| `ValuesWire` | Seeds -> SeedsQuick (the edge values of each family: see the comment of SeedsQuick), Next -> NextQuick (short strings 256 x 256 -> 12 x 9 bytes, Alpha strings of up to 4 -> 3 bytes, proof lengths 18 -> 7, GH payload length low byte 256 -> 11, proof cuts past the header 65 -> 3) |
| `Varint` | SmallMax 16500 -> 130; mode 1 strings over the class alphabet 0..4 -> 0..3 bytes, mode 2 strings over all bytes 0..2 -> 0..1 bytes, mode 3 runs of mixed -> of one continuation byte (Next <- NextQuick); the class alphabet 9 -> 6 bytes (Alpha <- AlphaQuick); boundary values for every j in 0..64 -> for j next to a length change (Seeds <- SeedsQuick) |
| `VerifiedRanges` | capacity N 3 -> 2, offsets MaxOff 7 -> 5 (three runs still overflow N) |
| `VerifiedRanges_n1` | offsets MaxOff 7 -> 3 (two runs still overflow N = 1) |
| `VerifierBytes` | Seeds -> SeedsQuick (small values up to one group + 1 byte, not three; 1 KiB groups only), CfgsOf -> CfgsOfQuick (a real or GiB seed: one genuine stream of g + 1 bytes, groups 0..2, no tampered item) |
