------------------------- MODULE TraceConnectCarrier -------------------------
(***************************************************************************)
(* Trace validation of the protected carrier: pinc-connect                 *)
(* carrier/session.rs.                                                     *)
(*                                                                         *)
(* The Rust test tests/trace_connect_carrier.rs runs a real dialer and a   *)
(* real listener over two byte streams: the handshake and records with    *)
(* reads, transmits, polls and seals of random sizes in random order, and *)
(* attacked runs (junk lengths, garbage, the first message repeated until  *)
(* the handshake output is full, records dropped, replayed, reordered,     *)
(* with a flipped bit, reflected or cut at the end, a key answer on an     *)
(* open carrier, seals before the handshake and after the end). Each run  *)
(* starts with the stream each end received, split into units by their     *)
(* lengths (the offset, the length, and for a unit whose bytes are the     *)
(* k-th record the other end sealed, k and whether its plaintext decodes). *)
(* Every call must be the step the operators of ConnectCarrierOps.tla      *)
(* compute from that table: the answer, the bytes taken by a read, the     *)
(* bytes handed out by a transmit, the unit length of a seal, and the      *)
(* state the public API shows after it (free(), pending_transmit(),        *)
(* key_request()). A record opens at packet number pn exactly when its     *)
(* bytes are the record the other end sealed as its pn-th: so the sender's *)
(* numbering and the receiver's are both checked. The handshake machine's *)
(* outcome is an input (it is proved in Handshake*.tla): the test records *)
(* what the step did (more, a key request, established, failed) and how   *)
(* many bytes it queued.                                                   *)
(*                                                                         *)
(* Constants TLC cannot hold (MAX_PACKET_NUMBER, u64::MAX and the          *)
(* ChaCha20-Poly1305 failure limit 2^36) stand at 2^30: no run comes near  *)
(* them. Needs the TLA+ CommunityModules (Json, IOUtils) and the           *)
(* environment variable PINC_TRACE_DIR, the directory that holds           *)
(* connect_carrier.ndjson.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, c, tab, K
vars == <<i, c, tab, K>>
INSTANCE ConnectCarrierOps WITH MaxPn <- 1073741824, Sat <- 1073741824

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_carrier.ndjson")
Ev0 == Trace[i]
Sides == {"d", "a"}
SendName(s) == IF s = "d" THEN 0 ELSE 1
RecvName(s) == 1 - SendName(s)

TabOf(us) == [o \in {us[j][1] : j \in DOMAIN us} |->
                LET j == CHOOSE j \in DOMAIN us : us[j][1] = o IN [h |-> us[j][2], g |-> us[j][3], f |-> us[j][4]]]
Hdr(o) == tab[Ev0.side][o].h
Opens(o, pn) == tab[Ev0.side][o].g = pn
Fok(o) == tab[Ev0.side][o].f

(* the handshake step the test saw: what it queued and how it ended *)
Sends(g) == IF g = 0 THEN <<>> ELSE <<[o |-> "send", m |-> g - 2]>>
HsOf(s, res, g) ==
    [herr |-> res = "Handshake",
     outs |-> IF res = "open" THEN Sends(g) \o <<[o |-> "est", kok |-> TRUE]>>
              ELSE IF res = "OutputFull" THEN Sends(g) \o <<[o |-> "send", m |-> K.outn]>>
              ELSE Sends(g),
     kreq |-> res = "kreq", sb |-> SendName(s), rb |-> RecvName(s)]

(* the state the public API shows *)
Shows(x) == /\ Free(K, x) = Ev0.free /\ x.out = Ev0.pend /\ (x.st = "hs" /\ x.kr) = Ev0.kr
Set(x) == c' = [c EXCEPT ![Ev0.side] = x]
Me == c[Ev0.side]

StreamEv == /\ Ev0.op = "stream" /\ tab' = [tab EXCEPT ![Ev0.side] = TabOf(Ev0.units)] /\ UNCHANGED <<c, K>>
InitEv == /\ Ev0.op = "init"
          /\ K' = [inl |-> Ev0.k.inl, maxm |-> Ev0.k.maxm, maxu |-> Ev0.k.maxu, tag |-> Ev0.k.tag,
                   outn |-> Ev0.k.outn, maxf |-> Ev0.k.maxf, aead |-> "aes", aesLim |-> 4194304,
                   chachaLim |-> 1073741824]
          /\ LET x == IF Ev0.kind = "dial"
                      THEN Dial(K', [herr |-> FALSE, outs |-> Sends(Ev0.pend), kreq |-> Ev0.kr, sb |-> 0, rb |-> 1]).c
                      ELSE C0("hs")
             IN /\ Set(x) /\ Free(K', x) = Ev0.free /\ x.out = Ev0.pend /\ (x.st = "hs" /\ x.kr) = Ev0.kr
          /\ UNCHANGED tab
RecvEv == LET x == Receive(K, Me, Ev0.len) IN
          /\ Ev0.op = "recv" /\ Ev0.off = Me.wr /\ x.took = Ev0.took /\ Set(x.c) /\ Shows(x.c)
          /\ UNCHANGED <<tab, K>>
PollEv == LET x == Poll(K, Me, Hdr, Opens, Fok, HsOf(Ev0.side, Ev0.res, Ev0.grow)) IN
          /\ Ev0.op = "poll" /\ x.r = Ev0.res /\ Set(x.c) /\ Shows(x.c) /\ UNCHANGED <<tab, K>>
AnsEv == LET x == AnswerSoft(K, Me, HsOf(Ev0.side, Ev0.res, Ev0.grow)) IN
         /\ Ev0.op = "ans" /\ x.r = Ev0.res /\ Set(x.c) /\ Shows(x.c) /\ UNCHANGED <<tab, K>>
TxEv == LET x == Transmit(Me, Ev0.cap) IN
        /\ Ev0.op = "tx" /\ x.n = Ev0.n /\ Set(x.c) /\ Shows(x.c) /\ UNCHANGED <<tab, K>>
SealEv == LET x == IF Ev0.how = "frame" THEN SealFrame(K, Me, Ev0.plen, Ev0.cap, Ev0.fe)
                   ELSE SealBytes(K, Me, Ev0.plen, Ev0.cap) IN
          /\ Ev0.op = "seal" /\ x.r = Ev0.res /\ x.n = Ev0.n /\ Set(x.c) /\ Shows(x.c) /\ UNCHANGED <<tab, K>>

Init == /\ i = 1 /\ c = [s \in Sides |-> C0("hs")] /\ tab = [s \in Sides |-> <<>>]
        /\ K = [inl |-> 0, maxm |-> 0, maxu |-> 0, tag |-> 0, outn |-> 0, maxf |-> 0, aead |-> "aes", aesLim |-> 0,
                chachaLim |-> 0]
Step == /\ i <= Len(Trace) /\ Ev0.t = "cca"
        /\ (StreamEv \/ InitEv \/ RecvEv \/ PollEv \/ AnsEv \/ TxEv \/ SealEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == \A s \in Sides : c[s].out <= K.outn /\ c[s].wr - c[s].rd <= K.inl
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
