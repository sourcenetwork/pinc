----------------------------- MODULE PortMapUpnp -----------------------------
(***************************************************************************)
(* The parsers of the UPnP leg: pinc-portmap upnp.rs.                      *)
(*                                                                         *)
(* The code, step for step on byte sequences, over the helpers of text.rs  *)
(* (PortMapText.tla) and the host rule of addr.rs (PortMapAddr.tla):       *)
(* `Url::new`, `parse_location`, `http_response`, `ssdp_location`,         *)
(* `control_of` with its `resolve`, `soap_result`, `external_ip` and       *)
(* `is_ssdp_answer`. A URL is [ip (4 octets), port, path]. TLC stops on an *)
(* index outside a sequence, so a finished check shows that no parse reads *)
(* outside its input on the domain (the code reaches its bytes only        *)
(* through `get`, `find`, `split_at` at a found position and slice         *)
(* patterns, so it cannot panic on any input; this model checks that the   *)
(* positions it computes stay inside).                                     *)
(*                                                                         *)
(* What the documentation of upnp.rs claims, stated apart from the code:   *)
(*  - LocationForm: a location that parses is a usable host (never         *)
(*    loopback, unspecified, multicast, broadcast or link-local), a port   *)
(*    of 1 to 65535 and a path of 1 to MAX_PATH (128) printable bytes that *)
(*    starts with a slash; LocationTrip: the form http://a.b.c.d:port/path *)
(*    reads back as its URL.                                               *)
(*  - HttpForm: an HTTP response that parses has the status line           *)
(*    HTTP/1.<digit> <3 digits> (then nothing or a space), a status of at  *)
(*    most 999, and a body that is the bytes after the head's blank line,  *)
(*    cut at Content-Length when that is shorter: a piece of the input.    *)
(*  - SsdpForm: a search answer that names a description is a 200 whose    *)
(*    LOCATION header is a location of LocationForm.                       *)
(*  - ControlTrust: a control URL taken from a description is on the       *)
(*    description's own host (an answer names where to send HTTP only      *)
(*    once), of the path form of LocationForm, for one of SERVICES.        *)
(*  - SoapForm: a SOAP success is a 200 and a fault a 500 that carries an  *)
(*    <errorCode> of digits.                                               *)
(* Not modelled: the request builders `get` and `soap`, straight-line uses *)
(* of the bounded writer (PortMapText.tla: never past the buffer, an       *)
(* overflow reported), whose literals the trace test checks byte for byte. *)
(*                                                                         *)
(* Checked over (about 3700 states): locations from every scheme prefix    *)
(* (http://, HTTP://, http:/, https://), 13 hosts (8 addresses of every    *)
(* class, 5 malformed), 7 port forms (none, empty, 0, 80, 65535, 65536, a  *)
(* letter) and 4 paths (none, /, /d, one with a space), each with and      *)
(* without surrounding spaces, and the paths of 128 and 129 bytes;         *)
(* responses from 9 status lines, 6 header lines (Content-Length shorter,  *)
(* longer, not a number; two LOCATION forms), with and without the blank   *)
(* line and 5 bodies (none, text, an errorCode, two external addresses);   *)
(* descriptions of one service of every type with 6 control forms (a path, *)
(* a relative path, an http URL on the description's host and on another, *)
(* none, a namespaced tag), and of two services whose first does not      *)
(* map ports; 36 URLs written in the one form.                             *)
(*                                                                         *)
(* PortMapUpnp_foreign.cfg is a witness: a description whose control URL   *)
(* names another host is in the domain and is refused (NoForeignRefused).  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLE c

T == INSTANCE PortMapText WITH c <- 0
A == INSTANCE PortMapAddr WITH c <- 0

(* ---- bytes ---- *)
CRLF == <<13, 10>>
CRLF2 == <<13, 10, 13, 10>>
Http == <<104, 116, 116, 112, 58, 47, 47>>                      \* http://
HttpSlash == <<72, 84, 84, 80, 47, 49, 46>>                     \* HTTP/1.
Http11 == <<72, 84, 84, 80, 47, 49, 46, 49, 32>>                \* "HTTP/1.1 "
S200 == <<50, 48, 48>>
\* urn:schemas-upnp-org:service:
Urn == <<117, 114, 110, 58, 115, 99, 104, 101, 109, 97, 115, 45, 117, 112, 110, 112, 45, 111, 114, 103, 58, 115,
         101, 114, 118, 105, 99, 101, 58>>
WanIp == <<87, 65, 78, 73, 80, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110>>          \* WANIPConnection
WanPpp == <<87, 65, 78, 80, 80, 80, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110>>     \* WANPPPConnection
\* upnp::SERVICES, index k is Services[k + 1]
Services == <<Urn \o WanIp \o <<58, 50>>, Urn \o WanIp \o <<58, 49>>, Urn \o WanPpp \o <<58, 49>>>>
ServiceType == <<115, 101, 114, 118, 105, 99, 101, 84, 121, 112, 101>>                    \* serviceType
ControlURL == <<99, 111, 110, 116, 114, 111, 108, 85, 82, 76>>                            \* controlURL
ErrorCode == <<101, 114, 114, 111, 114, 67, 111, 100, 101>>                               \* errorCode
\* NewExternalIPAddress
NewExtIp == <<78, 101, 119, 69, 120, 116, 101, 114, 110, 97, 108, 73, 80, 65, 100, 100, 114, 101, 115, 115>>
ServiceTypeOpen == <<60>> \o ServiceType \o <<62>>
ServiceClose == <<60, 47, 115, 101, 114, 118, 105, 99, 101, 62>>                          \* </service>
ContentLength == <<99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104>>  \* content-length
Location == <<108, 111, 99, 97, 116, 105, 111, 110>>                                      \* location
MaxPath == 128

(* ---- the code ---- *)
NoUrl == [ok |-> FALSE, u |-> [ip |-> <<0, 0, 0, 0>>, port |-> 0, path |-> <<>>]]
Graphic(x) == x >= 33 /\ x <= 126
\* Url::new
UrlNew(ip, port, path) ==
    IF Len(path) = 0 \/ Len(path) > MaxPath \/ ~\A k \in 1..Len(path) : Graphic(path[k]) THEN NoUrl
    ELSE [ok |-> TRUE, u |-> [ip |-> ip, port |-> port, path |-> path]]

\* upnp::parse_location
ParseLocation(b) ==
    LET r0 == T!Trim(b)
    IN IF Len(r0) < 7 \/ ~T!EqIC(SubSeq(r0, 1, 7), Http) THEN NoUrl
       ELSE LET rest == SubSeq(r0, 8, Len(r0))
                sl == {k \in 0..(Len(rest) - 1) : rest[k + 1] = 47}
                slash == IF sl = {} THEN Len(rest) ELSE T!MinOf(sl)
                hostport == T!Slice(rest, 0, slash)
                path == T!Slice(rest, slash, Len(rest))
                cs == {k \in 0..(Len(hostport) - 1) : hostport[k + 1] = 58}
                host == IF cs = {} THEN hostport ELSE T!Slice(hostport, 0, T!MinOf(cs))
                pr == IF cs = {} THEN [ok |-> TRUE, v |-> T!W32(80)]
                      ELSE T!ParseU32(T!Slice(hostport, T!MinOf(cs) + 1, Len(hostport)))
                ip == T!ParseIp4(host)
            IN IF ~pr.ok \/ pr.v.hi # 0 \/ pr.v.lo = 0 THEN NoUrl
               ELSE IF ~ip.ok \/ ~A!UsableHost(ip.o) THEN NoUrl
               ELSE UrlNew(ip.o, pr.v.lo, IF Len(path) = 0 THEN <<47>> ELSE path)

\* upnp::http_response: [ok, status, body, from] (from: the 0-based offset of the body in the input)
NoResp == [ok |-> FALSE, status |-> 0, body |-> <<>>, from |-> 0]
HttpResponse(b) ==
    LET le == T!Find(b, CRLF)
    IN IF le < 0 THEN NoResp
       ELSE LET line == T!Slice(b, 0, le)
            IN IF Len(line) < 7 \/ T!Slice(line, 0, 7) # HttpSlash THEN NoResp
               ELSE LET rest == T!Slice(line, 7, Len(line))
                    IN IF Len(rest) < 5 \/ rest[2] # 32 \/ ~T!IsDigit(rest[1]) THEN NoResp
                       ELSE IF Len(rest) > 5 /\ rest[6] # 32 THEN NoResp
                       ELSE LET st == T!ParseU32(<<rest[3], rest[4], rest[5]>>)
                                he == T!Find(b, CRLF2)
                            IN IF ~st.ok \/ he < 0 THEN NoResp
                               ELSE LET head == T!Slice(b, 0, he)
                                        all == T!Slice(b, he + 4, Len(b))
                                        h == T!Header(head, ContentLength)
                                        n == T!ParseU32(h.v)
                                        body == IF h.ok /\ n.ok /\ n.v.hi = 0 /\ n.v.lo < Len(all)
                                                THEN SubSeq(all, 1, n.v.lo) ELSE all
                                    IN [ok |-> TRUE, status |-> st.v.lo, body |-> body, from |-> he + 4]

\* upnp::ssdp_location
SsdpLocation(b) ==
    LET le == T!Find(b, CRLF)
    IN IF le < 0 THEN NoUrl
       ELSE LET line == T!Slice(b, 0, le)
            IN IF Len(line) < 12 \/ ~T!EqIC(T!Slice(line, 0, 9), Http11) \/ T!Slice(line, 9, 12) # S200 THEN NoUrl
               ELSE LET f == T!Find(b, CRLF2)
                        he == IF f < 0 THEN Len(b) ELSE f
                        h == T!Header(T!Slice(b, 0, he), Location)
                    IN IF ~h.ok THEN NoUrl ELSE ParseLocation(h.v)

\* resolve(ctl, base)
Resolve(ctl, base) ==
    IF Len(ctl) >= 7 /\ T!EqIC(SubSeq(ctl, 1, 7), Http)
    THEN LET u == ParseLocation(ctl) IN IF u.ok /\ u.u.ip = base.ip THEN u ELSE NoUrl
    ELSE IF Len(ctl) > 0 /\ ctl[1] = 47 THEN UrlNew(base.ip, base.port, ctl)
    ELSE LET w == T!Put(T!Put(T!NewOut(MaxPath, 0), <<47>>), ctl)
         IN IF T!Done(w) < 0 THEN NoUrl ELSE UrlNew(base.ip, base.port, T!Written(w))

\* upnp::control_of: [ok, u, k]
NoCtl == [ok |-> FALSE, u |-> NoUrl.u, k |-> 0]
RECURSIVE CtlFrom(_, _, _)
CtlFrom(desc, base, at) ==
    LET off == T!Find(T!Slice(desc, at, Len(desc)), ServiceTypeOpen)
    IN IF off < 0 THEN NoCtl
       ELSE LET el == T!Element(desc, at + off, ServiceType)
            IN IF ~el.ok THEN NoCtl
               ELSE LET next == el.next
                        e == T!Find(T!Slice(desc, next, Len(desc)), ServiceClose)
                        end == IF e < 0 THEN Len(desc) ELSE next + e
                        ks == {k \in 0..2 : Services[k + 1] = el.text}
                        ctl == T!Element(T!Slice(desc, 0, end), next, ControlURL)
                    IN IF ks # {} /\ ctl.ok
                       THEN LET r == Resolve(ctl.text, base)
                            IN IF r.ok THEN [ok |-> TRUE, u |-> r.u, k |-> T!MinOf(ks)] ELSE NoCtl
                       ELSE CtlFrom(desc, base, next)
ControlOf(desc, base) == CtlFrom(desc, base, 0)

\* upnp::soap_result: [k ("none", "ok", "fault"), body, code (a u32 record)]
SoapResult(resp) ==
    LET r == HttpResponse(resp)
        el == T!Element(r.body, 0, ErrorCode)
        p == T!ParseU32(el.text)
    IN IF r.ok /\ r.status = 200 THEN [k |-> "ok", body |-> r.body, code |-> T!W32(0)]
       ELSE IF r.ok /\ r.status = 500 /\ el.ok /\ p.ok THEN [k |-> "fault", body |-> <<>>, code |-> p.v]
       ELSE [k |-> "none", body |-> <<>>, code |-> T!W32(0)]

\* upnp::external_ip: [ok, o]
ExternalIp(body) ==
    LET el == T!Element(body, 0, NewExtIp) IN IF el.ok THEN T!ParseIp4(el.text) ELSE T!NoneIp

\* upnp::is_ssdp_answer
IsSsdpAnswer(port, b) == port = 1900 /\ Len(b) >= 7 /\ T!EqIC(SubSeq(b, 1, 7), HttpSlash)

(* ---- the specification ---- *)
PathForm(p) == Len(p) \in 1..MaxPath /\ p[1] = 47 /\ \A k \in 1..Len(p) : Graphic(p[k])
LocationForm(b) ==
    LET r == ParseLocation(b)
    IN r.ok => (A!UsableHost(r.u.ip) /\ r.u.port \in 1..65535 /\ PathForm(r.u.path))
Render(u) == Http \o T!Ip4Bytes(u.ip) \o <<58>> \o T!DecBytes(T!W32(u.port)) \o u.path
LocationTrip(u) == ParseLocation(Render(u)) = [ok |-> TRUE, u |-> u]

HttpForm(b) ==
    LET r == HttpResponse(b)
    IN r.ok =>
         /\ Len(b) >= 12 /\ SubSeq(b, 1, 7) = HttpSlash /\ T!IsDigit(b[8]) /\ b[9] = 32
         /\ T!IsDigit(b[10]) /\ T!IsDigit(b[11]) /\ T!IsDigit(b[12]) /\ (b[13] = 32 \/ b[13] = 13)
         /\ r.status \in 0..999
         /\ r.from >= 4 /\ SubSeq(b, r.from - 3, r.from) = CRLF2
         /\ r.from + Len(r.body) <= Len(b) /\ r.body = SubSeq(b, r.from + 1, r.from + Len(r.body))

SsdpForm(b) ==
    LET r == SsdpLocation(b)
    IN r.ok => (T!EqIC(SubSeq(b, 1, 9), Http11) /\ SubSeq(b, 10, 12) = S200 /\ LocationForm(T!Header(b, Location).v))

ControlTrust(desc, base) ==
    LET r == ControlOf(desc, base)
    IN r.ok => (r.u.ip = base.ip /\ PathForm(r.u.path) /\ r.k \in 0..2)

SoapForm(b) ==
    LET r == SoapResult(b)
    IN /\ r.k = "ok" => HttpResponse(b).status = 200
       /\ r.k = "fault" => (HttpResponse(b).status = 500 /\ T!Element(HttpResponse(b).body, 0, ErrorCode).ok)

(* ---- the domain ---- *)
Base == [ip |-> <<192, 168, 1, 1>>, port |-> 5000, path |-> <<47, 100>>]
Pre == {Http, <<72, 84, 84, 80, 58, 47, 47>>, <<104, 116, 116, 112, 58, 47>>, <<104, 116, 116, 112, 115, 58, 47, 47>>}
GoodHosts == {<<192, 168, 1, 1>>, <<10, 0, 0, 1>>, <<127, 0, 0, 1>>, <<0, 0, 0, 0>>, <<169, 254, 1, 1>>,
              <<224, 0, 0, 1>>, <<255, 255, 255, 255>>, <<8, 8, 8, 8>>}
BadHosts == {<<49, 46, 50, 46, 51>>, <<49, 46, 50, 46, 51, 46, 52, 46, 53>>, <<50, 53, 54, 46, 49, 46, 49, 46, 49>>,
             <<49, 46, 50, 46, 51, 46, 52, 97>>, <<>>}
Hosts == {T!Ip4Bytes(o) : o \in GoodHosts} \cup BadHosts
Ports == {<<>>, <<58>>, <<58, 48>>, <<58, 56, 48>>, <<58, 54, 53, 53, 51, 53>>, <<58, 54, 53, 53, 51, 54>>, <<58, 120>>}
Paths == {<<>>, <<47>>, <<47, 100>>, <<47, 97, 32, 98>>}
LongPaths == {<<47>> \o [k \in 1..127 |-> 97], <<47>> \o [k \in 1..128 |-> 97]}
Ws == {<<>>, <<32>>}
Locs == {w \o p \o h \o pt \o pa \o w : w \in Ws, p \in Pre, h \in Hosts, pt \in Ports, pa \in Paths}
        \cup {Http \o T!Ip4Bytes(<<192, 168, 1, 1>>) \o pa : pa \in LongPaths}

Status == {<<72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75>>,      \* HTTP/1.1 200 OK
           <<72, 84, 84, 80, 47, 49, 46, 48, 32, 50, 48, 48>>,                  \* HTTP/1.0 200
           <<72, 84, 84, 80, 47, 49, 46, 49, 32, 53, 48, 48, 32, 69>>,          \* HTTP/1.1 500 E
           <<72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48>>,                      \* HTTP/1.1 20
           <<72, 84, 84, 80, 47, 49, 46, 120, 32, 50, 48, 48>>,                 \* HTTP/1.x 200
           <<72, 84, 84, 80, 47, 50, 32, 50, 48, 48>>,                          \* HTTP/2 200
           <<104, 116, 116, 112, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75>>,  \* http/1.1 200 OK
           <<72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 79, 75>>,          \* HTTP/1.1 200OK
           <<72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 120, 48>>}                 \* HTTP/1.1 2x0
CL == <<67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32>>      \* "Content-Length: "
Heads == {<<>>, CL \o <<50>>, ContentLength \o <<58, 32, 57, 57>>, CL \o <<120>>,
          <<76, 79, 67, 65, 84, 73, 79, 78, 58, 32>> \o Http \o T!Ip4Bytes(<<192, 168, 1, 1>>) \o <<58, 53, 48, 48, 48, 47, 100>>,
          Location \o <<58>> \o Http \o T!Ip4Bytes(<<8, 8, 8, 8>>) \o <<47, 120>>}
ElemOf(name, text) == <<60>> \o name \o <<62>> \o text \o <<60, 47>> \o name \o <<62>>
Bodies == {<<>>, <<97, 98, 99, 100>>, ElemOf(ErrorCode, <<55, 49, 56>>),
           <<60, 117, 58>> \o NewExtIp \o <<62>> \o T!Ip4Bytes(<<1, 2, 3, 4>>) \o <<60, 47, 117, 58>> \o NewExtIp \o <<62>>,
           ElemOf(NewExtIp, T!Ip4Bytes(<<10, 0, 0, 1>>))}
Resp(st, hd, done, body) == st \o CRLF \o (IF hd = <<>> THEN <<>> ELSE hd \o CRLF) \o (IF done THEN CRLF ELSE <<>>) \o body
Resps == {Resp(st, hd, d, bo) : st \in Status, hd \in Heads, d \in BOOLEAN, bo \in Bodies}

Service == <<60, 115, 101, 114, 118, 105, 99, 101, 62>>                                  \* <service>
Block(ty, ctl) == Service \o ElemOf(ServiceType, ty) \o ctl \o ServiceClose
Types == {Services[1], Services[2], Services[3], <<117, 114, 110, 58, 120>>}
Ctls == {ElemOf(ControlURL, <<47, 99, 116, 108>>), ElemOf(ControlURL, <<99, 116, 108>>),
         ElemOf(ControlURL, Http \o T!Ip4Bytes(<<192, 168, 1, 1>>) \o <<58, 53, 48, 48, 48, 47, 99>>),
         ElemOf(ControlURL, Http \o T!Ip4Bytes(<<192, 168, 1, 2>>) \o <<47, 99>>),
         <<>>,
         <<60, 117, 58>> \o ControlURL \o <<32, 62, 47, 110, 60, 47, 117, 58>> \o ControlURL \o <<62>>}
Firsts == {Block(<<117, 114, 110, 58, 120>>, x) : x \in Ctls} \cup {Block(Services[1], <<>>)}
Descs == {Block(ty, x) : ty \in Types, x \in Ctls} \cup {f \o Block(ty, x) : f \in Firsts, ty \in Types, x \in Ctls}

Urls == {[ip |-> ip, port |-> p, path |-> pa] :
            ip \in {<<192, 168, 1, 1>>, <<8, 8, 8, 8>>, <<1, 2, 3, 4>>}, p \in {1, 80, 5000, 65535},
            pa \in {<<47>>, <<47, 100>>, <<47>> \o [k \in 1..127 |-> 97]}}

Init == c = [t |-> "root"]
Cases ==
    {[t |-> "loc", b |-> b] : b \in Locs} \cup {[t |-> "resp", b |-> b] : b \in Resps}
    \cup {[t |-> "desc", b |-> b] : b \in Descs} \cup {[t |-> "url", u |-> u] : u \in Urls}
Next == c.t = "root" /\ \E x \in Cases : c' = x
Spec == Init /\ [][Next]_c

Inv ==
    CASE c.t = "loc" -> LocationForm(c.b) /\ SsdpForm(Http11 \o S200 \o CRLF \o Location \o <<58>> \o c.b \o CRLF2)
      [] c.t = "resp" -> HttpForm(c.b) /\ SsdpForm(c.b) /\ SoapForm(c.b)
                         /\ (ExternalIp(HttpResponse(c.b).body).ok => HttpResponse(c.b).ok)
      [] c.t = "desc" -> ControlTrust(c.b, Base)
      [] c.t = "url" -> LocationTrip(c.u)
      [] OTHER -> TRUE

\* Witness (PortMapUpnp_foreign.cfg, which TLC must violate): no description names a mapping service whose control URL
\* is an http URL on another host that the parser then refuses.
NoForeignRefused ==
    c.t = "desc" => ~(\E ty \in Types, x \in Ctls :
                        /\ c.b = Block(ty, x) /\ ty # <<117, 114, 110, 58, 120>>
                        /\ x = ElemOf(ControlURL, Http \o T!Ip4Bytes(<<192, 168, 1, 2>>) \o <<47, 99>>)
                        /\ ~ControlOf(c.b, Base).ok)
=============================================================================
