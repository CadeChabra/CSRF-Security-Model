---------------------------- MODULE BaseWebModel ----------------------------
EXTENDS Integers, TLC, Sequences

(* --algorithm WebInteraction
variables 
    MessageLog = {};
    BrowserState = [cookies |-> {"sessionId1"}];
    ServerState = [SessionIds |-> {"sessionId1"}, Tokens |-> {}];
    
define
    
    HonestAccepted == \A msg \in MessageLog: msg.request.source = "honest" => msg.response.status = "success"
    MaliciousRejected == \A msg \in MessageLog: msg.request.source = "attacker" => msg.response.status = "error"

    HasValidSessionId(req) == \E SessionId \in ServerState.SessionIds: \E cookie \in req.cookies: SessionId = cookie
    Request(src) == [source |-> src, cookies |-> BrowserState.cookies]
    Response(req) == IF HasValidSessionId(req) THEN [destination |-> req.source, status |-> "accepted"] ELSE [destination |-> req.source, status |-> "error"]
    
end define;

procedure LogMessagePair(req, resp) begin
    Log:
    MessageLog := MessageLog \union {[request |-> req, response |-> resp]};
    return;
end procedure;

process SameSiteRequest = 1
variables
    req = Request("honest");
begin
    SSR:
    call LogMessagePair(req, Response(req));
end process;

process CrossSiteRequest = 1
variables
    req = Request("attacker");
begin
    CSR:
    call LogMessagePair(req, Response(req));
end process;
        
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "66a74c5d" /\ chksum(tla) = "fc2a9067")
\* Process variable req of process SameSiteRequest at line 29 col 5 changed to req_
\* Process variable req of process CrossSiteRequest at line 37 col 5 changed to req_C
CONSTANT defaultInitValue
VARIABLES MessageLog, BrowserState, ServerState, pc, stack

(* define statement *)
HonestAccepted == \A msg \in MessageLog: msg.request.source = "honest" => msg.response.status = "success"
MaliciousRejected == \A msg \in MessageLog: msg.request.source = "attacker" => msg.response.status = "error"

HasValidSessionId(req) == \E SessionId \in ServerState.SessionIds: \E cookie \in req.cookies: SessionId = cookie
Request(src) == [source |-> src, cookies |-> BrowserState.cookies]
Response(req) == IF HasValidSessionId(req) THEN [destination |-> req.source, status |-> "accepted"] ELSE [destination |-> req.source, status |-> "error"]

VARIABLES req, resp, req_, req_C

vars == << MessageLog, BrowserState, ServerState, pc, stack, req, resp, req_, 
           req_C >>

ProcSet == {1} \cup {1}

Init == (* Global variables *)
        /\ MessageLog = {}
        /\ BrowserState = [cookies |-> {"sessionId1"}]
        /\ ServerState = [SessionIds |-> {"sessionId1"}, Tokens |-> {}]
        (* Procedure LogMessagePair *)
        /\ req = [ self \in ProcSet |-> defaultInitValue]
        /\ resp = [ self \in ProcSet |-> defaultInitValue]
        (* Process SameSiteRequest *)
        /\ req_ = Request("honest")
        (* Process CrossSiteRequest *)
        /\ req_C = Request("attacker")
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "SSR"
                                        [] self = 1 -> "CSR"]

Log(self) == /\ pc[self] = "Log"
             /\ MessageLog' = (MessageLog \union {[request |-> req[self], response |-> resp[self]]})
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ req' = [req EXCEPT ![self] = Head(stack[self]).req]
             /\ resp' = [resp EXCEPT ![self] = Head(stack[self]).resp]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << BrowserState, ServerState, req_, req_C >>

LogMessagePair(self) == Log(self)

SSR == /\ pc[1] = "SSR"
       /\ /\ req' = [req EXCEPT ![1] = req_]
          /\ resp' = [resp EXCEPT ![1] = Response(req_)]
          /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "LogMessagePair",
                                                pc        |->  "Done",
                                                req       |->  req[1],
                                                resp      |->  resp[1] ] >>
                                            \o stack[1]]
       /\ pc' = [pc EXCEPT ![1] = "Log"]
       /\ UNCHANGED << MessageLog, BrowserState, ServerState, req_, req_C >>

SameSiteRequest == SSR

CSR == /\ pc[1] = "CSR"
       /\ /\ req' = [req EXCEPT ![1] = req_C]
          /\ resp' = [resp EXCEPT ![1] = Response(req_C)]
          /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "LogMessagePair",
                                                pc        |->  "Done",
                                                req       |->  req[1],
                                                resp      |->  resp[1] ] >>
                                            \o stack[1]]
       /\ pc' = [pc EXCEPT ![1] = "Log"]
       /\ UNCHANGED << MessageLog, BrowserState, ServerState, req_, req_C >>

CrossSiteRequest == CSR

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SameSiteRequest \/ CrossSiteRequest
           \/ (\E self \in ProcSet: LogMessagePair(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Mar 23 15:06:09 EDT 2023 by Cade Chabra
\* Created Tue Mar 07 16:33:46 EST 2023 by Cade Chabra
