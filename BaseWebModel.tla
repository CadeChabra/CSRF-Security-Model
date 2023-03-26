-------------------------- MODULE BaseWebModelTest --------------------------

EXTENDS Integers, TLC, Sequences



(* --algorithm BaseWebModelTest
variables 
    MessageLog = {};
    BrowserState = [cookies |-> {"sessionId1"}];
    ServerState = [SessionIds |-> {"sessionId1"}, Tokens |-> {}];
    
define
    
    HonestAccepted == 
        \A msg \in MessageLog: 
            msg.request.source = "honest" => msg.response.status = "success"
    MaliciousRejected == 
        \A msg \in MessageLog: 
            msg.request.source = "attacker" => msg.response.status = "error"

    HasValidSessionId(req) == \E SessionId \in ServerState.SessionIds: \E cookie \in req.cookies: SessionId = cookie
    Request(src) == [source |-> src, cookies |-> BrowserState.cookies]
    Response(req) == IF HasValidSessionId(req) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]
    
end define;
      

procedure LogMessagePair(req, resp) begin
    Log:
    MessageLog := MessageLog \union {[request |-> req, response |-> resp]};
    print << MessageLog >>;
    return;
end procedure;

process SiteRequest = 1
variables
    reqHon = Request("honest");
    reqAtk = Request("attacker");
begin
    SSR:
    print <<"Same Site Req">>;
    call LogMessagePair(reqHon, Response(reqHon));
    
    CSR:
    print <<"Cross Site Req">>;
    call LogMessagePair(reqAtk, Response(reqAtk));
end process;

\*process CrossSiteRequest = 1
\*variables
\*    req = Request("attacker");
\*begin
\*    CSR:
\*    print <<"Cross Site Req">>;
\*    call LogMessagePair(req, Response(req));
\*end process;
        
end algorithm; *)

\* ====
\* BEGIN TRANSLATION (chksum(pcal) = "5f69c2cb" /\ chksum(tla) = "6b68ddce")
CONSTANT defaultInitValue
VARIABLES MessageLog, BrowserState, ServerState, pc, stack

(* define statement *)
HonestAccepted ==
    \A msg \in MessageLog:
        msg.request.source = "honest" => msg.response.status = "success"
MaliciousRejected ==
    \A msg \in MessageLog:
        msg.request.source = "attacker" => msg.response.status = "error"

HasValidSessionId(req) == \E SessionId \in ServerState.SessionIds: \E cookie \in req.cookies: SessionId = cookie
Request(src) == [source |-> src, cookies |-> BrowserState.cookies]
Response(req) == IF HasValidSessionId(req) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]

VARIABLES req, resp, reqHon, reqAtk

vars == << MessageLog, BrowserState, ServerState, pc, stack, req, resp, 
           reqHon, reqAtk >>

ProcSet == {1}

Init == (* Global variables *)
        /\ MessageLog = {}
        /\ BrowserState = [cookies |-> {"sessionId1"}]
        /\ ServerState = [SessionIds |-> {"sessionId1"}, Tokens |-> {}]
        (* Procedure LogMessagePair *)
        /\ req = [ self \in ProcSet |-> defaultInitValue]
        /\ resp = [ self \in ProcSet |-> defaultInitValue]
        (* Process SiteRequest *)
        /\ reqHon = Request("honest")
        /\ reqAtk = Request("attacker")
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "SSR"]

Log(self) == /\ pc[self] = "Log"
             /\ MessageLog' = (MessageLog \union {[request |-> req[self], response |-> resp[self]]})
             /\ PrintT(<< MessageLog' >>)
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ req' = [req EXCEPT ![self] = Head(stack[self]).req]
             /\ resp' = [resp EXCEPT ![self] = Head(stack[self]).resp]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << BrowserState, ServerState, reqHon, reqAtk >>

LogMessagePair(self) == Log(self)

SSR == /\ pc[1] = "SSR"
       /\ PrintT(<<"Same Site Req">>)
       /\ /\ req' = [req EXCEPT ![1] = reqHon]
          /\ resp' = [resp EXCEPT ![1] = Response(reqHon)]
          /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "LogMessagePair",
                                                pc        |->  "CSR",
                                                req       |->  req[1],
                                                resp      |->  resp[1] ] >>
                                            \o stack[1]]
       /\ pc' = [pc EXCEPT ![1] = "Log"]
       /\ UNCHANGED << MessageLog, BrowserState, ServerState, reqHon, reqAtk >>

CSR == /\ pc[1] = "CSR"
       /\ PrintT(<<"Cross Site Req">>)
       /\ /\ req' = [req EXCEPT ![1] = reqAtk]
          /\ resp' = [resp EXCEPT ![1] = Response(reqAtk)]
          /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "LogMessagePair",
                                                pc        |->  "Done",
                                                req       |->  req[1],
                                                resp      |->  resp[1] ] >>
                                            \o stack[1]]
       /\ pc' = [pc EXCEPT ![1] = "Log"]
       /\ UNCHANGED << MessageLog, BrowserState, ServerState, reqHon, reqAtk >>

SiteRequest == SSR \/ CSR

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SiteRequest
           \/ (\E self \in ProcSet: LogMessagePair(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Mar 26 12:36:44 EDT 2023 by andyking
\* Created Sat Mar 25 15:05:39 EDT 2023 by andyking
