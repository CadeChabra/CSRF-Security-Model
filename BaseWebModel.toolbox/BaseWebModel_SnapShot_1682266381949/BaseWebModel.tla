---------------------------- MODULE BaseWebModel ----------------------------

EXTENDS Integers, TLC, Sequences

CONSTANT HonestSessionId

(* --algorithm BaseWebModel
variables 
    MessageLog = {};
    HonestBrowser = [source |-> "honest", Cookies |-> {}, Headers |-> {}];
    HonestServerState = [SessionIds |-> {}, Tokens |-> {}];
    AttackerServerState = [SessionIds |-> {}, Tokens |-> {}];
    AttackerState = [SessionIds |-> {}];
    AttackerBrowser = [source |-> "attacker", Cookies |-> {}, Headers |-> {}]
    
define
    
    HonestAccepted == 
        \A msg \in MessageLog: 
            msg.request.source = "honest" => msg.response.status = "success"
    MaliciousRejected == 
        \A msg \in MessageLog: 
            msg.request.source = "attacker" => msg.response.status = "error"
    

    HasValidSessionId(req, srv) == \E SessionId \in srv.SessionIds: \E cookie \in req.cookies: SessionId = cookie
\*    HasValidToken(req, srv) == \E Token \in srv.Tokens: \E Header \in req.headers: Token = Header
\*    HasValidToken(req, srv) == (srv.Tokens = {HonestKey}) = (req.cookies = {HonestSessionId})
    ServerRequest(src) == [source |-> src.source, cookies |-> src.Cookies, headers |-> src.Headers]
    Response(req, srv) == IF HasValidSessionId(req, srv) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]
    
end define;


procedure LogMessagePair(req, resp) begin
    Log:
    MessageLog := MessageLog \union {[request |-> req, response |-> resp]};
    print << MessageLog >>;
    return;
end procedure;

process SiteRequest = 1
begin
    SSR:
    print <<"Same Site Req">>;
   
    Session:
    HonestBrowser.Cookies := {HonestSessionId};
    HonestServerState.SessionIds := HonestBrowser.Cookies;
    
    call LogMessagePair(ServerRequest(HonestBrowser), Response(ServerRequest(HonestBrowser), HonestServerState));

end process;

process CrossSiteRequest = 2
begin
    CSR:
    print <<"Cross Site Req">>;
    
    HonestToAttacker:
    HonestBrowser.Cookies := {HonestSessionId};
    AttackerState.SessionIds := HonestBrowser.Cookies;
    AttackerBrowser.Cookies := AttackerState.SessionIds;
    
    call LogMessagePair(ServerRequest(AttackerBrowser), Response(ServerRequest(AttackerBrowser), HonestServerState));
    
end process;
        
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "af4e851f" /\ chksum(tla) = "204fe7a8")
CONSTANT defaultInitValue
VARIABLES MessageLog, HonestBrowser, HonestServerState, AttackerServerState, 
          AttackerState, AttackerBrowser, pc, stack

(* define statement *)
HonestAccepted ==
    \A msg \in MessageLog:
        msg.request.source = "honest" => msg.response.status = "success"
MaliciousRejected ==
    \A msg \in MessageLog:
        msg.request.source = "attacker" => msg.response.status = "error"


HasValidSessionId(req, srv) == \E SessionId \in srv.SessionIds: \E cookie \in req.cookies: SessionId = cookie


ServerRequest(src) == [source |-> src.source, cookies |-> src.Cookies, headers |-> src.Headers]
Response(req, srv) == IF HasValidSessionId(req, srv) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]

VARIABLES req, resp

vars == << MessageLog, HonestBrowser, HonestServerState, AttackerServerState, 
           AttackerState, AttackerBrowser, pc, stack, req, resp >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ MessageLog = {}
        /\ HonestBrowser = [source |-> "honest", Cookies |-> {}, Headers |-> {}]
        /\ HonestServerState = [SessionIds |-> {}, Tokens |-> {}]
        /\ AttackerServerState = [SessionIds |-> {}, Tokens |-> {}]
        /\ AttackerState = [SessionIds |-> {}]
        /\ AttackerBrowser = [source |-> "attacker", Cookies |-> {}, Headers |-> {}]
        (* Procedure LogMessagePair *)
        /\ req = [ self \in ProcSet |-> defaultInitValue]
        /\ resp = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "SSR"
                                        [] self = 2 -> "CSR"]

Log(self) == /\ pc[self] = "Log"
             /\ MessageLog' = (MessageLog \union {[request |-> req[self], response |-> resp[self]]})
             /\ PrintT(<< MessageLog' >>)
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ req' = [req EXCEPT ![self] = Head(stack[self]).req]
             /\ resp' = [resp EXCEPT ![self] = Head(stack[self]).resp]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << HonestBrowser, HonestServerState, 
                             AttackerServerState, AttackerState, 
                             AttackerBrowser >>

LogMessagePair(self) == Log(self)

SSR == /\ pc[1] = "SSR"
       /\ PrintT(<<"Same Site Req">>)
       /\ pc' = [pc EXCEPT ![1] = "Session"]
       /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                       AttackerServerState, AttackerState, AttackerBrowser, 
                       stack, req, resp >>

Session == /\ pc[1] = "Session"
           /\ HonestBrowser' = [HonestBrowser EXCEPT !.Cookies = {HonestSessionId}]
           /\ HonestServerState' = [HonestServerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
           /\ /\ req' = [req EXCEPT ![1] = ServerRequest(HonestBrowser')]
              /\ resp' = [resp EXCEPT ![1] = Response(ServerRequest(HonestBrowser'), HonestServerState')]
              /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "LogMessagePair",
                                                    pc        |->  "Done",
                                                    req       |->  req[1],
                                                    resp      |->  resp[1] ] >>
                                                \o stack[1]]
           /\ pc' = [pc EXCEPT ![1] = "Log"]
           /\ UNCHANGED << MessageLog, AttackerServerState, AttackerState, 
                           AttackerBrowser >>

SiteRequest == SSR \/ Session

CSR == /\ pc[2] = "CSR"
       /\ PrintT(<<"Cross Site Req">>)
       /\ pc' = [pc EXCEPT ![2] = "HonestToAttacker"]
       /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                       AttackerServerState, AttackerState, AttackerBrowser, 
                       stack, req, resp >>

HonestToAttacker == /\ pc[2] = "HonestToAttacker"
                    /\ HonestBrowser' = [HonestBrowser EXCEPT !.Cookies = {HonestSessionId}]
                    /\ AttackerState' = [AttackerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
                    /\ AttackerBrowser' = [AttackerBrowser EXCEPT !.Cookies = AttackerState'.SessionIds]
                    /\ /\ req' = [req EXCEPT ![2] = ServerRequest(AttackerBrowser')]
                       /\ resp' = [resp EXCEPT ![2] = Response(ServerRequest(AttackerBrowser'), HonestServerState)]
                       /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "LogMessagePair",
                                                             pc        |->  "Done",
                                                             req       |->  req[2],
                                                             resp      |->  resp[2] ] >>
                                                         \o stack[2]]
                    /\ pc' = [pc EXCEPT ![2] = "Log"]
                    /\ UNCHANGED << MessageLog, HonestServerState, 
                                    AttackerServerState >>

CrossSiteRequest == CSR \/ HonestToAttacker

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SiteRequest \/ CrossSiteRequest
           \/ (\E self \in ProcSet: LogMessagePair(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Apr 23 12:12:52 EDT 2023 by Cade Chabra
\* Created Sun Apr 23 11:29:07 EDT 2023 by Cade Chabra
