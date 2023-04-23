-------------------------- MODULE STPWebModel --------------------------

EXTENDS Integers, TLC, Sequences

CONSTANT HonestKey, AtkKey, HonestSessionId

(* --algorithm STPWebModel
variables 
    MessageLog = {};
    HonestBrowser = [source |-> "honest", Cookies |-> {}, Headers |-> {}];
    HonestServerState = [SessionIds |-> {}, Tokens |-> {}];
    AttackerServerState = [SessionIds |-> {}, Tokens |-> {}];
    HonestSecretKey = [secret |-> {HonestKey}];
    AttackerSecretKey = [secret |-> {AtkKey}];
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
    HasValidToken(req, srv) == (srv.Tokens = {HonestKey}) = (req.cookies = {HonestSessionId})
    ServerRequest(src) == [source |-> src.source, cookies |-> src.Cookies, headers |-> src.Headers]
    Response(req, srv) == IF (HasValidToken(req, srv)) = (HasValidSessionId(req, srv)) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]
    
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
    
    Tokens:
    HonestServerState.Tokens := HonestSecretKey.secret;
    HonestBrowser.Headers := HonestServerState.Tokens;
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
    
    Session:
    AttackerServerState.SessionIds := AttackerBrowser.Cookies;
    
    Tokens:
    AttackerServerState.Tokens := AttackerSecretKey.secret;
    AttackerBrowser.Headers := AttackerServerState.Tokens;
    call LogMessagePair(ServerRequest(AttackerBrowser), Response(ServerRequest(AttackerBrowser), AttackerServerState));
    
end process;
        
end algorithm; *)

\* ====
\* BEGIN TRANSLATION (chksum(pcal) = "5b2a3e13" /\ chksum(tla) = "2ee49425")
\* Label Session of process SiteRequest at line 50 col 5 changed to Session_
\* Label Tokens of process SiteRequest at line 54 col 5 changed to Tokens_
CONSTANT defaultInitValue
VARIABLES MessageLog, HonestBrowser, HonestServerState, AttackerServerState, 
          HonestSecretKey, AttackerSecretKey, AttackerState, AttackerBrowser, 
          pc, stack

(* define statement *)
HonestAccepted ==
    \A msg \in MessageLog:
        msg.request.source = "honest" => msg.response.status = "success"
MaliciousRejected ==
    \A msg \in MessageLog:
        msg.request.source = "attacker" => msg.response.status = "error"


HasValidSessionId(req, srv) == \E SessionId \in srv.SessionIds: \E cookie \in req.cookies: SessionId = cookie

HasValidToken(req, srv) == (srv.Tokens = {HonestKey}) = (req.cookies = {HonestSessionId})
ServerRequest(src) == [source |-> src.source, cookies |-> src.Cookies, headers |-> src.Headers]
Response(req, srv) == IF (HasValidToken(req, srv)) = (HasValidSessionId(req, srv)) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]

VARIABLES req, resp

vars == << MessageLog, HonestBrowser, HonestServerState, AttackerServerState, 
           HonestSecretKey, AttackerSecretKey, AttackerState, AttackerBrowser, 
           pc, stack, req, resp >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ MessageLog = {}
        /\ HonestBrowser = [source |-> "honest", Cookies |-> {}, Headers |-> {}]
        /\ HonestServerState = [SessionIds |-> {}, Tokens |-> {}]
        /\ AttackerServerState = [SessionIds |-> {}, Tokens |-> {}]
        /\ HonestSecretKey = [secret |-> {HonestKey}]
        /\ AttackerSecretKey = [secret |-> {AtkKey}]
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
                             AttackerServerState, HonestSecretKey, 
                             AttackerSecretKey, AttackerState, AttackerBrowser >>

LogMessagePair(self) == Log(self)

SSR == /\ pc[1] = "SSR"
       /\ PrintT(<<"Same Site Req">>)
       /\ pc' = [pc EXCEPT ![1] = "Session_"]
       /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                       AttackerServerState, HonestSecretKey, AttackerSecretKey, 
                       AttackerState, AttackerBrowser, stack, req, resp >>

Session_ == /\ pc[1] = "Session_"
            /\ HonestBrowser' = [HonestBrowser EXCEPT !.Cookies = {HonestSessionId}]
            /\ HonestServerState' = [HonestServerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
            /\ pc' = [pc EXCEPT ![1] = "Tokens_"]
            /\ UNCHANGED << MessageLog, AttackerServerState, HonestSecretKey, 
                            AttackerSecretKey, AttackerState, AttackerBrowser, 
                            stack, req, resp >>

Tokens_ == /\ pc[1] = "Tokens_"
           /\ HonestServerState' = [HonestServerState EXCEPT !.Tokens = HonestSecretKey.secret]
           /\ HonestBrowser' = [HonestBrowser EXCEPT !.Headers = HonestServerState'.Tokens]
           /\ /\ req' = [req EXCEPT ![1] = ServerRequest(HonestBrowser')]
              /\ resp' = [resp EXCEPT ![1] = Response(ServerRequest(HonestBrowser'), HonestServerState')]
              /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "LogMessagePair",
                                                    pc        |->  "Done",
                                                    req       |->  req[1],
                                                    resp      |->  resp[1] ] >>
                                                \o stack[1]]
           /\ pc' = [pc EXCEPT ![1] = "Log"]
           /\ UNCHANGED << MessageLog, AttackerServerState, HonestSecretKey, 
                           AttackerSecretKey, AttackerState, AttackerBrowser >>

SiteRequest == SSR \/ Session_ \/ Tokens_

CSR == /\ pc[2] = "CSR"
       /\ PrintT(<<"Cross Site Req">>)
       /\ pc' = [pc EXCEPT ![2] = "HonestToAttacker"]
       /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                       AttackerServerState, HonestSecretKey, AttackerSecretKey, 
                       AttackerState, AttackerBrowser, stack, req, resp >>

HonestToAttacker == /\ pc[2] = "HonestToAttacker"
                    /\ HonestBrowser' = [HonestBrowser EXCEPT !.Cookies = {HonestSessionId}]
                    /\ AttackerState' = [AttackerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
                    /\ AttackerBrowser' = [AttackerBrowser EXCEPT !.Cookies = AttackerState'.SessionIds]
                    /\ pc' = [pc EXCEPT ![2] = "Session"]
                    /\ UNCHANGED << MessageLog, HonestServerState, 
                                    AttackerServerState, HonestSecretKey, 
                                    AttackerSecretKey, stack, req, resp >>

Session == /\ pc[2] = "Session"
           /\ AttackerServerState' = [AttackerServerState EXCEPT !.SessionIds = AttackerBrowser.Cookies]
           /\ pc' = [pc EXCEPT ![2] = "Tokens"]
           /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                           HonestSecretKey, AttackerSecretKey, AttackerState, 
                           AttackerBrowser, stack, req, resp >>

Tokens == /\ pc[2] = "Tokens"
          /\ AttackerServerState' = [AttackerServerState EXCEPT !.Tokens = AttackerSecretKey.secret]
          /\ AttackerBrowser' = [AttackerBrowser EXCEPT !.Headers = AttackerServerState'.Tokens]
          /\ /\ req' = [req EXCEPT ![2] = ServerRequest(AttackerBrowser')]
             /\ resp' = [resp EXCEPT ![2] = Response(ServerRequest(AttackerBrowser'), AttackerServerState')]
             /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "LogMessagePair",
                                                   pc        |->  "Done",
                                                   req       |->  req[2],
                                                   resp      |->  resp[2] ] >>
                                               \o stack[2]]
          /\ pc' = [pc EXCEPT ![2] = "Log"]
          /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                          HonestSecretKey, AttackerSecretKey, AttackerState >>

CrossSiteRequest == CSR \/ HonestToAttacker \/ Session \/ Tokens

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
\* Last modified Fri Apr 21 15:54:26 EDT 2023 by Cade Chabra
\* Last modified Fri Apr 21 11:11:49 EDT 2023 by andyking
\* Created Sat Mar 25 15:05:39 EDT 2023 by andyking
