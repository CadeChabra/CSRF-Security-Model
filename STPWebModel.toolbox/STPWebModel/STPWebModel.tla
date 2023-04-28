-------------------------- MODULE STPWebModel --------------------------

EXTENDS Integers, TLC, Sequences

CONSTANT HonestKey, AtkKey, HonestSessionId

\* Web interaction model with STP implemented
(* --algorithm STPWebModel
variables 
    \* Logs all request-response pairs - used to check invariants
    MessageLog = {};
    \* Model of honest client's browser context
    HonestBrowser = [source |-> "honest", Cookies |-> {}, Headers |-> {}];
    \* Model of honest server
    HonestServerState = [SessionIds |-> {}, Tokens |-> {}];
    \* Model of attacker's capabilities
    AttackerServerState = [SessionIds |-> {}, Tokens |-> {}];
    AttackerState = [SessionIds |-> {}];
    AttackerBrowser = [source |-> "attacker", Cookies |-> {}, Headers |-> {}];
    \* Store unique CSRF tokens - assumed to be cryptographically strong and sufficiently difficult to guess
    HonestSecretKey = [secret |-> {HonestKey}];
    AttackerSecretKey = [secret |-> {AtkKey}];
    
define
    
    \* Invariants to be checked on the model
    HonestAccepted == 
        \A msg \in MessageLog: 
            msg.request.source = "honest" => msg.response.status = "success"
    MaliciousRejected == 
        \A msg \in MessageLog: 
            msg.request.source = "attacker" => msg.response.status = "error"
    
    \* Checks that a request (req) to a server (srv) has a valid session ID with that server
    HasValidSessionId(req, srv) == \E SessionId \in srv.SessionIds: \E cookie \in req.cookies: SessionId = cookie
    \* Checks that a requst (req) to a server (srv) has a valid CSRF token - main check of the STP technique
    HasValidToken(req, srv) == (srv.Tokens = {HonestKey}) = (req.cookies = {HonestSessionId})
    \* Generates a request from a source browser (src)
    ServerRequest(src) == [source |-> src.source, cookies |-> src.Cookies, headers |-> src.Headers]
    \* Creates a response based on a request (req) and the destination server (srv) - checks if request has a valid session ID and CSRF token before accepting/rejecting
    Response(req, srv) == IF (HasValidToken(req, srv)) = (HasValidSessionId(req, srv)) THEN [destination |-> req.source, status |-> "success"] ELSE [destination |-> req.source, status |-> "error"]
    
end define;

\* Adds a request-response pair to the message log
procedure LogMessagePair(req, resp) begin
    Log:
    MessageLog := MessageLog \union {[request |-> req, response |-> resp]};
    print << MessageLog >>;
    return;
end procedure;

\* Process for an honest request
process SiteRequest = 1
begin
    SSR:
    print <<"Same Site Req">>;
   
    \* Honest browser and server establish a session ID
    Session:
    HonestBrowser.Cookies := {HonestSessionId};
    HonestServerState.SessionIds := HonestBrowser.Cookies;
    
    \* Honest browser and server establish a CSRF token
    Tokens:
    HonestServerState.Tokens := HonestSecretKey.secret;
    HonestBrowser.Headers := HonestServerState.Tokens;
    \* Generate and log request-response pair based on a request from the honest site
    call LogMessagePair(ServerRequest(HonestBrowser), Response(ServerRequest(HonestBrowser), HonestServerState));

end process;

\* Process for a malicious cross-site request
process CrossSiteRequest = 2
begin
    CSR:
    print <<"Cross Site Req">>;
    
    \* Honest browser and server establish session ID 
    HonestToAttacker:
    HonestBrowser.Cookies := {HonestSessionId};
    HonestServerState.SessionIds := HonestBrowser.Cookies;
    \* Attacker is able to access session ID through the cookie set on the browser
    AttackerState.SessionIds := HonestBrowser.Cookies;
    AttackerBrowser.Cookies := AttackerState.SessionIds;
    
    Session:
    AttackerServerState.SessionIds := AttackerBrowser.Cookies;
    
    \* Attacker sets a CSRF token but does not know the honest user's token 
    Tokens:
    AttackerBrowser.Headers := AttackerSecretKey.secret;
    \* Generate and log request-response pair based on a request from the malicious site
    call LogMessagePair(ServerRequest(AttackerBrowser), Response(ServerRequest(AttackerBrowser), HonestServerState));
    
end process;
        
end algorithm; *)

\* ====
\* BEGIN TRANSLATION (chksum(pcal) = "67397c89" /\ chksum(tla) = "58bba5ed")
\* Label Session of process SiteRequest at line 61 col 5 changed to Session_
\* Label Tokens of process SiteRequest at line 66 col 5 changed to Tokens_
CONSTANT defaultInitValue
VARIABLES MessageLog, HonestBrowser, HonestServerState, AttackerServerState, 
          AttackerState, AttackerBrowser, HonestSecretKey, AttackerSecretKey, 
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
           AttackerState, AttackerBrowser, HonestSecretKey, AttackerSecretKey, 
           pc, stack, req, resp >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ MessageLog = {}
        /\ HonestBrowser = [source |-> "honest", Cookies |-> {}, Headers |-> {}]
        /\ HonestServerState = [SessionIds |-> {}, Tokens |-> {}]
        /\ AttackerServerState = [SessionIds |-> {}, Tokens |-> {}]
        /\ AttackerState = [SessionIds |-> {}]
        /\ AttackerBrowser = [source |-> "attacker", Cookies |-> {}, Headers |-> {}]
        /\ HonestSecretKey = [secret |-> {HonestKey}]
        /\ AttackerSecretKey = [secret |-> {AtkKey}]
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
                             AttackerBrowser, HonestSecretKey, 
                             AttackerSecretKey >>

LogMessagePair(self) == Log(self)

SSR == /\ pc[1] = "SSR"
       /\ PrintT(<<"Same Site Req">>)
       /\ pc' = [pc EXCEPT ![1] = "Session_"]
       /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                       AttackerServerState, AttackerState, AttackerBrowser, 
                       HonestSecretKey, AttackerSecretKey, stack, req, resp >>

Session_ == /\ pc[1] = "Session_"
            /\ HonestBrowser' = [HonestBrowser EXCEPT !.Cookies = {HonestSessionId}]
            /\ HonestServerState' = [HonestServerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
            /\ pc' = [pc EXCEPT ![1] = "Tokens_"]
            /\ UNCHANGED << MessageLog, AttackerServerState, AttackerState, 
                            AttackerBrowser, HonestSecretKey, 
                            AttackerSecretKey, stack, req, resp >>

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
           /\ UNCHANGED << MessageLog, AttackerServerState, AttackerState, 
                           AttackerBrowser, HonestSecretKey, AttackerSecretKey >>

SiteRequest == SSR \/ Session_ \/ Tokens_

CSR == /\ pc[2] = "CSR"
       /\ PrintT(<<"Cross Site Req">>)
       /\ pc' = [pc EXCEPT ![2] = "HonestToAttacker"]
       /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                       AttackerServerState, AttackerState, AttackerBrowser, 
                       HonestSecretKey, AttackerSecretKey, stack, req, resp >>

HonestToAttacker == /\ pc[2] = "HonestToAttacker"
                    /\ HonestBrowser' = [HonestBrowser EXCEPT !.Cookies = {HonestSessionId}]
                    /\ HonestServerState' = [HonestServerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
                    /\ AttackerState' = [AttackerState EXCEPT !.SessionIds = HonestBrowser'.Cookies]
                    /\ AttackerBrowser' = [AttackerBrowser EXCEPT !.Cookies = AttackerState'.SessionIds]
                    /\ pc' = [pc EXCEPT ![2] = "Session"]
                    /\ UNCHANGED << MessageLog, AttackerServerState, 
                                    HonestSecretKey, AttackerSecretKey, stack, 
                                    req, resp >>

Session == /\ pc[2] = "Session"
           /\ AttackerServerState' = [AttackerServerState EXCEPT !.SessionIds = AttackerBrowser.Cookies]
           /\ pc' = [pc EXCEPT ![2] = "Tokens"]
           /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                           AttackerState, AttackerBrowser, HonestSecretKey, 
                           AttackerSecretKey, stack, req, resp >>

Tokens == /\ pc[2] = "Tokens"
          /\ AttackerBrowser' = [AttackerBrowser EXCEPT !.Headers = AttackerSecretKey.secret]
          /\ /\ req' = [req EXCEPT ![2] = ServerRequest(AttackerBrowser')]
             /\ resp' = [resp EXCEPT ![2] = Response(ServerRequest(AttackerBrowser'), HonestServerState)]
             /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "LogMessagePair",
                                                   pc        |->  "Done",
                                                   req       |->  req[2],
                                                   resp      |->  resp[2] ] >>
                                               \o stack[2]]
          /\ pc' = [pc EXCEPT ![2] = "Log"]
          /\ UNCHANGED << MessageLog, HonestBrowser, HonestServerState, 
                          AttackerServerState, AttackerState, HonestSecretKey, 
                          AttackerSecretKey >>

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
\* Last modified Fri Apr 28 16:31:17 EDT 2023 by Cade Chabra
\* Last modified Fri Apr 21 11:11:49 EDT 2023 by andyking
\* Created Sat Mar 25 15:05:39 EDT 2023 by andyking
