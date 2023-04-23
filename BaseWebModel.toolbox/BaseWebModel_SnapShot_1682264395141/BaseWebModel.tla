---------------------------- MODULE BaseWebModel ----------------------------

EXTENDS Integers, TLC, Sequences

CONSTANT HonestSessionId

(* --algorithm STPWebModel
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
    HasValidToken(req, srv) == (srv.Tokens = {HonestKey}) = (req.cookies = {HonestSessionId})
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
    
    call LogMessagePair(ServerRequest(AttackerBrowser), Response(ServerRequest(AttackerBrowser), AttackerServerState));
    
end process;
        
end algorithm; *)

=============================================================================
\* Modification History
\* Last modified Sun Apr 23 11:39:10 EDT 2023 by Cade Chabra
\* Created Sun Apr 23 11:29:07 EDT 2023 by Cade Chabra
