---- MODULE no_transactions ----
EXTENDS FiniteSets, Naturals
CONSTANTS MaxQueue

Range(T) == { T[x] : x \in DOMAIN T }

(*--algorithm outbox
variables
    queueIn = { [id |-> x] : x \in 1..MaxQueue },
    queueOut = { },
    db = {},

define 
    MessageIds == 1..MaxQueue
    TypeInvariant == 
        /\ queueIn \in SUBSET [id : MessageIds]
        /\ queueOut \in SUBSET [id : MessageIds, ver : Nat]
        /\ db \in SUBSET [id : MessageIds, ver : Nat]
        
    NoGhostMessages == \A m \in queueOut : 
                            \E i \in db : i.id = m.id /\ i.ver = m.ver
    
    NoDuplicatedProcessings == \A a \in db:
                                ~ \E b \in db : a.id = b.id /\ a.ver /= b.ver
     
    Safety == NoGhostMessages /\ NoDuplicatedProcessings

    Termination == <>(/\ pc[1] = "Receive"
                      /\ Cardinality(queueIn) = 0)
    
    end define;

macro Fail() begin
    if c > 2 then 
        queueIn := {m \in queueIn: m /= msg};
    end if;

    goto MainLoop;
end macro;

fair process Handler = 1
variables
    msg,
    c, 
begin
Start:
    c := 0;
MainLoop:
    while TRUE do
    
    Receive:
        await Cardinality(queueIn) > 0; (* wait for a message *)
        with m \in queueIn do msg := m; end with; (* assign msg to an input queue *)
        c := c+1;
                
    UpdateDb:
        either Fail();
        or db := db \union {[id |-> msg.id, ver |-> c]}; 
        end either;

    SendOutgoingMsg:
        either Fail();
        or queueOut := queueOut \union {[id |-> msg.id, ver |-> c]};
        end either;

    AckInMsg:
        either Fail();
        or queueIn := {m \in queueIn: m /= msg};
        end either;
        
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES queueIn, queueOut, db, pc

(* define statement *)
MessageIds == 1..MaxQueue
TypeInvariant ==
    /\ queueIn \in SUBSET [id : MessageIds]
    /\ queueOut \in SUBSET [id : MessageIds, ver : Nat]
    /\ db \in SUBSET [id : MessageIds, ver : Nat]

NoGhostMessages == \A m \in queueOut :
                        \E i \in db : i.id = m.id /\ i.ver = m.ver

NoDuplicatedProcessings == \A a \in db:
                            ~ \E b \in db : a.id = b.id /\ a.ver /= b.ver

Safety == NoGhostMessages /\ NoDuplicatedProcessings

Termination == <>(/\ pc[1] = "Receive"
                  /\ Cardinality(queueIn) = 0)

VARIABLES msg, c

vars == << queueIn, queueOut, db, pc, msg, c >>

ProcSet == {1}

Init == (* Global variables *)
        /\ queueIn = { [id |-> x] : x \in 1..MaxQueue }
        /\ queueOut = { }
        /\ db = {}
        (* Process Handler *)
        /\ msg = defaultInitValue
        /\ c = defaultInitValue
        /\ pc = [self \in ProcSet |-> "Start"]

Start == /\ pc[1] = "Start"
         /\ c' = 0
         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
         /\ UNCHANGED << queueIn, queueOut, db, msg >>

MainLoop == /\ pc[1] = "MainLoop"
            /\ pc' = [pc EXCEPT ![1] = "Receive"]
            /\ UNCHANGED << queueIn, queueOut, db, msg, c >>

Receive == /\ pc[1] = "Receive"
           /\ Cardinality(queueIn) > 0
           /\ \E m \in queueIn:
                msg' = m
           /\ c' = c+1
           /\ pc' = [pc EXCEPT ![1] = "UpdateDb"]
           /\ UNCHANGED << queueIn, queueOut, db >>

UpdateDb == /\ pc[1] = "UpdateDb"
            /\ \/ /\ IF c > 2
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                        ELSE /\ TRUE
                             /\ UNCHANGED queueIn
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                  /\ db' = db
               \/ /\ db' = (db \union {[id |-> msg.id, ver |-> c]})
                  /\ pc' = [pc EXCEPT ![1] = "SendOutgoingMsg"]
                  /\ UNCHANGED queueIn
            /\ UNCHANGED << queueOut, msg, c >>

SendOutgoingMsg == /\ pc[1] = "SendOutgoingMsg"
                   /\ \/ /\ IF c > 2
                               THEN /\ queueIn' = {m \in queueIn: m /= msg}
                               ELSE /\ TRUE
                                    /\ UNCHANGED queueIn
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED queueOut
                      \/ /\ queueOut' = (queueOut \union {[id |-> msg.id, ver |-> c]})
                         /\ pc' = [pc EXCEPT ![1] = "AckInMsg"]
                         /\ UNCHANGED queueIn
                   /\ UNCHANGED << db, msg, c >>

AckInMsg == /\ pc[1] = "AckInMsg"
            /\ \/ /\ IF c > 2
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                        ELSE /\ TRUE
                             /\ UNCHANGED queueIn
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
               \/ /\ queueIn' = {m \in queueIn: m /= msg}
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
            /\ UNCHANGED << queueOut, db, msg, c >>

Handler == Start \/ MainLoop \/ Receive \/ UpdateDb \/ SendOutgoingMsg
              \/ AckInMsg

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Handler
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Handler)

\* END TRANSLATION

====
