---- MODULE MessageHandler ----
EXTENDS FiniteSets, Naturals
CONSTANTS MaxQueue

Range(T) == { T[x] : x \in DOMAIN T }

(*--algorithm outbox
variables
    queueIn = { [id |-> x] : x \in 1..MaxQueue },
    queueOut = { },
    db = {},
    processed = {}

define 
    MessageIds == 1..MaxQueue
    TypeInvariant == 
        /\ queueIn \in SUBSET [id : MessageIds]
        /\ queueOut \in SUBSET [id : MessageIds, ver : Nat]
        /\ db \in SUBSET [id : MessageIds, ver : Nat]
    
    NoGhostMessages == \A m \in processed : 
                        \/ ~ \E msg \in queueOut : msg.id = m.id
                        \/   \E chg \in db       : chg.id = m.id
    
    NoLostMessages == \A m \in processed :
                        \/ ~ \E chg \in db       : chg.id = m.id
                        \/   \E msg \in queueOut : msg.id = m.id
    
    NoLostWrite == \A m \in processed: 
                    \E chg \in db: chg.id = m.id
    
    NoDuplicatedProcessings == \A a \in db:
                               ~ \E b \in db : a.id = b.id /\ a.ver /= b.ver
     
    Safety == NoGhostMessages /\ NoDuplicatedProcessings

    Finishes == <>(/\ pc[1] = "Receive"
                   /\ Cardinality(queueIn) = 1)
    
    end define;

macro Fail() begin
    if c > 2 then 
        queueIn := {m \in queueIn: m /= msg};
        processed := processed \union {msg};
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
    
    Receive: (* wait for a message and store in msg vairable *)
        await Cardinality(queueIn) > 0; 
        with m \in queueIn do msg := m; end with; 
        c := c+1;

    SendOutgoingMsg:  (*send output messages - can fail *)
        either Fail();
        or queueOut := queueOut \union {[id |-> msg.id, ver |-> c]};
        end either;
        
    UpdateDb: (* update data base - can fail *)
        either Fail();
        or db := db \union {[id |-> msg.id, ver |-> c]}; 
        end either;

    AckInMsg: (* remove message from the input queue - can fail *)
        either Fail();
        or 
            queueIn := {m \in queueIn: m /= msg};
            processed := processed \union {msg};
        end either;
        
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES queueIn, queueOut, db, processed, pc

(* define statement *)
MessageIds == 1..MaxQueue
TypeInvariant ==
    /\ queueIn \in SUBSET [id : MessageIds]
    /\ queueOut \in SUBSET [id : MessageIds, ver : Nat]
    /\ db \in SUBSET [id : MessageIds, ver : Nat]

NoGhostMessages == \A m \in processed :
                    \/ ~ \E msg \in queueOut : msg.id = m.id
                    \/   \E chg \in db       : chg.id = m.id

NoLostMessages == \A m \in processed :
                    \/ ~ \E chg \in db       : chg.id = m.id
                    \/   \E msg \in queueOut : msg.id = m.id

NoLostWrite == \A m \in processed:
                \E chg \in db: chg.id = m.id

NoDuplicatedProcessings == \A a \in db:
                           ~ \E b \in db : a.id = b.id /\ a.ver /= b.ver

Safety == NoGhostMessages /\ NoDuplicatedProcessings

Finishes == <>(/\ pc[1] = "Receive"
               /\ Cardinality(queueIn) = 1)

VARIABLES msg, c

vars == << queueIn, queueOut, db, processed, pc, msg, c >>

ProcSet == {1}

Init == (* Global variables *)
        /\ queueIn = { [id |-> x] : x \in 1..MaxQueue }
        /\ queueOut = { }
        /\ db = {}
        /\ processed = {}
        (* Process Handler *)
        /\ msg = defaultInitValue
        /\ c = defaultInitValue
        /\ pc = [self \in ProcSet |-> "Start"]

Start == /\ pc[1] = "Start"
         /\ c' = 0
         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
         /\ UNCHANGED << queueIn, queueOut, db, processed, msg >>

MainLoop == /\ pc[1] = "MainLoop"
            /\ pc' = [pc EXCEPT ![1] = "Receive"]
            /\ UNCHANGED << queueIn, queueOut, db, processed, msg, c >>

Receive == /\ pc[1] = "Receive"
           /\ Cardinality(queueIn) > 0
           /\ \E m \in queueIn:
                msg' = m
           /\ c' = c+1
           /\ pc' = [pc EXCEPT ![1] = "SendOutgoingMsg"]
           /\ UNCHANGED << queueIn, queueOut, db, processed >>

SendOutgoingMsg == /\ pc[1] = "SendOutgoingMsg"
                   /\ \/ /\ IF c > 2
                               THEN /\ queueIn' = {m \in queueIn: m /= msg}
                                    /\ processed' = (processed \union {msg})
                               ELSE /\ TRUE
                                    /\ UNCHANGED << queueIn, processed >>
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED queueOut
                      \/ /\ queueOut' = (queueOut \union {[id |-> msg.id, ver |-> c]})
                         /\ pc' = [pc EXCEPT ![1] = "UpdateDb"]
                         /\ UNCHANGED <<queueIn, processed>>
                   /\ UNCHANGED << db, msg, c >>

UpdateDb == /\ pc[1] = "UpdateDb"
            /\ \/ /\ IF c > 2
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                             /\ processed' = (processed \union {msg})
                        ELSE /\ TRUE
                             /\ UNCHANGED << queueIn, processed >>
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                  /\ db' = db
               \/ /\ db' = (db \union {[id |-> msg.id, ver |-> c]})
                  /\ pc' = [pc EXCEPT ![1] = "AckInMsg"]
                  /\ UNCHANGED <<queueIn, processed>>
            /\ UNCHANGED << queueOut, msg, c >>

AckInMsg == /\ pc[1] = "AckInMsg"
            /\ \/ /\ IF c > 2
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                             /\ processed' = (processed \union {msg})
                        ELSE /\ TRUE
                             /\ UNCHANGED << queueIn, processed >>
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
               \/ /\ queueIn' = {m \in queueIn: m /= msg}
                  /\ processed' = (processed \union {msg})
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
            /\ UNCHANGED << queueOut, db, msg, c >>

Handler == Start \/ MainLoop \/ Receive \/ SendOutgoingMsg \/ UpdateDb
              \/ AckInMsg

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Handler
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Handler)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
