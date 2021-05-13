---- MODULE MessageHandler ----
EXTENDS FiniteSets, Naturals
CONSTANTS MaxFailures, NoMessages

(*--algorithm outbox
variables
    queueIn = { [id |-> x] : x \in MessageIds },
    queueOut = { },
    db = {},
    processed = {},
    failures = [ msgId \in MessageIds |-> 0],
    txCounter = 0,

define 
    MessageIds == 1..NoMessages
    TypeInvariant == 
        /\ queueIn \in SUBSET [id : MessageIds]
        /\ queueOut \in SUBSET [id : MessageIds, txId : Nat]
        /\ db \in SUBSET [id : MessageIds, txId : Nat]
    
    NoGhostMessages == \A m \in processed : 
                        \/ ~ \E msg \in queueOut : msg.id = m.id
                        \/   \E chg \in db       : chg.id = m.id
    
    NoLostMessages == \A m \in processed :
                        \/ ~ \E chg \in db       : chg.id = m.id
                        \/   \E msg \in queueOut : msg.id = m.id
    
    NoLostWrite == \A m \in processed: 
                    \E chg \in db: chg.id = m.id
    
    NoDuplicatedProcessings == \A a \in db:
                               ~ \E b \in db : a.id = b.id /\ a.txId /= b.txId
     
    Safety == NoGhostMessages /\ NoDuplicatedProcessings

    Finishes == <>(/\ pc[1] = "Receive"
                   /\ Cardinality(queueIn) = NoMessages)
    
    end define;

macro Fail(messageId) begin
    if failures[messageId] = MaxFailures then 
        queueIn := {m \in queueIn: m /= msg};
        processed := processed \union {msg};
    else
        failures[messageId] := failures[messageId] + 1;
    end if;

    goto MainLoop;
end macro;

fair process Handler = 1
variables
    msg,
    txId, 
begin
MainLoop:
    while TRUE do
    
    Receive: (* wait for a message and store in msg variable *)
        await Cardinality(queueIn) > 0; 
        with m \in queueIn do msg := m; end with; 
    
    Process:
        txId := txCounter;
        txCounter := txCounter + 1;

    SendOutgoingMsg:  (*send output messages - can fail *)
        either Fail(msg.id);
        or queueOut := queueOut \union {[id |-> msg.id, txId |-> txId]};
        end either;
        
    UpdateDb: (* update data base - can fail *)
        either Fail(msg.id);
        or db := db \union {[id |-> msg.id, txId |-> txId]}; 
        end either;

    AckInMsg: (* remove message from the input queue - can fail *)
        either Fail(msg.id);
        or 
            queueIn := {m \in queueIn: m /= msg};
            processed := processed \union {msg};
        end either;
        
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES queueIn, queueOut, db, processed, failures, txCounter, pc

(* define statement *)
MessageIds == 1..NoMessages
TypeInvariant ==
    /\ queueIn \in SUBSET [id : MessageIds]
    /\ queueOut \in SUBSET [id : MessageIds, txId : Nat]
    /\ db \in SUBSET [id : MessageIds, txId : Nat]

NoGhostMessages == \A m \in processed :
                    \/ ~ \E msg \in queueOut : msg.id = m.id
                    \/   \E chg \in db       : chg.id = m.id

NoLostMessages == \A m \in processed :
                    \/ ~ \E chg \in db       : chg.id = m.id
                    \/   \E msg \in queueOut : msg.id = m.id

NoLostWrite == \A m \in processed:
                \E chg \in db: chg.id = m.id

NoDuplicatedProcessings == \A a \in db:
                           ~ \E b \in db : a.id = b.id /\ a.txId /= b.txId

Safety == NoGhostMessages /\ NoDuplicatedProcessings

Finishes == <>(/\ pc[1] = "Receive"
               /\ Cardinality(queueIn) = NoMessages)

VARIABLES msg, txId

vars == << queueIn, queueOut, db, processed, failures, txCounter, pc, msg, 
           txId >>

ProcSet == {1}

Init == (* Global variables *)
        /\ queueIn = { [id |-> x] : x \in MessageIds }
        /\ queueOut = { }
        /\ db = {}
        /\ processed = {}
        /\ failures = [ msgId \in MessageIds |-> 0]
        /\ txCounter = 0
        (* Process Handler *)
        /\ msg = defaultInitValue
        /\ txId = defaultInitValue
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop == /\ pc[1] = "MainLoop"
            /\ pc' = [pc EXCEPT ![1] = "Receive"]
            /\ UNCHANGED << queueIn, queueOut, db, processed, failures, 
                            txCounter, msg, txId >>

Receive == /\ pc[1] = "Receive"
           /\ Cardinality(queueIn) > 0
           /\ \E m \in queueIn:
                msg' = m
           /\ pc' = [pc EXCEPT ![1] = "Process"]
           /\ UNCHANGED << queueIn, queueOut, db, processed, failures, 
                           txCounter, txId >>

Process == /\ pc[1] = "Process"
           /\ txId' = txCounter
           /\ txCounter' = txCounter + 1
           /\ pc' = [pc EXCEPT ![1] = "SendOutgoingMsg"]
           /\ UNCHANGED << queueIn, queueOut, db, processed, failures, msg >>

SendOutgoingMsg == /\ pc[1] = "SendOutgoingMsg"
                   /\ \/ /\ IF failures[(msg.id)] = MaxFailures
                               THEN /\ queueIn' = {m \in queueIn: m /= msg}
                                    /\ processed' = (processed \union {msg})
                                    /\ UNCHANGED failures
                               ELSE /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)] + 1]
                                    /\ UNCHANGED << queueIn, processed >>
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED queueOut
                      \/ /\ queueOut' = (queueOut \union {[id |-> msg.id, txId |-> txId]})
                         /\ pc' = [pc EXCEPT ![1] = "UpdateDb"]
                         /\ UNCHANGED <<queueIn, processed, failures>>
                   /\ UNCHANGED << db, txCounter, msg, txId >>

UpdateDb == /\ pc[1] = "UpdateDb"
            /\ \/ /\ IF failures[(msg.id)] = MaxFailures
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                             /\ processed' = (processed \union {msg})
                             /\ UNCHANGED failures
                        ELSE /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)] + 1]
                             /\ UNCHANGED << queueIn, processed >>
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                  /\ db' = db
               \/ /\ db' = (db \union {[id |-> msg.id, txId |-> txId]})
                  /\ pc' = [pc EXCEPT ![1] = "AckInMsg"]
                  /\ UNCHANGED <<queueIn, processed, failures>>
            /\ UNCHANGED << queueOut, txCounter, msg, txId >>

AckInMsg == /\ pc[1] = "AckInMsg"
            /\ \/ /\ IF failures[(msg.id)] = MaxFailures
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                             /\ processed' = (processed \union {msg})
                             /\ UNCHANGED failures
                        ELSE /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)] + 1]
                             /\ UNCHANGED << queueIn, processed >>
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
               \/ /\ queueIn' = {m \in queueIn: m /= msg}
                  /\ processed' = (processed \union {msg})
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                  /\ UNCHANGED failures
            /\ UNCHANGED << queueOut, db, txCounter, msg, txId >>

Handler == MainLoop \/ Receive \/ Process \/ SendOutgoingMsg \/ UpdateDb
              \/ AckInMsg

Next == Handler

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Handler)

\* END TRANSLATION

====
