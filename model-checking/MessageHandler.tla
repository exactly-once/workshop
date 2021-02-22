---- MODULE MessageHandler ----
EXTENDS FiniteSets, Naturals
CONSTANTS MaxFailures, NoHandlers, NoMessages

(*--algorithm outbox
variables
    queueIn = { [id |-> x] : x \in MessageIds },
    queueOut = { },
    db = {},
    processed = {},
    failures = [ msgId \in MessageIds |-> 0],
    txId = 0,

define 
    MessageIds == 1..NoMessages
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
    c, 
begin
MainLoop:
    while TRUE do
    
    Receive: (* wait for a message and store in msg vairable *)
        await Cardinality(queueIn) > 0; 
        with m \in queueIn do msg := m; end with; 
    
    Process:
        c := txId;
        txId := txId + 1;

    SendOutgoingMsg:  (*send output messages - can fail *)
        either Fail(msg.id);
        or queueOut := queueOut \union {[id |-> msg.id, ver |-> c]};
        end either;
        
    UpdateDb: (* update data base - can fail *)
        either Fail(msg.id);
        or db := db \union {[id |-> msg.id, ver |-> c]}; 
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
VARIABLES queueIn, queueOut, db, processed, failures, txId, pc

(* define statement *)
MessageIds == 1..NoMessages
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
               /\ Cardinality(queueIn) = NoMessages)

VARIABLES msg, c

vars == << queueIn, queueOut, db, processed, failures, txId, pc, msg, c >>

ProcSet == {1}

Init == (* Global variables *)
        /\ queueIn = { [id |-> x] : x \in MessageIds }
        /\ queueOut = { }
        /\ db = {}
        /\ processed = {}
        /\ failures = [ msgId \in MessageIds |-> 0]
        /\ txId = 0
        (* Process Handler *)
        /\ msg = defaultInitValue
        /\ c = defaultInitValue
        /\ pc = [self \in ProcSet |-> "MainLoop"]

MainLoop == /\ pc[1] = "MainLoop"
            /\ pc' = [pc EXCEPT ![1] = "Receive"]
            /\ UNCHANGED << queueIn, queueOut, db, processed, failures, txId, 
                            msg, c >>

Receive == /\ pc[1] = "Receive"
           /\ Cardinality(queueIn) > 0
           /\ \E m \in queueIn:
                msg' = m
           /\ pc' = [pc EXCEPT ![1] = "Process"]
           /\ UNCHANGED << queueIn, queueOut, db, processed, failures, txId, c >>

Process == /\ pc[1] = "Process"
           /\ c' = txId
           /\ txId' = txId + 1
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
                      \/ /\ queueOut' = (queueOut \union {[id |-> msg.id, ver |-> c]})
                         /\ pc' = [pc EXCEPT ![1] = "UpdateDb"]
                         /\ UNCHANGED <<queueIn, processed, failures>>
                   /\ UNCHANGED << db, txId, msg, c >>

UpdateDb == /\ pc[1] = "UpdateDb"
            /\ \/ /\ IF failures[(msg.id)] = MaxFailures
                        THEN /\ queueIn' = {m \in queueIn: m /= msg}
                             /\ processed' = (processed \union {msg})
                             /\ UNCHANGED failures
                        ELSE /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)] + 1]
                             /\ UNCHANGED << queueIn, processed >>
                  /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                  /\ db' = db
               \/ /\ db' = (db \union {[id |-> msg.id, ver |-> c]})
                  /\ pc' = [pc EXCEPT ![1] = "AckInMsg"]
                  /\ UNCHANGED <<queueIn, processed, failures>>
            /\ UNCHANGED << queueOut, txId, msg, c >>

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
            /\ UNCHANGED << queueOut, db, txId, msg, c >>

Handler == MainLoop \/ Receive \/ Process \/ SendOutgoingMsg \/ UpdateDb
              \/ AckInMsg

Next == Handler

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Handler)

\* END TRANSLATION

====
