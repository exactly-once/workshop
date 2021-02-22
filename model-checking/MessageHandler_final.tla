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
    txId = 0,

define 
    Fails(messageId) == IF messageId > MaxFailures THEN {TRUE, FALSE} ELSE {FALSE}
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
    
    ConsistentOutput == \A m1 \in queueOut:
                        ~\E m2 \in queueOut: m1.id = m2.id /\ m1.ver /= m2.ver
    
    Safety == NoGhostMessages /\ NoDuplicatedProcessings

    Finishes == <>(/\ pc[1] = "Receive"
                   /\ Cardinality(queueIn) = NoMessages)
    
    end define;

macro Fail(messageId) begin
    failures[messageId] := failures[messageId]+1;
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

    Update: (* update data base and send output messages - can fail *)
        with fails \in Fails(msg.id) do
            if fails then 
                Fail(msg.id)
            else
                if ~\E chg \in db : chg.id = msg.id then
                    db := db \union {[id |-> msg.id, ver |-> c]}; 
                end if;
            end if;
        end with;

    Send:
        with fails \in Fails(msg.id) do
            if fails then 
                Fail(msg.id)
            else
                with chg \in {chg \in db : chg.id = msg.id} do
                    queueOut := queueOut \union {[id |-> msg.id, ver |-> chg.ver]};
                end with;
            end if;
        end with;

    AckInMsg: (* remove message from the input queue - can fail *)
        with fails \in Fails(msg.id) do
            if fails then 
                Fail(msg.id)
            else
                queueIn := {m \in queueIn: m /= msg};
                processed := processed \union {msg};
            end if;
        end with;
        
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES queueIn, queueOut, db, processed, failures, txId, pc

(* define statement *)
Fails(messageId) == IF messageId > MaxFailures THEN {TRUE, FALSE} ELSE {FALSE}
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

ConsistentOutput == \A m1 \in queueOut:
                    ~\E m2 \in queueOut: m1.id = m2.id /\ m1.ver /= m2.ver

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
           /\ pc' = [pc EXCEPT ![1] = "Update"]
           /\ UNCHANGED << queueIn, queueOut, db, processed, failures, msg >>

Update == /\ pc[1] = "Update"
          /\ \E fails \in Fails(msg.id):
               IF fails
                  THEN /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)]+1]
                       /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                       /\ db' = db
                  ELSE /\ IF ~\E chg \in db : chg.id = msg.id
                             THEN /\ db' = (db \union {[id |-> msg.id, ver |-> c]})
                             ELSE /\ TRUE
                                  /\ db' = db
                       /\ pc' = [pc EXCEPT ![1] = "Send"]
                       /\ UNCHANGED failures
          /\ UNCHANGED << queueIn, queueOut, processed, txId, msg, c >>

Send == /\ pc[1] = "Send"
        /\ \E fails \in Fails(msg.id):
             IF fails
                THEN /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)]+1]
                     /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                     /\ UNCHANGED queueOut
                ELSE /\ \E chg \in {chg \in db : chg.id = msg.id}:
                          queueOut' = (queueOut \union {[id |-> msg.id, ver |-> chg.ver]})
                     /\ pc' = [pc EXCEPT ![1] = "AckInMsg"]
                     /\ UNCHANGED failures
        /\ UNCHANGED << queueIn, db, processed, txId, msg, c >>

AckInMsg == /\ pc[1] = "AckInMsg"
            /\ \E fails \in Fails(msg.id):
                 IF fails
                    THEN /\ failures' = [failures EXCEPT ![(msg.id)] = failures[(msg.id)]+1]
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED << queueIn, processed >>
                    ELSE /\ queueIn' = {m \in queueIn: m /= msg}
                         /\ processed' = (processed \union {msg})
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED failures
            /\ UNCHANGED << queueOut, db, txId, msg, c >>

Handler == MainLoop \/ Receive \/ Process \/ Update \/ Send \/ AckInMsg

Next == Handler

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Handler)

\* END TRANSLATION

====
