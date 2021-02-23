---- MODULE MessageHandler ----
EXTENDS FiniteSets, Naturals
CONSTANTS MaxFailures, NoMessages

(*--algorithm outbox
variables
    queueIn = { [id |-> x] : x \in MessageIds },
    queueOut = { },
    db = {},
    processed = {},
    failures = 0,
    txCounter = 0,

define 
    Fails == IF failures <= MaxFailures THEN {TRUE, FALSE} ELSE {FALSE}
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
    
    ConsistentOutput == \A m1 \in queueOut:
                        ~\E m2 \in queueOut: m1.id = m2.id /\ m1.txId /= m2.txId
    
    Safety == NoGhostMessages /\ NoDuplicatedProcessings

    Finishes == <>(/\ pc[1] = "Receive"
                   /\ Cardinality(queueIn) = NoMessages)
    
    end define;

macro Fail() begin
    failures := failures+1;
    goto MainLoop;
end macro;

fair process Handler = 1
variables
    msg,
    txId, 
begin
MainLoop:
    while TRUE do
    
    Receive: (* wait for a message and store in msg vairable *)
        await Cardinality(queueIn) > 0; 
        with m \in queueIn do msg := m; end with; 
    
        txId := txCounter;
        txCounter := txCounter + 1;
        
    Update: (* update data base - can fail *)
        with fails \in Fails do
            if fails then
                Fail()
            else
                if ~\E chg \in db : chg.id = msg.id then
                    db := db \union {[id |-> msg.id, txId |-> txId]}; 
                end if;
            end if;
        end with;

    Send:
        with fails \in Fails do
            if fails then
                Fail()
            else
                with chg \in {chg \in db : chg.id = msg.id} do
                    queueOut := queueOut \union {[id |-> msg.id, txId |-> chg.txId]};
                end with;
            end if;
        end with;

    AckInMsg: (* remove message from the input queue - can fail *)
        with fails \in Fails do
            if fails then
                Fail()
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
VARIABLES queueIn, queueOut, db, processed, failures, txCounter, pc

(* define statement *)
Fails == IF failures <= MaxFailures THEN {TRUE, FALSE} ELSE {FALSE}
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

ConsistentOutput == \A m1 \in queueOut:
                    ~\E m2 \in queueOut: m1.id = m2.id /\ m1.txId /= m2.txId

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
        /\ failures = 0
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
           /\ txId' = txCounter
           /\ txCounter' = txCounter + 1
           /\ pc' = [pc EXCEPT ![1] = "Update"]
           /\ UNCHANGED << queueIn, queueOut, db, processed, failures >>

Update == /\ pc[1] = "Update"
          /\ \E fails \in Fails:
               IF fails
                  THEN /\ failures' = failures+1
                       /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                       /\ db' = db
                  ELSE /\ IF ~\E chg \in db : chg.id = msg.id
                             THEN /\ db' = (db \union {[id |-> msg.id, txId |-> txId]})
                             ELSE /\ TRUE
                                  /\ db' = db
                       /\ pc' = [pc EXCEPT ![1] = "Send"]
                       /\ UNCHANGED failures
          /\ UNCHANGED << queueIn, queueOut, processed, txCounter, msg, txId >>

Send == /\ pc[1] = "Send"
        /\ \E fails \in Fails:
             IF fails
                THEN /\ failures' = failures+1
                     /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                     /\ UNCHANGED queueOut
                ELSE /\ \E chg \in {chg \in db : chg.id = msg.id}:
                          queueOut' = (queueOut \union {[id |-> msg.id, txId |-> chg.txId]})
                     /\ pc' = [pc EXCEPT ![1] = "AckInMsg"]
                     /\ UNCHANGED failures
        /\ UNCHANGED << queueIn, db, processed, txCounter, msg, txId >>

AckInMsg == /\ pc[1] = "AckInMsg"
            /\ \E fails \in Fails:
                 IF fails
                    THEN /\ failures' = failures+1
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED << queueIn, processed >>
                    ELSE /\ queueIn' = {m \in queueIn: m /= msg}
                         /\ processed' = (processed \union {msg})
                         /\ pc' = [pc EXCEPT ![1] = "MainLoop"]
                         /\ UNCHANGED failures
            /\ UNCHANGED << queueOut, db, txCounter, msg, txId >>

Handler == MainLoop \/ Receive \/ Update \/ Send \/ AckInMsg

Next == Handler

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Handler)

\* END TRANSLATION

====
