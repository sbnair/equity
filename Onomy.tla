------------------------------- MODULE Onomy -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT    Peer,
            Adr,
            Val,
            MaxReq

VARIABLE    adrQ,
            aCtl,
            comm,
            commQ,            
            hash,
            netInt,
            r1,
            r2,
            rcvBuf,
            sndBuf,
            store,
            tCtl 

Cmt == INSTANCE Commit
Net == INSTANCE NetworkInterface
Rnd1 == INSTANCE Round1
Rnd2 == INSTANCE Round2
Str == INSTANCE Storage
Sub == INSTANCE Submit


-----------------------------------------------------------------------------

NoVal ==            CHOOSE v : v \notin Val

Stage ==           {  
                      "submit", 
                      "round 1", 
                      "round 2",
                      "lock", 
                      "commit"
                    }

TypeInvariant ==    \* Each peer maintains a tx queue per storage address 
                    /\ adrQ \in [Peer -> [Adr -> Seq(Nat)]]
                    \* Each peer tracks the status of each address
                    /\ aCtl \in [Peer -> [Adr -> Stage]]
                    
                    (*******************************************************)
                    (* Each Peer has a record for each transaction         *)
                    (*                                                     *)
                    (* hash: TX hash                                       *) 
                    (* adrs: Set of tuples for each address                *) 
                    (*******************************************************)
                    
                    /\ tCtl \in [Peer -> {[
                                           hash: Nat, 
                                           adrs: {[
                                                   adr: Adr, 
                                                   val: Val, 
                                                   stg: Stage
                                                 ]}
                                         ]}
                                ]
                    (******************************************************)
                    (* A counter (hash) variable is used to identify      *) 
                    (* transactions by increment.  It is not an ordering  *)
                    (* but only an identifier.  Transactions are ordered  *)
                    (* by the network itself, not by the user.            *)
                    (******************************************************)
                    /\ hash \in Nat

                                                            
IInit ==            /\ Cmt!CommitInit
                    /\ Net!NetInit
                    /\ Rnd1!Round1Init
                    /\ Rnd2!Round2Init
                    /\ Str!StorageInit
                    \* The queue for each address at each peer is empty 
                    /\ adrQ = [p \in Peer |-> [a \in Adr |-> <<>>]]
                    \* The control var for each address at each peer is 
                    \* submit 
                    /\ aCtl = [p \in Peer |-> [a \in Adr |-> "submit"]]
                    \* The control var for each hash at each peer is empty
                    /\ tCtl = [p \in Peer |-> {}]
                    /\ hash = 1
                    
-----------------------------------------------------------------------------                    

ReqBuilder(adrsub) == {[adr |-> a, val |-> CHOOSE v \in Val : TRUE] : a \in adrsub}
                      (*
                      LET F[adrs \in SUBSET adrsub] ==
                        IF adrs = {} THEN {[adr: Adr, val: Val]} ELSE
                          LET a == CHOOSE a \in adrs : TRUE 
                              v == CHOOSE v \in Val : TRUE IN
                              UNION {F[adrs \ {a}], [adr |-> a, val |-> v]}
                      IN F[adrsub] *)


                    (*******************************************************)
                    (* User requests operation that may affect multiple    *)
                    (* addresses.                                          *)
                    (*******************************************************)
                    
Req(p) ==           /\ hash < MaxReq
                    /\ \E adrs \in SUBSET Adr :
                        /\ LET req == ReqBuilder(adrs) IN
                        \* Peer p places msg on the network interface
                           /\ sndBuf' = [sndBuf EXCEPT ![p] = Append(sndBuf[p], 
                                              [
                                               hash |-> hash, 
                                               aVals  |-> req, 
                                               stg   |->"submit"
                                              ])]
                        
                        \* Update ctl status of the memory address 
                        \* /\ ctl' = [ctl EXCEPT ![p][a] = "queued"]
                        \* Increment the counter representing unique hash
                    /\ hash' = hash + 1
                    /\ UNCHANGED <<adrQ, aCtl, comm, commQ, netInt, r1, r2, 
                                   rcvBuf, store, tCtl>>

-----------------------------------------------------------------------------

(************************     Network Interface     ************************)

Send(p) ==          /\ Net!Send(p) 
                    /\ UNCHANGED <<adrQ, aCtl, comm, commQ, hash, 
                                   r1, r2, store, tCtl>>

Rcv(p) ==           /\ Net!Rcv(p)
                    /\ UNCHANGED <<adrQ, aCtl, comm, commQ, hash, 
                                   r1, r2, sndBuf, store, tCtl>>

(************************          Submit          *************************)

RcvTx(p) ==         /\ Sub!RcvTx(p)
                    /\ UNCHANGED <<aCtl, comm, commQ, hash, netInt, 
                                   r1, r2, sndBuf, store>>

SubmitAdr(p, a) ==  /\ Sub!SubmitAdr(p, a)
                    /\ UNCHANGED <<comm, commQ, hash, netInt, 
                                   r1, r2, rcvBuf, store>>

(************************          Round 1         *************************)

Round1Rcv(p) ==     /\ Rnd1!Round1Rcv(p)
                    /\ UNCHANGED <<adrQ, aCtl, comm, commQ, hash, netInt, 
                                   r2, sndBuf, store, tCtl>>

Round1Snd(p, a) ==  /\ Rnd1!Round1Snd(p, a)
                    /\ UNCHANGED <<adrQ, comm, commQ, hash, netInt, 
                                   r2, rcvBuf, store, tCtl>>
                                   
(************************          Round 2         *************************)

Round2Rcv(p) ==     /\ Rnd2!Round2Rcv(p)
                    /\ UNCHANGED <<adrQ, aCtl, comm, commQ, hash, netInt, 
                                   r1, sndBuf, store, tCtl>>
                                   
Round2Snd(p, a) ==  /\ Rnd2!Round2Snd(p, a)
                    /\ UNCHANGED <<adrQ, comm, commQ, hash, netInt, 
                                   r1, rcvBuf, store, tCtl>>

(************************          Commit          *************************)

CommitRcv(p) ==     /\ Cmt!CommitRcv(p)
                    /\ UNCHANGED <<adrQ, aCtl, commQ, hash, netInt, 
                                   r1, r2, sndBuf, store, tCtl>>

CommitSeq(p, a) ==  /\ Cmt!CommitSeq(p, a)
                    /\ UNCHANGED <<adrQ, aCtl, hash, netInt, 
                                   r1, r2, rcvBuf, sndBuf, store, tCtl>>

AdrLock(p, a) ==    /\ Cmt!AdrLock(p, a)
                    /\ UNCHANGED <<adrQ, comm, hash, netInt, 
                                   r1, r2, rcvBuf, sndBuf, store, tCtl>>

CommitAdr(p, a) ==  /\ Cmt!CommitAdr(p, a)
                    /\ UNCHANGED <<adrQ, comm, hash, netInt, 
                                   r1, r2, rcvBuf, sndBuf>>

-----------------------------------------------------------------------------
                                 
Next == \/ \E p \in Peer : \/ Req(p) \/ Send(p) \/ Rcv(p) \/ RcvTx(p)
                           \/ Round1Rcv(p) \/ Round2Rcv(p) \/ CommitRcv(p)
                           
           \/ \E a \in Adr : \/ SubmitAdr(p, a) \/ Round1Snd(p, a)
                             \/ Round2Snd(p, a) \/ CommitSeq(p, a)
                             \/ AdrLock(p,a) \/ CommitAdr(p, a)

Spec == IInit /\ [][Next]_<<adrQ, aCtl, comm, commQ, hash, netInt, 
                            r1, r2, rcvBuf, sndBuf, store, tCtl>>

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Mon Nov 23 21:45:02 CST 2020 by dninja
\* Created Sun Sep 13 11:03:56 CDT 2020 by dninja
