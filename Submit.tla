------------------------------- MODULE Submit -------------------------------
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS   Adr,
            Peer
            
VARIABLE    aCtl,
            adrQ,
            rcvBuf,
            sndBuf,
            tCtl
            
-----------------------------------------------------------------------------

                    (*******************************************************)
                    (* Add storage updates to peer-wise address queues.    *)
                    (* Each update is stored in a sequence of hash values  *) 
                    (* for each address                                    *)
                    (*                                                     *)
                    (* p == peer, o[1] == address, h == transaction hash   *)
                    (*******************************************************)

AddAdrQ(p, h, op) ==  LET F[subOp \in SUBSET op] ==
                          IF subOp = {} THEN adrQ
                          ELSE LET o == CHOOSE o \in subOp : TRUE
                            IN [F[subOp \ {o}] EXCEPT 
                               ![p][o.adr] = Append(@, h)]
                      IN F[op]


                    (*******************************************************)
                    (* Add new transaction control record                  *)
                    (* Each transaction control record has control         *)
                    (* variables for each address                          *)
                    (*                                                     *)
                    (* p == peer, h == transaction hash, o[1] == address   *)
                    (* o[2] == value                                       *)
                    (*******************************************************)
                    
AddTxCtl(p, h, op) == [tCtl EXCEPT ![p] = UNION {tCtl[p], 
                       {[hash |-> h, 
                         adrs |-> {[
                                    adr |-> o.adr, 
                                    val |-> o.val, 
                                    stg |-> "submit"
                                  ] : o \in op}]}
                       }]


                    (*******************************************************)
                    (* Process transaction at head of the receive buffer   *)
                    (*                                                     *)
                    (* p == peer                                           *)
                    (*******************************************************)

RcvTx(p) ==         \* Enabling Condition: Receive buffer is not empty
                    /\ Len(rcvBuf[p]) > 0
                    \* Enabling Condition: Receive buffer is set to "submit"
                    /\ Head(rcvBuf[p]).msg.stg = "submit"
                    /\ LET \* Set of address X values tuples in the transaction
                         op == Head(rcvBuf[p]).msg.aVals IN
                           \* Hash of transaction
                         LET h == Head(rcvBuf[p]).msg.hash
                         IN  /\ adrQ' = AddAdrQ(p, h, op) 
                             /\ tCtl' = AddTxCtl(p, h, op)
                             \* Remove tx from receive buffer
                             /\ rcvBuf' = [rcvBuf EXCEPT ![p] = Tail(@)]
                             /\ UNCHANGED <<aCtl, sndBuf>>

                    (*******************************************************)
                    (* Set tx control variable for each address in the     *)
                    (* queue submitted to "vote"                           *)
                    (*                                                     *)
                    (* p == peer, a == address, txs == txs in queue        *)
                    (*******************************************************)

UpdTxCtl(p, a, txs) == LET F[i \in 0 .. Len(txs)] ==
                         IF i = 0 THEN tCtl
                         ELSE 
                           \* CHOOSE the tx record for current tx 
                           LET txRec == CHOOSE txRec \in tCtl[p] :
                               txRec.hash = txs[i]
                           IN LET aRec == CHOOSE aRec \in txRec.adrs : 
                                  aRec.adr = a
                              IN LET newRecSet == 
                                   IF Cardinality(txRec.adrs) = 1 THEN
                                     {[adr |-> a, 
                                       val |-> aRec.val, 
                                       stg |-> "vote"]}
                                   ELSE UNION {txRec.adrs \ {aRec},
                                               {[adr |-> a, 
                                                val |-> aRec.val, 
                                                stg |-> "vote"]}} 
                                 IN [F[i-1] EXCEPT ![p] = 
                                   IF Cardinality(@) = 1 THEN newRecSet
                                   ELSE UNION {
                                     \* All tx not the current tx
                                     {tx \in F[i-1][p] : tx.hash # txs[i]},
                                     \* Create new tx record with address 
                                     \* status updated to vote
                                     newRecSet}]
                       IN F[Len(txs)]
          

                    (*******************************************************)
                    (* Peer submits address queue to network when address  *)
                    (* control is set to "submit" and queue is not empty.  *)
                    (* After submit, address control is set to "round 1"   *)
                    (*                                                     *)
                    (* p == peer, a == address                             *)
                    (*******************************************************)

SubmitAdr(p, a) ==  LET txs == adrQ[p][a] IN
                    \* Enabling condition: length of address queue > 0
                    /\ Len(txs) > 0
                    \* Enabling condition: address control = submit
                    /\ aCtl[p][a] = "submit"
                    \* Send the current queue to all nodes
                    /\ sndBuf' = [sndBuf EXCEPT ![p] = Append(@, 
                                                        [
                                                         adr   |-> a,
                                                         hashs |-> txs, 
                                                         stg   |-> "round 1"
                                                        ])]
                    /\ aCtl' = [aCtl EXCEPT ![p][a] = "round 1"]
                    \* Set transaction control for each submission to vote
                    /\ tCtl' = UpdTxCtl(p, a, txs)
                    /\ adrQ' = [adrQ EXCEPT ![p][a] = << >>]
                    /\ UNCHANGED <<rcvBuf>>
                    
=============================================================================
\* Modification History
\* Last modified Mon Nov 23 22:12:35 CST 2020 by dninja
\* Created Sun Oct 11 23:05:00 CDT 2020 by dninja
