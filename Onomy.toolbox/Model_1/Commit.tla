------------------------------- MODULE Commit -------------------------------
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT    Adr,
            Peer,
            Val

VARIABLE    aCtl,
            comm,
            commQ,
            rcvBuf,
            store,
            tCtl
            

Str == INSTANCE Storage

-----------------------------------------------------------------------------

CommitInvariant ==  /\ comm \in [Peer -> [Adr -> {[
                                                   orig: Peer, 
                                                   hashs: Seq(Nat)
                                                 ]}]]
                    
                    (*******************************************************)
                    (* Ordered commit queue of transactions.  Transactions *)
                    (* must be placed in commit queue before an effected   *)
                    (* address is unlocked and available for voting        *)
                    (*******************************************************)
                    /\ commQ \in [Peer -> [Adr -> Seq(Nat)]]
                    
CommitInit ==       /\ comm = [p \in Peer |-> [a \in Adr |-> {}]]
                    /\ commQ = [p \in Peer |-> [a \in Adr |-> <<>>]]

                                      
                    (*******************************************************)
                    (* Commit Receive: each peer receives commits for next *)
                    (* update for an address                               *)
                    (*******************************************************)
                    
CommitRcv(p) ==     /\ Len(rcvBuf[p]) > 0 \* Receive buffer is not empty
                    /\ Head(rcvBuf[p]).msg.stg = "commit"
                    /\ LET vote == Head(rcvBuf[p])
                       IN LET msg == vote.msg
                              route == vote.route IN
                            LET v == CHOOSE v \in comm[p][msg.adr] : 
                                               v.orig = route.orig
                            IN  \* The peer has not voted yet in Commit
                              /\ v = {}
                              \* Add Commit vote to comm accounting function
                              /\ comm' = [comm EXCEPT ![p][msg.adr] = 
                                               UNION {comm[p][msg.adr], 
                                                      [
                                                       orig  |-> route.orig, 
                                                       hashs |-> msg.hashs
                                                      ]}]
                              \* Remove Round 2 vote from rcvBuf'
                              /\ rcvBuf' = [rcvBuf EXCEPT ![p] = Tail(@)]
                    /\ UNCHANGED <<aCtl, commQ, store, tCtl>>
                    

                    (********************************************************)
                    (* For each transaction within a round of adr consensus *)
                    (* set adr for commit in transaction accounting variable*)
                    (* if all transaction address variable states are commit*)
                    (* then commit transaction and remove the head of the   *)
                    (* commit adr queue.  If adr commit queue is empty set  *)
                    (* to submit.                                           *)
                    (********************************************************)

SetCount(commVotes) == LET s == CHOOSE s \in commVotes : TRUE
                       IN Cardinality({t \in commVotes : t = s})


                    (********************************************************)
                    (* Are each of the addresses within the transaction     *)
                    (* ready to commit?                                     *)
                    (********************************************************)
                       
CommitTest(a, txRec) == LET F[aRecs \in SUBSET txRec.adrs] ==
                          IF aRecs = {} THEN TRUE 
                          ELSE LET aRec == CHOOSE aRec \in aRecs : TRUE IN
                            \* Is this the current address?
                            IF aRec.adr = a THEN F[aRecs \ {aRec}]
                            ELSE  IF aRec.stg = "commit"
                                  THEN F[aRecs \ {aRec}]
                                  ELSE FALSE
                        IN F[txRec.adrs]

      
                   (********************************************************)
                   (* Build store update based on transaction record in    *)
                   (* tCtl                                                 *)
                   (********************************************************)
                   
CommitTX(p, txRec) == LET F[aRecs \in SUBSET txRec.adrs] ==
                     LET aRec == CHOOSE aRec \in aRecs : TRUE
                     IN IF aRec = {} THEN store
                        ELSE [F[aRecs \ {aRec}] EXCEPT ![p][aRec.adr] =
                                                   [
                                                     val   |-> aRec.val, 
                                                     nonce |-> @.nonce + 1,
                                                     hash  |-> txRec.hash
                                                   ]
                             ]
                   IN F[txRec.adrs]
                   
                   
                   (********************************************************)
                   (* Check if commit queue is empty or going to be empty  *)
                   (* after this step, then set to "submit" if empty       *)
                   (* or "commit" if not empty                             *)
                   (********************************************************)

AdrUnlock(commAdr, p, txRec) ==
                  \* Iterate through the address tuples in the transaction
                    LET F[aRecs \in SUBSET txRec.adrs] ==
                      \* a: Choose an address tuple from tuple set
                      LET aRec == CHOOSE aRec \in aRecs : TRUE
                         \* IF: aRec is empty then aCtl function iterable
                      IN IF aRec = {} THEN aCtl
                         \* ELSE: aCtl iterable EXCEPT [peer][address]
                         ELSE [F[aRecs \ {aRec}] EXCEPT ![p][aRec.adr] =
                           \* IF: this is the address that initiates commit
                           IF commAdr = aRec.adr THEN
                             \* THEN: IF: There is more than one tx in
                             \* the address commit queue
                             IF Cardinality(commQ[p][aRec.adr]) > 1 
                             THEN "commit"
                             ELSE "submit"
                           \* ELSE: IF: this is not the address committing
                           ELSE IF commQ[p][aRec.adr] = << >> THEN "submit"
                                ELSE "commit"]
                    IN F[txRec.adrs]




                   (********************************************************)
                   (* If aCtl set to commit and commitQ empty then         *)
                   (* transfer round2 sequence of hash to commitQ          *)
                   (********************************************************)

CommitSeq(p, a) ==  \* Enabling condition: Address control set to commit
                    /\ aCtl[p][a] = "commit"
                    \* Enabling condition: Commit queue is empty
                    /\ commQ[p][a] = << >>
                    /\ LET commVotes == comm[p][a]
                          \* Enabling condition: commit votes = # peers
                       IN /\ SetCount(commVotes) = Cardinality(Peer)  
                          /\ LET cmt == CHOOSE cmt \in commVotes : TRUE
                             IN /\ commQ' = [commQ EXCEPT ![p][a] = cmt.hashs]
                                /\ comm' = [comm EXCEPT ![p][a] = {}]
                    /\ UNCHANGED <<aCtl, rcvBuf, store, tCtl>>
                                                
AdrLock(p, a) ==    \* Enabling condition: Address control set to commit
                    /\ aCtl[p][a] = "commit"
                    \* Enabling condition: Commit queue for adr is not empty
                    /\ commQ[p][a] # << >>
                    \* Commit if all address in tx are in commit state or 
                    \* lock the address
                    /\ LET tx == Head(commQ[p][a]) IN
                         LET txRec == CHOOSE txRec \in tCtl[p] :
                             txRec[1] = tx IN
                         /\ CommitTest(a, txRec) = FALSE
                         /\ \* Else lock the address until other adr
                            \* in transaction are ready to commit
                            /\ aCtl' = [aCtl EXCEPT ![p][a] = "lock"]
                            \* Remove the current tx from the commit
                            \* queue of the address as tx will be
                            \* committed and address unlocked when
                            \* all address in tx are set to commit in
                            \* tCtl
                            /\ commQ' = [commQ EXCEPT ![p][a] = Tail(@)]
                   /\ UNCHANGED <<comm, rcvBuf, store, tCtl>>

                    
                   (********************************************************)
                   (* Commit transaction if all addresses in transaction   *)
                   (* control are set to "commit" otherwise lock address   *)
                   (********************************************************)                             
                           
CommitAdr(p, a) ==  \* Enabling condition: Address control set to commit
                    /\ aCtl[p][a] = "commit"
                    \* Enabling condition: Commit queue for adr is not empty
                    /\ commQ[p][a] # << >>
                    \* Commit if all address in tx are in commit state or 
                    \* lock the address
                    /\ LET tx == Head(commQ[p][a])
                       IN LET txRec == CHOOSE txRec \in tCtl[p] :
                              txRec[1] = tx IN
                          \* Enabling condition: All other adr are commit
                          /\ CommitTest(a, txRec)
                          \* Commit the tx to the store
                          /\ store' = CommitTX(p, txRec)
                          \* Unlock other addresses in the tx
                          /\ aCtl' = AdrUnlock(a, p, txRec)
                          \* Remove the current tx from the commit
                          \* queue of the address
                          /\ commQ' = [commQ EXCEPT ![p][a] = Tail(@)]
                          \* Remove transaction record from tCtl
                          /\ tCtl' = [tCtl EXCEPT ![p] = @ \ {txRec}]
                   /\ UNCHANGED <<comm, rcvBuf>>
                            
=============================================================================
\* Modification History
\* Last modified Mon Nov 23 21:47:53 CST 2020 by dninja
\* Created Wed Oct 21 12:25:12 CDT 2020 by dninja
