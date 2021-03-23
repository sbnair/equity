------------------------------- MODULE Round1 -------------------------------
EXTENDS FiniteSets, Naturals, Sequences, Borda

CONSTANTS   Adr,
            Peer
            

VARIABLE    aCtl,
            r1,
            rcvBuf,
            sndBuf
            
-----------------------------------------------------------------------------            
R1Invariant ==      /\ r1 \in [Peer -> [Adr -> {[
                                                 orig: Peer, 
                                                 hashs: Seq(Nat)
                                                ]}]]
                    
Round1Init ==       /\ r1 = [p \in Peer |-> [a \in Adr |-> {}]]

                    
                    (*******************************************************)
                    (* Round 1 Receive: each peer receives votes for next  *)
                    (* update for an address                               *)
                    (*******************************************************)
                    
Round1Rcv(p) ==     /\ Len(rcvBuf[p]) > 0 \* Receive buffer is not empty
                    \* Receive buffer is set to submit
                    /\ Head(rcvBuf[p]).msg.stg = "round 1"
                    /\ LET vote == Head(rcvBuf[p])
                       IN LET msg == vote.msg
                              route == vote.route IN
                            LET v == CHOOSE v \in r1[p][msg.adr] : 
                                             v.orig = route.orig
                            IN  \* The peer has not voted yet in Round 1
                              /\ v = {}
                              \* Add Round 1 vote to r1 accounting function
                              /\ r1' = [r1 EXCEPT ![p][msg.adr] = 
                                           UNION {r1[p][msg.adr], 
                                                  [
                                                   orig  |-> route.orig, 
                                                   hashs |-> msg.hashs
                                                  ]}]
                              /\ rcvBuf' = [rcvBuf EXCEPT ![p] = Tail(@)]
                    /\ UNCHANGED <<aCtl, sndBuf>>


                    (*******************************************************)
                    (* Round 1 Send: each peer sends vote for round 1      *)
                    (*                                                     *)
                    (* Round 1 vote is the Kemeny Median (Borda Ranking)   *)
                    (* of tx received that all peers have seen.  The       *)
                    (* Kemeny Median determines the order in which         *)
                    (* transactions affecting this specific address were   *)
                    (* received by the network                             *)
                    (*                                                     *)
                    (* Each peer, in this version of the protocol, should  *)
                    (* submit the same Round 1 vote or Kemeny Ranking to   *)
                    (* all other nodes                                     *)
                    (*******************************************************)
                    
Round1Snd(p, a) ==  /\ aCtl[p][a] = "round 1" 
                    /\ LET  r1Votes == r1[p][a]
                            bSets == BordaSets(r1[p][a])
                       IN   /\ Cardinality(r1Votes) = Cardinality(Peer)
                            \* Cull tx hash that are not in all votes
                            \* Then sort Borda Counts for ranking
                            /\ LET round1Seq == BordaRank(
                                                BordaCull(bSets, Peer))
                               IN  sndBuf' = [sndBuf EXCEPT ![p] = 
                                              Append(@, 
                                                     [
                                                       adr   |-> a,
                                                       hashs |-> round1Seq,
                                                       stg   |-> "round 2"
                                                     ])]
                            /\ aCtl' = [aCtl EXCEPT ![p][a] = "round 2"]
                            /\ r1' = [r1 EXCEPT ![p][a] = {}]
                            /\ UNCHANGED <<rcvBuf>>

=============================================================================
\* Modification History
\* Last modified Mon Nov 23 21:47:19 CST 2020 by dninja
\* Created Sun Oct 11 22:18:09 CDT 2020 by dninja
