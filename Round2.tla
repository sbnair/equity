------------------------------- MODULE Round2 -------------------------------
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT    Adr,
            Peer

VARIABLE    aCtl,
            r2,
            rcvBuf,
            sndBuf
            
-----------------------------------------------------------------------------            
R2Invariant ==      /\ r2 \in [Peer -> [Adr -> {[
                                                 orig: Peer, 
                                                 hashs: Seq(Nat)
                                               ]}]]
                    
Round2Init ==       /\ r2 = [p \in Peer |-> [a \in Adr |-> {}]]
                                      
                    (*******************************************************)
                    (* Round 2 Receive: each peer receives calculated      *)
                    (* Kemeny Median (Borda Count) ranking representing    *)
                    (* order of transactional updates for this address     *)
                    (*******************************************************)
                    
Round2Rcv(p) ==     /\ Len(rcvBuf[p]) > 0 \* Receive buffer is not empty
                    \* Receive buffer is set to submit
                    /\ Head(rcvBuf[p]).msg.stg = "round 2"
                    /\ LET vote == Head(rcvBuf[p])
                       IN LET msg == vote.msg
                              route == vote.route IN
                            LET v == CHOOSE v \in r2[p][msg.adr] : 
                                             v.orig = route.orig
                            IN  \* The peer has not voted yet in Round 2
                              /\ v = {}
                              \* Add Round 2 vote to r2 accounting function
                              /\ r2' = [r2 EXCEPT ![p][msg.adr] = 
                                           UNION {r2[p][msg.adr], 
                                                  [
                                                   orig  |-> route.orig, 
                                                   hashs |-> msg.hashs
                                                  ]}]
                              \* Remove Round 2 vote from rcvBuf'
                              /\ rcvBuf' = [rcvBuf EXCEPT ![p] = Tail(@)]
                    /\ UNCHANGED <<aCtl, sndBuf>>
                    
                    
                    (******************************************************)
                    (* SetCount: confirms that Round 1 votes by all peers *)
                    (* are the same                                       *)
                    (******************************************************)
                    
SetCount(r2Votes) == LET s == CHOOSE s \in r2Votes : TRUE
                     IN Cardinality({t \in r2Votes : t.hashs = s.hashs}) 
                 
                 
                    (******************************************************)
                    (* Round 2 is only confirming that all votes are the  *)
                    (* same.  This is superfluous as the spec             *)
                    (* already is specified to ensure all votes are the   *)
                    (* some.  Unexpected behavior will be caught.         *)
                    (******************************************************)

Round2Snd(p, a) ==  /\ aCtl[p][a] = "round 2"
                    /\ LET r2Votes == r2[p][a]
                       IN  /\ SetCount(r2Votes) = Cardinality(Peer)
                           \* Choose a sequence of hash to use as commit
                           \* sequence and then broadcast
                           /\ LET commit == CHOOSE s \in r2Votes : TRUE
                              IN  sndBuf' = [sndBuf EXCEPT ![p] = 
                                             Append(@, 
                                                    [
                                                     adrs  |-> a,
                                                     hashs |-> commit.hashs, 
                                                     stg   |-> "commit"
                                                    ])]
                           /\ aCtl' = [aCtl EXCEPT ![p][a] = "commit"]
                           /\ r2' = [r2 EXCEPT ![p][a] = {}]
                           /\ UNCHANGED <<rcvBuf>>

=============================================================================
\* Modification History
\* Last modified Mon Nov 23 21:47:43 CST 2020 by dninja
\* Created Wed Oct 21 13:37:05 CDT 2020 by dninja
