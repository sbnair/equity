------------------------------- MODULE Borda -------------------------------
EXTENDS FiniteSets, Naturals, Sequences

          \* Summation recursive operator
Sum(S) == LET F[T \in SUBSET S] ==
            IF T = {} THEN 0
            ELSE LET x == CHOOSE x \in T: TRUE
                IN x +  F[T\{x}]
          IN F[S]


                      
                      (*******************************************************)
                      (* Borda Count is used in this spec as it has low      *)
                      (* computational cost vs other Kemeny Median methods   *)
                      (* while still providing decent results                *)
                      (*******************************************************)
                    (* vote.orig == Peer                                     *)
                    (* vote.hashs == Seq(Nat) Sequence of op hash ids        *)
                    (* r1Counts == Seq(Nat \X {Nat}) mapping of hash to      *) 
                    (* Borda rank                                            *)
                    (*********************************************************)
                                        
BordaSets(Votes) ==     LET F[V \in SUBSET Votes] ==
                          IF V = {} THEN << >> ELSE 
                            LET vote == CHOOSE vote \in V : TRUE \* 1st LET
                            IN LET G[i \in 0 .. Len(vote)] == \* 1st IN
                              IF i = 0 THEN F[V \ {vote}]
                              ELSE LET \* 2nd LET
                                
                        (*****************************************************)
                        (* Simple Borda score that is                        *)
                        (* weighted based on order received by peer          *)
                        (*                                                   *)
                        (* Note that to reduce calculations, score is not    *)
                        (* updated after operations are removed that have    *)
                        (* not reached all of peers before the round         *)
                        (*****************************************************)
                        
                                    bScore == Len(vote.hashs) - (i - 1)
                        
                        (*****************************************************)
                        (* Borda scores for the hash                         *)
                        (*****************************************************)
                        
                                    bScores == SelectSeq(
                                                 G[i-1],
                                                 LAMBDA c : c[1] = 
                                                 vote.hashs[i]
                                               )
                        \* Check if there are no bScores for the hash              
                                IN IF bScores = {} \* 2rd IN
                        \* Then create bScores set for hash and set
                        \* first member of the set to the bScore 
                                  THEN Append(
                                         G[i-1], 
                                         <<vote.hashs[i], {bScore}>>
                                       )
                        \* Else place bScore element for the
                        \* hash at this address to the current set
                                  ELSE LET H[j \in 1 .. Len(G[i-1])] == \* 4th LET
                                      IF G[i-1][j][1] = vote[2]
                                      THEN UNION {G[i-1][j][2], bScore}
                                      ELSE H[j-1]
                                    IN H[Len(G[i-1])] \* 4th IN
                            IN G[Len(vote)] \* 3rd IN
                      IN F[Votes]           

BordaCull(bSets, Peer) ==  SelectSeq(bSets, LAMBDA x : Cardinality(x[2]) =
                                                 Cardinality(Peer))  
                     


                      \* Insert Sort Greatest to Least
BordaRank(bSets) ==     LET f[i \in 1 .. Len(bSets)] ==
                          IF i = 1 THEN << >> ELSE  
                          LET g[j \in 0 .. i-1] ==
                            IF i = 0 THEN f[i-1] ELSE
                              IF Sum(g[i-1][2]) > Sum(g[j-1][2]) THEN
                                 SubSeq(g[j-1], 1, j-1) \o g[j-1][i] \o
                                 SubSeq(g[j-1], j+1, i-1) \o
                                 SubSeq(g[j-1], i+1, Len(g[j-1]))
                              ELSE IF Sum(g[i-1][2]) = Sum(g[j-1][2])
                                THEN 
                                \* To solve tie then lexigraphical sort
                                /\ g[i-1][1] > g[j-1][i]
                                /\ SubSeq(g[j-1], 1, j-1) \o g[j-1][i] \o
                                   SubSeq(g[j-1], j+1, i-1) \o
                                   SubSeq(g[j-1], i+1, Len(g[j-1]))
                                ELSE j[i-1]
                          IN g[Len(bSets)] 
                        IN f[Len(bSets)]

=============================================================================
\* Modification History
\* Last modified Sun Nov 22 20:17:45 CST 2020 by dninja
\* Created Wed Oct 28 10:56:18 CDT 2020 by dninja
