-------------------------- MODULE NetworkInterface --------------------------
EXTENDS     Naturals, FiniteSets, Sequences

VARIABLE    netInt,      (* Network Interface *)
            sndBuf,
            rcvBuf

CONSTANT    Peer,       (* Set of peers *)
            Adr,        (* Set of addresses *)
            Val         (* Set of memory values *)
           

\* ASSUME \A p, d, niOld, niNew :  /\ Send(p, d, niOld, niNew) /in BOOLEAN
\*                                /\ Reply(p, d, niOld, niNew) /in BOOLEAN                        
-----------------------------------------------------------------------------
Stage ==  {
            "round 1",
            "round 2",
            "commit"
          }


           (****************************************************************)
           (* Messages are split between transaction submission and stages *)
           (* of ordering, consensus and commit.  Submission involves one  *)
           (* transaction with potentially many affected address.  The     *)
           (* other stages involve a single address, but potentially many  *)
           (* transactions.                                                *)
           (****************************************************************)

Message == [ 
            hash: Nat, 
            aVals : {[adr: Adr, val: Val]}, 
            step : "submit"
           ]
             \cup
           [
            adr : Adr, 
            hashs: Seq(Nat),
            stg : Stage
           ]

Routing == [
            orig : Peer,
            dest : Peer
           ]

Packet  == [
            route : Routing,
            msg : Message
           ]


                    (*******************************************************)
                    (* Specify all types of msgs that may be transmitted   *)
                    (* between peers.                                      *)
                    (*                                                     *)
                    (* Internet is modelled as an unordered set of msgs    *)
                    (*******************************************************)

NetInvariant ==     /\ netInt \in [Peer -> {Packet}]
                    \* Each peer has a buffer for all msgs received
                    /\ rcvBuf \in [Peer -> Seq(Packet)]
                    \* Each peer has a send Buffer for all msgs sent
                    /\ sndBuf \in [Peer -> Seq(Message)]
                                                   

                        
NetInit ==          /\ netInt = [p \in Peer |-> {}]
                    /\ rcvBuf = [p \in Peer |-> <<>>]
                    /\ sndBuf = [p \in Peer |-> <<>>]
                    
-----------------------------------------------------------------------------
                    
                    (*******************************************************)
                    (* Broadcasts message to network interface addressed   *)
                    (* to all Peer except Peer sending the message         *)
                    (*******************************************************) 

Broadcast(p, msg) ==  LET F[subPeer \in SUBSET Peer] ==
                        IF subPeer = {} THEN netInt
                        ELSE LET n == CHOOSE n \in subPeer : TRUE IN
                          IF n # p THEN 
                            LET pkt == [
                                        route |-> [orig |-> p, dest |-> n],
                                        msg |-> msg
                                       ]
                            IN [F[subPeer \ {n}] EXCEPT ![n] = 
                                                 UNION{@, {pkt}}]
                          ELSE F[subPeer \ {n}]
                      IN F[Peer]
                    
                  
                    (*******************************************************)
                    (* Peer p sends all peers a messages in Peer except    *)
                    (* itself.                                             *)
                    (*******************************************************)
                    
Send(p) ==          \* Enabling condition: Is send buffer non-empty?
                    /\ Len(sndBuf[p]) > 0
                    \* Broadcast head of send buffer to network
                    /\ LET msg == Head(sndBuf[p]) IN
                        /\ netInt' = Broadcast(p, msg)
                        \* Place head of send buffer in the receive buffer of
                        \* sending peer
                        /\ LET pkt == [
                                       route |-> [orig |-> p, dest |-> p],
                                       msg |-> msg
                                      ] 
                           IN rcvBuf' = [rcvBuf EXCEPT ![p] = Append(@, pkt)]
                    \* Replace send buffer with tail
                    /\ sndBuf' = [sndBuf EXCEPT ![p] = Tail(@)]


                    (*******************************************************)
                    (* Peer p receives msg from the network into it's own  *)
                    (* receive buffer                                      *)
                    (*******************************************************)
                    
Rcv(p) ==           \* Enabling Condition: Msgs for Peer on network 
                    /\ Cardinality(netInt[p]) > 0
                    \* Network msgs are assumed unordered, so Peer CHOOSES on
                    /\ LET pkt == CHOOSE pkt \in netInt[p] : TRUE
                       IN /\ rcvBuf' = [rcvBuf EXCEPT ![p] = Append(@, pkt)] 
                          /\ netInt' = [netInt EXCEPT ![p] = @ \ {pkt}]
                    /\ UNCHANGED sndBuf
=============================================================================
\* Modification History
\* Last modified Mon Nov 23 12:28:26 CST 2020 by dninja
\* Created Mon Sep 21 10:35:10 CDT 2020 by dninja
