-------------------------------- MODULE User --------------------------------
EXTENDS     Naturals, Sequences

CONSTANT    Adr,
            Val
            
            
VARIABLE    (* 
                A counter (hash) variable is used to identify unique 
                transactions by increment.  It is not meant to be an
                ordering but only an identifier.  Transactions are ordered by
                the network itself, not by the user.
                
                In actual implementation a hash digest consisting of
                the operation with local timestamp will be used as a unique 
                transaction ID.
                
                Unforegability will be ensured by a signature of hash that
                will be shared with and validated by all Peers  
            *)
            hash
-----------------------------------------------------------------------------
UTypeInvariant ==   hash \in Nat

UInit ==            hash = 1 

(* 
    System is setup to accept transactions input by User to a Peer
    Validation of the transaction is assumed up to the Peer and thus
    abstracted to a sequence of affected storage addresses and values
*)
UReq ==     [
             aVals: {[adr: a, val: v] : a \in Adr, v \in Val}, 
             status: {"submit"}
            ]
=============================================================================
\* Modification History
\* Last modified Sat Nov 21 18:30:34 CST 2020 by dninja
\* Created Wed Sep 23 23:42:16 CDT 2020 by dninja
