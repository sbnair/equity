------------------------------ MODULE Storage ------------------------------
EXTENDS Naturals, Sequences

CONSTANT    Adr,
            Peer,
            Val

VARIABLE    store

-----------------------------------------------------------------------------
TypeInvariant ==        /\ store \in [Peer -> [Adr -> [val: Val, 
                                                       nonce: Nat, 
                                                       hash: Nat]]]

NoVal ==                CHOOSE v : v \notin Val

StorageInit ==          (* Initialize all storage addresses NoVal at each nonce *) 
                        /\ store = [p \in Peer |-> [a \in Adr |-> 
                                   [val |-> NoVal, nonce |-> 0, hash |-> 0]]]
=============================================================================
\* Modification History
\* Last modified Tue Nov 17 20:28:24 CST 2020 by dninja
\* Created Wed Sep 23 10:07:18 CDT 2020 by dninja
