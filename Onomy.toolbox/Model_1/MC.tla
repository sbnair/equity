---- MODULE MC ----
EXTENDS Onomy, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3, a4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT definitions Peer
const_1606191254481106000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions Adr
const_1606191254481107000 == 
{a1, a2, a3, a4}
----

\* MV CONSTANT definitions Val
const_1606191254481108000 == 
{v1, v2, v3}
----

\* SYMMETRY definition
symm_1606191254481109000 == 
Permutations(const_1606191254481108000)
----

\* CONSTANT definitions @modelParameterConstants:1MaxReq
const_1606191254481110000 == 
10
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1606191254481111000
----
\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_1606191254481112000
----
=============================================================================
\* Modification History
\* Created Mon Nov 23 22:14:14 CST 2020 by dninja
