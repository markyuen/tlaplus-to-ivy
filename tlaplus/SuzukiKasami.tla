---------------------------- MODULE SuzukiKasami ----------------------------
(***************************************************************************)
(* TLA+ specification of Suzuki and Kasami's distributed mutual exclusion  *)
(* algorithm that appeared in:                                             *)
(* I. Suzuki and T. Kasami: A Distributed Mutual Exclusion Algorithm. ACM  *)
(* Transactions on Computer Systems 3(4):344-349, 1985.                    *)
(***************************************************************************)
EXTENDS TLC, Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Utility functions to perform generic operations.                        *)
(***************************************************************************)
Fold(f(_, _), i, s) ==
   LET DFold[s0 \in SUBSET s] ==
      LET elt == CHOOSE e \in s0 : TRUE
      IN IF s0 = {} THEN i ELSE f(elt, DFold[s0 \ {elt}])
   IN DFold[s]

Range(f) == {f[x] : x \in DOMAIN f}

Max(x, y) == IF x > y THEN x ELSE y

MaxSet(s) == IF s = {} THEN 0 ELSE CHOOSE x \in s : \A y \in s : x >= y

-----------------------------------------------------------------------------
(***************************************************************************)
(* The parameter Node represents the set of nodes. The parameter           *)
(* MaxTokenSeq is used only for model checking in order to keep the state  *)
(* space finite.                                                           *)
(***************************************************************************)
CONSTANTS Node, MaxTokenSeq

ASSUME
   /\ IsFiniteSet(Node)
   /\ MaxTokenSeq \in Nat

VARIABLES
   nState,  \* local state of each node
   reqs,    \* set of all requests sent
   tokens,  \* set of all tokens sent
   crit     \* set of nodes in critical section

(***************************************************************************)
(* The type correctness predicate.                                         *)
(***************************************************************************)
ArrType == [Node -> Nat]

Requests ==
   [for  : Node,
    from : Node,
    seq  : Nat]

Tokens ==
   [for : Node,
    Q   : Seq(Node),
    LN  : ArrType,
    seq : Nat]

TypeOK ==
   /\ nState \in [Node -> [havePrivilege : BOOLEAN,
                           requesting    : BOOLEAN,
                           RN            : ArrType,
                           tokenSeq      : Nat]]
   /\ reqs \subseteq Requests
   /\ tokens \subseteq Tokens
   /\ crit \in SUBSET Node

(***************************************************************************)
(* Helper functions to create messages and retrieve tokens.                *)
(***************************************************************************)
CreateRequests(from, seq) ==
   {[for  |-> n,
     from |-> from,
     seq  |-> seq] : n \in Node \ {from}}

CreateToken(for, Q, LN, seq) ==
   [for |-> for,
    Q   |-> Q,
    LN  |-> LN,
    seq |-> seq]

GetCurrentToken(n) == CHOOSE t \in tokens : t.seq = nState[n].tokenSeq

(***************************************************************************)
(* The initial state predicate.                                            *)
(***************************************************************************)
ArrInit == [n \in Node |-> 0]

TokenInit == CHOOSE n \in Node : TRUE

Init ==
   /\ nState =
      [n \in Node |-> [havePrivilege |-> n = TokenInit,
                       requesting    |-> FALSE,
                       RN            |-> ArrInit,
                       tokenSeq      |-> IF n = TokenInit THEN 1 ELSE 0]]
   /\ reqs = {}
   /\ tokens = {CreateToken(TokenInit, <<>>, ArrInit, 1)}
   /\ crit = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Node n requests access to the critical section.                         *)
(*                                                                         *)
(* If n has privilege, then it only needs to adjust its state to reflect   *)
(* that it wants to enter the critical section. Otherwise, if n does not   *)
(* have privilege, then it needs to broadcast its request message to all   *)
(* other nodes after incrementing its sequence number, indicating how many *)
(* times n has broadcasted a request. A node may only have one outstanding *)
(* request at any given moment.                                            *)
(***************************************************************************)
Request(n) ==
   /\ ~nState[n].requesting
   /\ UNCHANGED <<tokens, crit>>
   /\ \/ /\ nState[n].havePrivilege
         /\ nState' = [nState EXCEPT ![n].requesting = TRUE]
         /\ UNCHANGED reqs
      \/ /\ ~nState[n].havePrivilege
         /\ nState' = [nState EXCEPT ![n].requesting = TRUE,
                                     ![n].RN = [@ EXCEPT ![n] = @ + 1]]
         /\ reqs' = reqs \cup CreateRequests(n, nState[n].RN[n] + 1)

(***************************************************************************)
(* Node n receives a request r and acknowledges it.                        *)
(*                                                                         *)
(* Node n will always update its internal RN state. If n has privilege and *)
(* is not requesting, then it will generate and send the next token to the *)
(* requester.                                                              *)
(***************************************************************************)
RetainOrReleaseOnReq(n, upRN, r, t) ==
   \/ /\ nState[n].requesting
      /\ nState' = [nState EXCEPT ![n].RN = upRN]
      /\ UNCHANGED tokens
   \/ /\ ~nState[n].requesting
      /\ upRN[r.from] = t.LN[r.from] + 1
      /\ nState' = [nState EXCEPT ![n].havePrivilege = FALSE,
                                  ![n].RN = upRN]
      /\ LET nextT == CreateToken(r.from, t.Q, t.LN, t.seq + 1)
         IN tokens' = tokens \cup {nextT}

RcvRequest(n, r) ==
   /\ r.for = n
   /\ UNCHANGED <<reqs, crit>>
   /\ LET upRN == [nState[n].RN EXCEPT ![r.from] = Max(@, r.seq)]
      IN \/ /\ ~nState[n].havePrivilege
            /\ nState' = [nState EXCEPT ![n].RN = upRN]
            /\ UNCHANGED tokens
         \/ /\ nState[n].havePrivilege
            /\ RetainOrReleaseOnReq(n, upRN, r, GetCurrentToken(n))

(***************************************************************************)
(* Node n receives a privilege message with token t and acknowledges it.   *)
(***************************************************************************)
RcvPrivilege(n, t) ==
   /\ t.for = n
   /\ t.seq > nState[n].tokenSeq
   /\ nState' = [nState EXCEPT ![n].havePrivilege = TRUE,
                               ![n].tokenSeq = t.seq]
   /\ UNCHANGED <<reqs, tokens, crit>>

(***************************************************************************)
(* Node n enters the critical section.                                     *)
(***************************************************************************)
Enter(n) ==
   /\ nState[n].havePrivilege
   /\ nState[n].requesting
   /\ crit' = crit \cup {n}
   /\ UNCHANGED <<nState, reqs, tokens>>

(***************************************************************************)
(* Node n exits the critical section and notifies other nodes.             *)
(*                                                                         *)
(* The token state will be updated to account for more recently received   *)
(* requests. If the resulting queue is non-empty, then the next token must *)
(* be generated and sent to the next node in the queue.                    *)
(*                                                                         *)
(* A subtle note on this implementation is that the current token should   *)
(* always be updated, since in the case that the updated queue is empty    *)
(* and the next token is not immediately generated, then the token's state *)
(* must be updated for other future steps. Always updating even if the     *)
(* next token is immediately generated also helps keep tokens consistent   *)
(* for defining invariants.                                                *)
(***************************************************************************)
GetUpdatedQ(n, Q, RN, upLN) ==
   LET qElems == Range(Q)
   IN Fold(LAMBDA e, r :
         IF /\ e \notin qElems
            /\ RN[e] = upLN[e] + 1
         THEN Append(r, e)
         ELSE r,
         Q,
         Node \ {n})

RetainOrReleaseAfterCrit(n, t) ==
   LET upLN == [t.LN EXCEPT ![n] = nState[n].RN[n]]
       upQ == GetUpdatedQ(n, t.Q, nState[n].RN, upLN)
       upT == CreateToken(t.for, upQ, upLN, t.seq)
   IN \/ /\ upQ = <<>>
         /\ nState' = [nState EXCEPT ![n].requesting = FALSE]
         /\ tokens' = (tokens \ {t}) \cup {upT}
      \/ /\ upQ # <<>>
         /\ nState' = [nState EXCEPT ![n].havePrivilege = FALSE,
                                     ![n].requesting = FALSE]
         /\ LET nextT == CreateToken(Head(upQ), Tail(upQ), upLN, t.seq + 1)
            IN tokens' = (tokens \ {t}) \cup {upT, nextT}

Exit(n) ==
   /\ n \in crit
   /\ crit' = crit \ {n}
   /\ UNCHANGED reqs
   /\ RetainOrReleaseAfterCrit(n, GetCurrentToken(n))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation.                                                    *)
(***************************************************************************)
RequestStep == \E n \in Node : Request(n)

RcvRequestStep == \E n \in Node, r \in reqs : RcvRequest(n, r)

RcvPrivilegeStep == \E n \in Node, t \in tokens : RcvPrivilege(n, t)

EnterStep == \E n \in Node : Enter(n)

ExitStep == \E n \in Node : Exit(n)

Next ==
   \/ RequestStep
   \/ RcvRequestStep
   \/ RcvPrivilegeStep
   \/ EnterStep
   \/ ExitStep

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness condition.                                                     *)
(*                                                                         *)
(* For any node n, if n requests to enter the critical section, then it    *)
(* must eventually gain access to the critical section. In order for this  *)
(* property to be satisfied by the specification, we need to add weak      *)
(* fairness to certain actions, otherwise the specification allows for     *)
(* infinite stuttering, preventing a node from entering the critical       *)
(* section even if it is enabled to do so.                                 *)
(***************************************************************************)
vars == <<nState, reqs, tokens, crit>>

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ WF_vars(RcvRequestStep)
   /\ WF_vars(RcvPrivilegeStep)
   /\ WF_vars(EnterStep)
   /\ WF_vars(ExitStep)

ReqLeadsToCrit == \A n \in Node : nState[n].requesting ~> n \in crit

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
Mutex ==
   (************************************************************************)
   (* The main safety property of mutual exclusion. Affirms that only one  *)
   (* node may be in the critical section at any given time.               *)
   (************************************************************************)
   \A n, m \in crit : n = m

SinglePrivilege ==
   (************************************************************************)
   (* Affirms that only one node may have privilege at any given time.     *)
   (************************************************************************)
   LET hasPrivilege == {n \in Node : nState[n].havePrivilege}
   IN \A n, m \in hasPrivilege : n = m

AllowedInCrit ==
   (************************************************************************)
   (* Affirms that any node n in the critical section must have privilege  *)
   (* and be requesting. In conjunction with the below token-based         *)
   (* invariants, further affirms that node n has the latest token.        *)
   (************************************************************************)
   \A n \in crit : /\ nState[n].havePrivilege
                   /\ nState[n].requesting

UniqueTokens ==
   (************************************************************************)
   (* Affirms that all token sequence numbers are unique, and that current *)
   (* node token sequence numbers are unique, bar the initial node token   *)
   (* sequence number of 0, which is shared from the initial state.        *)
   (************************************************************************)
   LET tokenSeqT == Fold(LAMBDA e, r : Append(r, e.seq), <<>>, tokens)
       tokenSeqN ==
      Fold(LAMBDA e, r :
         IF nState[e].tokenSeq # 0
         THEN Append(r, nState[e].tokenSeq)
         ELSE r,
         <<>>,
         Node)
   IN /\ Len(tokenSeqT) = Cardinality(tokens)
      /\ Len(tokenSeqT) = Cardinality(Range(tokenSeqT))
      /\ Len(tokenSeqN) = Cardinality(Range(tokenSeqN))

CorrespondingTokens ==
   (************************************************************************)
   (* Affirms that every current node token corresponds to a token, once   *)
   (* again bar token sequence number 0. In conjunction with the above     *)
   (* UniqueTokens invariant, further affirms that the current privileged  *)
   (* node's token can be uniquely identified through token sequence       *)
   (* number alone, allowing us to utilize the helper function             *)
   (* GetCurrentToken(n), once we know that node n has privilege.          *)
   (************************************************************************)
   \A n \in Node :
      \/ /\ n # TokenInit
         /\ nState[n].tokenSeq = 0
      \/ \E t \in tokens :
         /\ nState[n].tokenSeq = t.seq
         /\ n = t.for

CurrentPrivilegeLatestToken ==
   (************************************************************************)
   (* Affirms that privilege can only belong to one node at a time, and    *)
   (* that the privileged node's token sequence number is the most recent  *)
   (* (i.e. the largest of all token sequence numbers). Otherwise, if no   *)
   (* node currently has privilege, then that means the privilege message  *)
   (* carrying the latest token is in transit, and this token's sequence   *)
   (* number is larger than any current node's token sequence number.      *)
   (************************************************************************)
   LET hasPrivilege == {n \in Node : nState[n].havePrivilege}
       maxTokenSeq == MaxSet({t.seq : t \in tokens})
       maxNodeTokenSeq == MaxSet({nState[n].tokenSeq : n \in Node})
   IN IF Cardinality(hasPrivilege) = 1
      THEN
         LET n == CHOOSE n \in hasPrivilege : TRUE
             t ==
            CHOOSE t \in {t \in tokens : t.seq = nState[n].tokenSeq} : TRUE
         IN /\ nState[n].tokenSeq = maxNodeTokenSeq
            /\ t.seq = maxTokenSeq
      ELSE
         /\ Cardinality(hasPrivilege) = 0
         /\ maxTokenSeq > maxNodeTokenSeq

GoodTokenQueues ==
   (************************************************************************)
   (* Affirms that all token queues only have up to one instance of each   *)
   (* node other than themself.                                            *)
   (************************************************************************)
   \A t \in tokens : /\ Len(t.Q) < Cardinality(Node)
                     /\ t.for \notin Range(t.Q)

NoRequestToSelf ==
   (************************************************************************)
   (* Affirms that no request is sent to oneself.                          *)
   (************************************************************************)
   \A r \in reqs : r.for # r.from

NoConsecutivePrivilege ==
   (************************************************************************)
   (* Affirms that no consecutive tokens belong to the same node. I.e.,    *)
   (* that no privilege message is sent to oneself.                        *)
   (************************************************************************)
   \A t \in {t \in tokens : t.seq > 1} :
      LET prev == CHOOSE prev \in tokens : prev.seq = t.seq - 1
      IN t.for # prev.for

Good ==
   (************************************************************************)
   (* A conjunction of all invariants declared.                            *)
   (************************************************************************)
   /\ Mutex
   /\ SinglePrivilege
   /\ AllowedInCrit
   /\ UniqueTokens
   /\ CorrespondingTokens
   /\ CurrentPrivilegeLatestToken
   /\ GoodTokenQueues
   /\ NoRequestToSelf
   /\ NoConsecutivePrivilege

THEOREM Spec => []TypeOK /\ []Good

-----------------------------------------------------------------------------
(***************************************************************************)
(* A state constraint that is useful for validating the specification      *)
(* using finite-state model checking.                                      *)
(***************************************************************************)
TokenConstraint == \A t \in tokens : t.seq < MaxTokenSeq

=============================================================================
