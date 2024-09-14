---- MODULE POFifo ----
(*************************************************)
(* From Lamport's Science of Concurrent Programs *)
(*************************************************)

EXTENDS Sequences, Naturals, TLC

CONSTANTS EnQers, DeQers, Data, Ids

Done == CHOOSE Done : Done \notin Data
Busy == CHOOSE Busy : Busy \notin Data
NonElt == CHOOSE NonElt : NonElt \notin (Data \X Ids)

VARIABLES
    (* external variables *)
    enq,deq,

    (* internal variables *)
    elts,before,adding,

    (* auxiliary variables *)
    p,pg,eb,s,queueBar,enqInnerBar


\* The ultimate mapping to the queue that queueBar needs to eventually converge on
qBar == pg \o eb


beingAdded == {adding[e] : e \in EnQers} \ {NonElt}

Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq \in [DeQers -> Data]
        /\ elts = {}
        /\ before = {}
        /\ adding = [e \in EnQers |-> NonElt]

InitP == /\ Init
         /\ p = <<>>
         /\ pg = <<>>
         /\ eb = <<>>
         /\ s = [e \in EnQers \cup DeQers |-> <<0,"">>]
         /\ queueBar = <<>>
         /\ enqInnerBar = [e \in EnQers |-> Done]

Range(seq) == {seq[i]: i \in DOMAIN seq}
IndexOf(seq, val) == CHOOSE i \in DOMAIN seq : seq[i]=val

BeginEnq(e) == /\ enq[e] = Done
               /\ \E D \in Data : \E id \in {i \in Ids : <<D,i>> \notin (elts \union beingAdded)} :
                    LET w == <<D,id>>
                    IN /\ enq' = [enq EXCEPT ![e]=D]
                       /\ elts' = elts \union {w}
                       /\ before' = before \union {<<el,w>> : el \in (elts \ beingAdded)}
                       /\ adding' = [adding EXCEPT ![e]= w ]
               /\ UNCHANGED deq


Prefix(seq, n) == SubSeq(seq, 1, n)

IsBefore(e1,e2) == <<e1,e2>> \in before

(**************************************)
(* Invariants for seq that encodes pg *)
(**************************************)
\* Q1. Every datum in pg is in elts.
Q1(pgp, items) == Range(pgp) \subseteq items

\* Q2. No datum appears twice in pg.
Q2(pgp) == \A i,j \in DOMAIN pgp : pgp[i]=pgp[j] => i=j

\* Q3. For each i ∈ 1..Len(pg) and each datum u ∈ elts, if u ≺ pg(i) then u = pg (j) for some j ∈ 1..(i − 1).
Q3(pgp, items) == \A i \in DOMAIN pgp, u \in items :
                    IsBefore(u, pgp[i]) => \E j \in 1..i-1 : u = pgp[j]

PgInv(pgp, items) == /\ Q1(pgp, items)
                     /\ Q2(pgp)
                     /\ Q3(pgp, items)


(* The longest prefix of pp that satisfies the PgInv invariant *)
LongestPrefix(pp, items) ==
    IF \E n \in DOMAIN pp : PgInv(Prefix(pp, n), items)
    THEN LET n == CHOOSE n \in DOMAIN pp : /\ PgInv(Prefix(pp, n), items)
                                            /\ \/ n = Len(pp)
                                               \/ ~PgInv(Prefix(pp, n+1), items)
          IN Prefix(pp, n)
    ELSE <<>>

(**************************************************************************************************)
(* Following each BeginEnqP step such that Len(pg')>Len(pg) (which implies eb=<<>>), s adds       *)
(* Len(pg') − Len(pg) stuttering steps. While there are k more of those stuttering steps left to  *)
(* be executed, queueBar equals the sequence obtained by removing the last k elements of qBar.    *)
(**************************************************************************************************)
BeginEnqP(e) == LET w == adding'[e]
                 IN /\ \A ee \in EnQers \ {e} : s[ee][1] = 0
                    /\ \/ /\ s[e][1] = 0
                          /\ \A d \in DeQers : s[d][1] = 0
                          /\ BeginEnq(e)
                          /\ \E el \in Data \X Ids : p' = Append(p, el)
                          /\ pg' = IF eb = <<>>
                                   THEN LongestPrefix(p', elts')
                                   ELSE pg
                          /\ s' = IF eb = <<>> THEN [s EXCEPT ![e] = <<Len(pg')-Len(pg),"BeginEnq">>] ELSE s
                          /\ enqInnerBar' = [enqInnerBar EXCEPT ![e]=Busy]
                          /\ UNCHANGED <<eb,queueBar>>
                       \/ LET k==s[e][1] IN
                          /\ k>0
                          /\ s[e][2]="BeginEnq"
                          /\ queueBar' = Prefix(qBar,Len(qBar)-(k-1))
                          /\ s' = [s EXCEPT ![e] = <<k-1,"BeginEnq">>]
                          /\ enqInnerBar' = LET v == qBar[Len(qBar)-(k-1)]
                                             IN IF \E ee \in EnQers : adding[ee]=v
                                                THEN [enqInnerBar EXCEPT ![CHOOSE ee \in EnQers : adding[ee]=v]=Done]
                                                ELSE enqInnerBar
                          /\ UNCHANGED <<adding,before,deq,elts,enq,p,eb,pg>>

EndEnq(e) == /\ enq[e] # Done
             /\ enq' = [enq EXCEPT ![e]=Done]
             /\ adding' = [adding EXCEPT ![e]=NonElt]
             /\ UNCHANGED <<deq, elts, before, p>>

(*************************************************************************************************************)
(* s adds a stuttering step before each EndEnqP step that appends an element w to eb (and hence to qBar).    *)
(* Immediately after that stuttering step, queueBar equals qBar \o << w >>.                                  *)
(*************************************************************************************************************)
EndEnqP(e) == LET addingP == [adding EXCEPT ![e]=NonElt]
                  beingAddedP == {addingP[ee] : ee \in EnQers} \ {NonElt}
                  w == adding[e]
                  (* There is a queued element which is not in pg, which means it must precede w*)
                  IsBlocked == \E u \in elts : u \notin beingAddedP /\ u \notin Range(pg) 
              IN
          /\ \A d \in DeQers : s[d][1] = 0
          /\ \A ee \in EnQers \ {e} : s[ee][1] = 0
                (* value has previously been added to queue, no stuttering step required *)
          /\ \/ /\ s[e][1] = 0
                /\ enqInnerBar[e] = Done
                /\ EndEnq(e)
                /\ UNCHANGED <<eb,s,pg,queueBar,enqInnerBar>>
                (* add a stuttering step which appends a value to eb (and, consequently, queueBar) *)
             \/ /\ s[e][1] = 0
                /\ ENABLED EndEnq(e) 
                /\ enqInnerBar[e] = Busy
                /\ w \notin Range(pg) (* w has not previously been identified as a dequeueable value *)
                /\ IsBlocked
                /\ s' = [s EXCEPT ![e] = <<1,"EndEnq">>]
                /\ eb' = Append(eb, w)
                /\ queueBar' = Append(qBar, w)
                /\ enqInnerBar' = [enqInnerBar EXCEPT ![e]=Done]
                /\ UNCHANGED  <<enq,deq,elts,before,adding,p,pg>>
                (* final step after stuttering *)
             \/ /\ s[e] = <<1,"EndEnq">>
                /\ s' = [s EXCEPT ![e] = <<0,"EndEnq">>]
                /\ EndEnq(e)
                /\ UNCHANGED <<eb,pg,queueBar,enqInnerBar>>

BeginDeq(d) == /\ deq[d] # Busy
               /\ deq' = [deq EXCEPT ![d]=Busy]
               /\ UNCHANGED <<enq, elts, before, adding>>

BeginDeqP(d) == /\ BeginDeq(d)
                /\ \A e \in EnQers : s[e][1] = 0
                /\ UNCHANGED <<p,pg,eb,s,queueBar,enqInnerBar>>


EndDeq(d) == /\ deq[d] = Busy
             /\ pg # <<>>
             /\ \E el \in elts:
               /\ \A el2 \in elts: ~(IsBefore(el2,el))
               /\ elts' = elts \ {el}
               /\ deq' = [deq EXCEPT ![d]=el[1]]
               /\ before' = before \intersect (elts' \X elts')
               /\ elts' = elts \ {p[1]}
               /\ p' = Tail(p)
               /\ pg' = Tail(pg)
             /\ UNCHANGED <<enq, adding, eb>>

(***********************************************************************************)
(* s adds a single stuttering step before each EndDeq step.                        *)
(* The value of queueBar equals Tail(qBar) immediately after that stuttering step. *)
(***********************************************************************************)
EndDeqP(d) ==  \/ /\ ENABLED EndDeq(d)
                  /\ \A e \in EnQers : s[e][1] = 0
                  /\ \A dd \in DeQers \ {d} : s[dd][1] = 0
                  /\ s[d][1] = 0
                  /\ s' = [s EXCEPT ![d] = <<1,"EnqDeq">>]
                  /\ queueBar' = Tail(qBar)
                  /\ UNCHANGED <<enq,deq,elts,before,adding,p,pg,eb,enqInnerBar>>
               \/ /\ s[d] = <<1,"EnqDeq">>
                  /\ s' = [s EXCEPT ![d]= <<0,"EnqDeq">>]
                  /\ EndDeq(d)
                  /\ UNCHANGED <<queueBar,enqInnerBar>>

NextP == \/ \E e \in EnQers : \/ BeginEnqP(e)
                              \/ EndEnqP(e)
         \/ \E d \in DeQers :  \/ BeginDeqP(d)
                               \/ EndDeqP(d)


v == <<enq,deq,elts,before,adding,p,pg,eb,s,queueBar,enqInnerBar>>
Spec == InitP /\ [][NextP]_v /\ WF_v(\E d \in DeQers: EndDeqP(d))

(********************************************************************************************************************************)
(* The value of enqInnerBar(e) for an enqueuer e should equal Done except when adding[e] equals the datum that e is enqueueing, *)
(* and that datum is not yet in queueBar. This means that enqInnerBar can be defined in terms of adding and queueBar.           *)
(********************************************************************************************************************************)
\* enqInnerBar == [e \in EnQers |-> LET u == adding[e] IN IF u # NonElt /\ u \notin Range(queueBar) THEN Busy ELSE Done]

(**********************************************************************************************************************************)
(* The value of deqInnerBar(d) for a dequeuer d should equal the value of deq[d] except between when d has removed the first      *)
(* element of queueBar (by executing the stuttering step added in case 1) and before the subsequent EndDeqP(d) step has occurred. *)
(* In that case, deq[d] should equal qBar(1). It’s therefore easy to define deqInnerBar as a state function of IPOFifo if the     *)
(* value of the stuttering variable s added in case 1 contains the value of d for which the following EndPODeqpqs(d) step is to   *)
(* be performed.                                                                                                                  *)
(**********************************************************************************************************************************)
deqInnerBar == [d \in DeQers |-> IF s[d] = <<1,"EnqDeq">> THEN qBar[1][1] ELSE deq[d]]

queue == [i \in DOMAIN queueBar |-> queueBar[i][1]]

Fifo == INSTANCE IFifo WITH
            enqInner <- enqInnerBar,
            deqInner <- deqInnerBar,
            NoData <- Busy

Linearizability == Fifo!Spec

Alias == [
    enq |-> enq,
    deq |-> deq,
    enqInnerBar |-> enqInnerBar,
    deqInnerBar |-> deqInnerBar,
    queueBar |-> queueBar,
    queue |-> queue,
    qBar |-> qBar,
    elts |-> elts,
    before |-> before,
    adding |-> adding,
    p |-> p,
    pg |-> pg,
    eb |-> eb,
    s |-> s,
    beingAdded |-> beingAdded]
====