---- MODULE IPOFifo ----
(*************************************************)
(* From Lamport's Science of Concurrent Programs *)
(*************************************************)

EXTENDS Sequences, Naturals

CONSTANTS EnQers, DeQers, Data, Ids

Done == CHOOSE Done : Done \notin Data
Busy == CHOOSE Busy : Busy \notin Data

VARIABLES
    (* external variables *)
    enq,deq,

    (* internal variables *)
    elts,before,adding,
    (* auxiliary variables *)
    p,pg,eb,s,queueBar

v == <<enq,deq,elts,before,adding,p,pg,eb,s,queueBar>>

\* The ultimate mapping to the queue that queueBar needs to eventually converge on
qBar == pg \o eb

NonElt == CHOOSE NonElt : NonElt \notin (Data \X Ids)

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

Range(seq) == {seq[i]: i \in DOMAIN seq}
IndexOf(seq, val) == CHOOSE i \in DOMAIN seq : seq[i]=val

(******************************************************)
(* Append w to seq, as well as other valid values     *)
(******************************************************)
RECURSIVE Augment(_, _)
Augment(seq, w) ==
    IF \E x \in Range(seq) : /\ IndexOf(seq, x) > IndexOf(seq, w)
                             /\ x \in elts
    THEN Augment(Append(seq, w), CHOOSE x \in Range(seq) : IndexOf(seq, x) > IndexOf(seq, w) /\ x \in elts)
    ELSE Append(seq, w)


BeginEnq(e) == /\ enq[e] = Done
               /\ \E D \in Data : \E id \in {i \in Ids : <<D,i>> \notin (elts \union beingAdded)} :
                    LET w == <<D,id>>
                    IN /\ enq' = [enq EXCEPT ![e]=D]
                       /\ elts' = elts \union {w}
                       /\ before' = before \union {<<el,w>> : el \in (elts \ beingAdded)}
                       /\ adding' = [adding EXCEPT ![e]= w ]
               /\ UNCHANGED deq

(**************************************************************************************************)
(* Following each BeginPOEnq pq step such that Len(pg')>Len(pg) (which implies eb=<<>>), s adds   *)
(* Len(pg') − Len(pg) stuttering steps. While there are k more of those stuttering steps left to  *)
(* be executed, queueBar equals the sequence obtained by removing the last k elements of qBar.    *)
(**************************************************************************************************)
BeginEnqP(e) == LET w == adding'[e]
                 IN \/ /\ s[e][1]=0
                       /\ BeginEnq(e)
                       /\ \E el \in Data \X Ids : p' = Append(p, el)
                       /\ pg' = IF eb = <<>> THEN Augment(pg, w) ELSE pg
                       /\ s' = IF eb = <<>> THEN [s EXCEPT ![e] = <<Len(pg')-Len(pg),"BeginEnq">>] ELSE s
                       /\ UNCHANGED <<eb,queueBar>>
                    \/ LET k==s[e][1] IN
                       /\ k>0
                       /\ s[e][2]="BeginEnq"
                       /\ queueBar' = SubSeq(qBar,1,Len(qBar)-k)
                       /\ s' = [s EXCEPT ![e] = <<k-1,"BeginEnq">>]
                       /\ UNCHANGED <<adding,before,deq,elts,enq,p,eb,pg>>

EndEnq(e) == /\ enq[e] # Done
             /\ enq' = [enq EXCEPT ![e]=Done]
             /\ adding' = [adding EXCEPT ![e]=NonElt]
             /\ UNCHANGED <<deq, elts, before, p>>

InBlockedState == \E u \in elts : u \notin beingAdded /\ u \notin {pg[i] : i \in DOMAIN pg}

(*************************************************************************************************************)
(* s adds a stuttering step before each EndPOEnqpq step that appends an element w to eb (and hence to qBar). *)
(* Immediately after that stuttering step, queueBar equals qBar \o << w >>.                                  *)
(*************************************************************************************************************)
EndEnqP(e) == \/ /\ ENABLED EndEnq(e)
                 /\ InBlockedState
                 /\ s[e][1] = 0
                 /\ s' = [s EXCEPT ![e] = <<1,"EndEnq">>]
                 /\ eb' = Append(eb, adding[e])
                 /\ UNCHANGED  <<enq,deq,elts,before,adding,p,pg,queueBar>>
              \/ /\ s[e] = <<1,"EndEnq">>
                 /\ s' = [s EXCEPT ![e] = <<0,"EndEnq">>]
                 /\ EndEnq(e)
                 /\ UNCHANGED <<eb,s,pg,queueBar>>
              \/ /\ ~InBlockedState
                 /\ EndEnq(e)
                 /\ UNCHANGED <<eb,s,pg,queueBar>>

BeginDeq(d) == /\ deq[d] # Busy
               /\ deq' = [deq EXCEPT ![d]=Busy]
               /\ UNCHANGED <<enq, elts, before, adding>>

BeginDeqP(d) == /\ BeginDeq(d)
                /\ UNCHANGED <<p,pg,eb,s,queueBar>>

isBefore(e1,e2) == <<e1,e2>> \in before

EndDeq(d) == /\ deq[d] = Busy
             /\ pg # <<>>
             /\ \E el \in elts:
               /\ \A el2 \in elts: ~(isBefore(el2,el))
               /\ elts' = elts \ {el}
               /\ deq' = [deq EXCEPT ![d]=el[1]]
               /\ before' = before \intersect (elts' \X elts')
               /\ elts' = elts \ {p[1]}
               /\ p' = Tail(p)
               /\ pg' = Tail(pg)
             /\ UNCHANGED <<enq, adding, eb>>

(***********************************************************************************)
(* s adds a single stuttering step before each EndPODeqpq step.                    *)
(* The value of queueBar equals Tail(qBar) immediately after that stuttering step. *)
(***********************************************************************************)
EndDeqP(d) ==  \/ /\ ENABLED EndDeq(d)
                  /\ s[d][1] = 0
                  /\ s' = [s EXCEPT ![d] = <<1,"EnqDeq">>]
                  /\ queueBar' = Tail(qBar)
                  /\ UNCHANGED <<enq,deq,elts,before,adding,p,pg,eb>>
               \/ /\ s[d] = <<1,"EnqDeq">>
                  /\ s' = [s EXCEPT ![d]= <<0,"EnqDeq">>]
                  /\ EndDeq(d)
                  /\ UNCHANGED queueBar

NextP == \/ \E e \in EnQers : \/ BeginEnqP(e)
                              \/ EndEnqP(e)
         \/ \E d \in DeQers :  \/ BeginDeqP(d)
                               \/ EndDeqP(d)

Spec == InitP /\ [][NextP]_v

====