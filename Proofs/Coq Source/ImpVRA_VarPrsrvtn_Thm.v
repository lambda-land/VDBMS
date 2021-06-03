(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".
 
Load VRA_Imp_To_Exp.
Import VRA_Imp_To_Exp.

Import VRA_VarPrsrvtn_Thm.

Theorem variation_preservation_Imp e S q A (HndpQ: NoDupElemvQ q): 
       { e , S |- q | A } ->
       forall c, E[[e]]c = true ->
          (S[[ S]]c) ||= (Q[[ [q]S]]c) =set= QT[[ A]]c.

Proof. intros HImp c He.
(*
  HImp : {e, S |- q | A}
  --------------------------------------
  (S[[ S]]c) ||= (Q[[ [q] S]] c) =set= QT[[ A]] c
*)
(* HImp : {e, S |- q | A} -> {e, S |= [q] S | A'} /\ A =vqtype= A' *) 
apply ImpQ_ImpType_ExpQ_ExpType in HImp; try auto.
destruct HImp as [A' [HExpQ HEquiv] ].
(* {e, S |= [q] S | A'} -> HExpQ : (S[[ S]]c) ||= (Q[[ [q] S]] c) =set= QT[[ A']] c *) 
destruct A' as (A', e'). 
eapply variation_preservation with (c:=c) in HExpQ;
try auto. 
(* A =vqtype= A' -> HEquiv : QT[[ A]] c =set= QT[[ A']] c *)
apply configVQtype_equiv with (c:=c) in HEquiv.
(*
  HExpQ : ||= (Q[[ [q] S]] c) =set= QT[[ A']] c
  HEquiv : QT[[ A]] c =set= QT[[ A']] c
  --------------------------------------
  (S[[ S]]c) ||= (Q[[ [q] S]] c) =set= QT[[ A]] c
*)
symmetry in HEquiv.
transitivity (QT[[ (A', e')]] c); try auto.
Qed.
       
