(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".
 
Load VRA_ImptoExp.
Import VRA_ImptoExp.

Import VRA_varPrsrvtn_thm.

Theorem variation_preservation_Imp e S q A (HndpQ: NoDupElemvQ q): 
       { e , S |- q | A } ->
       forall c, E[[e]]c = true ->
           ||= (Q[[ [q]S]]c) =x= QT[[ A]]c.

Proof. intros HImp c He.
(*
  HImp : {e, S |- q | A}
  --------------------------------------
  ||= (Q[[ [q] S]] c) =x= QT[[ A]] c
*)
(* HImp : {e, S |- q | A} -> {e, S |= [q] S | A'} /\ A =T= A' *) 
apply ImpQ_ImpType_ExpQ_ExpType in HImp; try auto.
destruct HImp as [A' [HExpQ HEquiv] ].
(* {e, S |= [q] S | A'} -> HExpQ : ||= (Q[[ [q] S]] c) =x= QT[[ A']] c *) 
apply variation_preservation with (c:=c) in HExpQ;
try auto.
(* A =T= A' -> HEquiv : QT[[ A]] c =x= QT[[ A']] c *)
apply configVQtype_equiv with (c:=c) in HEquiv.
(*
  HExpQ : ||= (Q[[ [q] S]] c) =x= QT[[ A']] c
  HEquiv : QT[[ A]] c =x= QT[[ A']] c
  --------------------------------------
  ||= (Q[[ [q] S]] c) =x= QT[[ A]] c
*)
symmetry in HEquiv.
transitivity (QT[[ A']] c); auto.
Qed.
       
