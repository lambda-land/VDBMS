(** Variational relational algebra *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Export Logic.
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.ListSet.
Require Import Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Sorting.Sorted.
Require Import FunInd.
Require Import Recdef.
Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

(* Local libs and moduels *)
Load CpdtTactics.
Require Import Coq_Extended_Logic.


(*Require Import Coq.MSets.MSetInterface.

Require Import Coq.MSets.MSetWeakList. 

Require Import MSets.

Module MDT_String.
Definition t := string.
Definition eq_dec := string_dec.
End MDT_String.

Module StringDec := DecidableTypeEx.Make_UDT(MDT_String).

(** → Then build the MSet module *)
Module StringWL := MSetWeakList.Make StringDec.

Import StringWL.Raw.*)

Load Feature.
Import Feature.

Module VDBMS_Encoding.

(** -------------------------------------------------------------
  Elemribute: Type and Comparison Function, Lemmas
-----------------------------------------------------------------*)
(* Plain Element (Elemribute/Value) *)
Definition elem : Type := string.

Inductive comp : Type := 
  | EQc | LTc | GTc.

(* Variational Element (Elemribute/Value) *)
Inductive velem : Type :=
   | ae : elem -> fexp -> velem. 

(* Shorthands for finding/accessing elements *)
Definition fstVelem (v:velem) : elem  := let  'ae x e := v  in x.
Definition sndVelem (v:velem) : fexp := let  'ae x e := v  in e.

(*----------------------Equality Schemes----------------------------*)

(* Comment :- why not using equality and relevant facts from string libary?
velem (string, fexp) equality scheme, generates equality scheme for string and fexp.
Although string library provides string equality and all relevant facts, 
I don't know how to make scheme command use that when scheming equality for velem.
Thus for the sake of consistency i.e. not using two types of string equality, we will
use schemed equality and equality facts from equality module for string like fexp and velem 
------------------------------------------------------------------------------------------*)


Scheme Equality for string. 

(* Equalities for string *)
Module DT_string.
Definition t := string.
Definition eq_dec := string_eq_dec.
Definition eqb := string_beq.
Definition eq :=  @Logic.eq t.
Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
Proof. split. 
       apply internal_string_dec_bl.
       apply internal_string_dec_lb. 
Qed.
End DT_string.

(** Usual Decidable Type Full for string *)
Module stringDecF := Equalities.Make_UDTF(DT_string).
(* Generate Boolean Equality Facts (e.g. eqb_neq, eqb_refl) for string*)
Module stringBEF := Equalities.BoolEqualityFacts(stringDecF). 

Scheme Equality for fexp. 

(* Equalities for fexp *)
Module DT_fexp.
Definition t := fexp.
Definition eq_dec := fexp_eq_dec.
Definition eqb := fexp_beq.
Definition eq :=  @Logic.eq t.
Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
Proof. split. 
       apply internal_fexp_dec_bl.
       apply internal_fexp_dec_lb. 
Qed.
End DT_fexp.

(** Usual Decidable Type Full for fexp *)
Module fexpDecF := Equalities.Make_UDTF(DT_fexp).
(* Generate Boolean Equality Facts (e.g. eqb_neq, eqb_refl) for fexp*)
Module fexpBEF := Equalities.BoolEqualityFacts(fexpDecF). 


Scheme Equality for velem. 
(* Equalities for velem*)

(* Decidable Module for velem *)
Module DT_velem.
Definition t := velem.
Definition eq_dec := velem_eq_dec.
Definition eqb := velem_beq.
Definition eq :=  @Logic.eq t.
Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
Proof. split. 
       apply internal_velem_dec_bl.
       apply internal_velem_dec_lb. 
Qed.
End DT_velem.

(** Usual Decidable Type Full for velem *)
Module velemDecF := Equalities.Make_UDTF(DT_velem).
(* Generate Boolean Equality Facts (e.g. eqb_neq, eqb_refl) for Velem*)
Module velemBEF := Equalities.BoolEqualityFacts(velemDecF). 

(*----------------------Equality Schemes End----------------------------*)

(** -----------------------elem velem-------------------------- **)


(** ------------------------------------------------------------
  Elemribute List
---------------------------------------------------------------*)

(* Plain Elemribute List *)
Definition elems : Type := set elem.

(*------------------------------------------------------------------------*)

(* Variational Elemribute List *)
Definition velems : Type := set velem.

(*Lemma not_equal: forall a a' e', a' <> a -> ae a' e' <> ae a e'.
Proof. intros. rewrite <- velemBEF.eqb_neq. simpl.  Admitted.*)

(** ------------------------------------------------------------
  Operations on elem element in velems 
---------------------------------------------------------------*)

(* list Logic specific list of velems*)

Lemma existsb_In : 
    forall a l, 
         existsb (velem_beq a) l = true <-> In a l.
Proof. intros. split.
- intro H. rewrite existsb_exists in H.
  destruct H. destruct H.
  rewrite velemDecF.eqb_eq in H0.
  rewrite H0. auto.
- intro H. rewrite existsb_exists.
  exists a. split. auto.
  rewrite velemDecF.eqb_eq. auto.
Qed.

Lemma existsb_In_elem : 
    forall a l, 
         existsb (string_beq a) l = true <-> In a l.
Proof. intros. split.
- intro H. rewrite existsb_exists in H.
  destruct H. destruct H.
  rewrite stringDecF.eqb_eq in H0.
  rewrite H0. auto.
- intro H. rewrite existsb_exists.
  exists a. split. auto.
  rewrite stringDecF.eqb_eq. auto.
Qed.

Lemma not_existsb_In : 
    forall a l, 
         existsb (velem_beq a) l = false <-> ~ In a l.
Proof. intros.  split.
- intro H. rewrite <- existsb_In.
rewrite not_true_iff_false. auto.
- intro H. rewrite <- existsb_In in H.
rewrite not_true_iff_false in H. auto.
Qed.

Lemma not_existsb_In_elem : 
    forall a l, 
         existsb (string_beq a) l = false <-> ~ In a l.
Proof. intros.  split.
- intro H. rewrite <- existsb_In_elem.
rewrite not_true_iff_false. auto.
- intro H. rewrite <- existsb_In_elem in H.
rewrite not_true_iff_false in H. auto.
Qed.


(* count occurances of elemribite a in given velems *)
Fixpoint count_occ_Elem (a : elem) (v:velems) : nat := 
   match v with
   | []           => O
   | ae x e :: xs => 
       match (string_beq a x) with
       | true  => S (count_occ_Elem a xs)
       | false => count_occ_Elem a xs
       end
   end.

(* -- eqbElem --*)

Definition eqbElem (a: elem) (v:velem) : bool := string_beq a (fstVelem v).

Tactic Notation "simpl_eqbElem"  := unfold eqbElem; simpl.
Tactic Notation "eqbElem_eq" := simpl_eqbElem; rewrite stringDecF.eqb_eq.

Tactic Notation "simpl_eqbElem" "in" hyp(H) := unfold eqbElem in H; simpl in H.
Tactic Notation "eqbElem_eq" "in" hyp(H) := simpl_eqbElem in H; rewrite stringDecF.eqb_eq in H.

(* lemma eqbElem *)
Lemma ex_velem_fexp : forall A a, (exists x, In x A /\ (eqbElem a) x = true) <-> (exists e, In (ae a e) A).
Proof. intros. split. 
       - induction A; intro H;
         destruct H as [v Hv];
         simpl in Hv; destruct Hv. 
       + destruct H.
       + destruct H.
         ++ destruct v.
         eqbElem_eq in H0. 
         rewrite H. simpl.  exists f.
         left. rewrite H0. reflexivity.
         ++ simpl. rewrite dist_exists_or. 
           right. apply IHA. exists v.
           split. auto. auto.
      - induction A; intro H.
      + destruct H as [e He];
        simpl in He. destruct He. 
      + simpl in H. rewrite dist_exists_or in H. 
        destruct H. 
        ++ exists a0. simpl. split. eauto.
           destruct H as [e He];
           simpl in He. rewrite He. eqbElem_eq.
           auto.
        ++ apply IHA in H. destruct H as [v Hv];
           simpl in Hv; destruct Hv. exists v.
           split. simpl. eauto. auto.
Qed.

(* -- existsbElem -- *)

(* check whether elem a exists in velems l - existsb from lib *)
Definition existsbElem (a : elem) (l : velems) := existsb (eqbElem a) l.


Lemma existsbElem_filter: forall a A, existsbElem a A = false -> 
                           (forall x, ~ In x (filter (eqbElem a) A)).
Proof. intros. 
unfold existsbElem in H. 
rewrite <- not_true_iff_false in H.
assert (Hab: ~(exists x, In x A /\ ((eqbElem a)) x = true)). 
rewrite <- existsb_exists. auto. 
rewrite <- dist_not_exists in Hab. 
rewrite filter_In. apply Hab.
Qed.

(*  -- InElem  -- *)
(* In-Elem: Plain Element in V-set *)
Function InElem (a:elem) (l:velems) {struct l}: Prop :=
    match l with
    | []           => False
    | ae x e :: xs => x = a \/ InElem a xs
    end.

(* -- InElem cons intro -- *)
Lemma InElem_cons_intro: forall a l, InElem a l -> forall e, InElem a ((ae a e)::l).
Proof. intros. simpl. auto. Qed.

(* -- InElem inversion -- *)
Lemma InElem_inv_noteq : forall a b l, (fstVelem a) <>  b -> InElem b (a :: l)
-> InElem b l.
Proof. intros. destruct a. simpl in *.
destruct H0. contradiction. auto.
Qed.


(* -- InElem existsbElem lemma -- *)

Lemma existsbElem_InElem : 
    forall a l, existsbElem a l = true <-> InElem a l.
Proof. unfold existsbElem. intros; split; 
functional induction (InElem a l) using InElem_ind.
- simpl. congruence. 
- intro H. simpl in H. apply orb_true_iff in H.
  destruct H. 
  ++ eqbElem_eq in H. 
     eauto.
  ++ eauto.
- eauto. 
- intro H. simpl. apply orb_true_iff.
  destruct H.
  ++ eqbElem_eq.
     eauto.
  ++ eauto.
Qed.

Lemma not_existsbElem_InElem : 
    forall a l, existsbElem a l = false <-> ~InElem a l.
Proof. intros.  split.
- intro H. rewrite <- existsbElem_InElem.
rewrite not_true_iff_false. auto.
- intro H. rewrite <- existsbElem_InElem in H.
rewrite not_true_iff_false in H. auto.
Qed.


Hint Resolve existsbElem_InElem not_existsbElem_InElem.

Ltac existsbElem_InElem := rewrite existsbElem_InElem.
Ltac InElem_existsbElem := rewrite <- existsbElem_InElem.

Tactic Notation "existsbElem_InElem" "in" hyp(H) := rewrite existsbElem_InElem in H.
Tactic Notation "InElem_existsbElem" "in" hyp(H) := rewrite <- existsbElem_InElem in H.

Ltac not_existsbElem_InElem := rewrite not_existsbElem_InElem.
Ltac not_InElem_existsbElem := rewrite <- not_existsbElem_InElem.

Tactic Notation "not_existsbElem_InElem" "in" hyp(H) := rewrite not_existsbElem_InElem in H.
Tactic Notation "not_InElem_existsbElem" "in" hyp(H) := rewrite <- not_existsbElem_InElem in H.

(* -- InElem Deciadability -- *)

Lemma InElem_reflect : forall x y, reflect (InElem x y) (existsbElem x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply existsbElem_InElem.
Qed.


Definition InElem_dec (a: elem) (b: velems) : {InElem a b}+{~(InElem a b)}.
  destruct (InElem_reflect a b) as [P|Q]. left. apply P. right. apply Q.
Defined.

(* -- InElem In lemmas -- *)

Lemma existsbElem_exists :
      forall a l, existsbElem a l = true <-> exists x, In x l /\ (eqbElem a) x = true.
Proof. unfold existsbElem. intros. apply existsb_exists. Qed.

Hint Resolve existsbElem_exists.

(* R.S. is equiv. to (exists e, In (ae a e) A. *)
Lemma InElem_In_exvelem : 
      forall a A, InElem a A  <-> exists x, In x A /\ (eqbElem a) x = true.
Proof.  intros. InElem_existsbElem. eauto. Qed.

Lemma InElem_In_exfexp : forall (a:elem) (A:velems), InElem a A  <-> exists e, In (ae a e) A.
Proof.  intros. rewrite <- ex_velem_fexp. InElem_existsbElem. eauto. Qed.

(*Lemma InElem_In_a : forall (A:velems), (exists a, In a A <-> InElem (fstVelem a) A ).
Proof. intros. exists a. InElem_existsbElem. eauto. Qed.*)

Lemma In_InElem_fstVelem : forall (a:velem) (A:velems), In a A  -> InElem (fstVelem a) A.
Proof. intros. rewrite InElem_In_exvelem. 
       exists a. split. auto.
       unfold eqbElem. rewrite stringBEF.eqb_refl. reflexivity.
Qed.

(* -- removeElem  --*)

(* remove all occurances of elem a from velems A *)
Function removeElem (a : elem) (A: velems) {struct A} : velems := 
    match A with 
   | nil => nil
   | ae a' e' :: A' => match (string_beq a a') with
                     | true => removeElem a A'
                     | false => ae a' e' :: removeElem a A'
                     end
   end.

(* --InElem removeElem lemmas -- *)

(* not used yet but might need them later *)
Theorem notInElem_removeElem : forall l x, ~ InElem x (removeElem x l).
Proof. intros. 
functional induction (removeElem x l) using removeElem_ind.
- simpl. apply neg_false. reflexivity.
- auto.
- simpl. apply Classical_Prop.and_not_or.
  split. + rewrite stringBEF.eqb_neq in e0. 
  eauto. + auto.
Qed.

Lemma InElem_InElem_removeElem : forall l x y, x <> y ->
InElem x l <-> InElem x (removeElem y l).
Proof. intros l x y H. split; induction l; intros  H0. 
- simpl in H0. destruct H0.
- destruct a as (a, f). simpl. destruct (string_beq y a) eqn: Hya. 
  + simpl in H0. destruct H0.
    ++ rewrite stringDecF.eqb_eq in Hya. 
    rewrite Hya in H . symmetry in H0. contradiction.
    ++ eauto. 
  + simpl. simpl in H0. 
    destruct H0. eauto. 
    eauto.
- simpl in H0. destruct H0.
- destruct a as (a, f). simpl. simpl in H0.
  destruct (string_beq y a) eqn: Hya.
  ++ eauto.
  ++ simpl in H0. destruct H0.
     +++ eauto.
     +++ eauto.
Qed.


Lemma notInElem_removeElem_eq: forall l x, ~ InElem x l -> removeElem x l = l.
Proof.
intros l x. induction l; intro H. 
- eauto.
- destruct a as (a, e). simpl. simpl in H. 
  apply Classical_Prop.not_or_and in H. destruct H as [H1 H2].
  destruct(string_beq x a) eqn:Hxa. rewrite stringDecF.eqb_eq in Hxa.
  destruct H1. eauto. rewrite (IHl H2). reflexivity.
Qed.

Lemma In_removeElem a a' e' A: a <> a' -> 
      In (ae a' e') A <-> In (ae a' e') (removeElem a A).
Proof. intros H. split; induction A; intros  H0. 
- simpl in H0. destruct H0.
- destruct a0 as (a0, f). simpl. destruct (string_beq a a0) eqn: Hya. 
  + simpl in H0. destruct H0.
    ++ rewrite stringDecF.eqb_eq in Hya. 
    inversion H0; subst. destruct H. reflexivity.
    ++ eauto. 
  + simpl. simpl in H0. 
    destruct H0. eauto. 
    eauto.
- simpl in H0. destruct H0.
- destruct a0 as (a0, f). simpl. simpl in H0.
  destruct (string_beq a a0) eqn: Hya.
  ++ eauto.
  ++ simpl in H0. destruct H0.
     +++ eauto.
     +++ eauto.
Qed.

Theorem notIn_removeElem : forall l x e, ~ In (ae x e) (removeElem x l).
Proof. intros. 
functional induction (removeElem x l) using removeElem_ind.
- simpl. apply neg_false. reflexivity.
- auto.
- simpl. apply Classical_Prop.and_not_or.
  split. + rewrite stringBEF.eqb_neq in e1. 
  unfold not. intro e2. unfold not in e1. apply e1.
  inversion e2. reflexivity. + auto.
Qed.

Lemma notIn_notInremoveElem a a' A: 
~ In a' A -> ~ In a' (removeElem a A).
Proof. destruct a' as (a', e'). 
destruct (string_eq_dec a a').
- rewrite e. intro H. apply notIn_removeElem.
- apply In_removeElem with (e':=e') (A:=A) in n.
intro H. rewrite n in H. assumption.
Qed.


(* not used yet but might need them later *)
(*Lemma InElem_removeElem: forall l x y, InElem x (removeElem y l) -> InElem x l /\ x <> y.
Admitted.

Lemma removeElem_removeElem_comm : forall l x y,
    removeElem x (removeElem y l) = removeElem y (removeElem x l).
Admitted.

Lemma removeElem_removeElem_eq : forall l x, removeElem x (removeElem x l) = removeElem x l.
Admitted.*)


(*  -- removeElem List.length -- *)
Lemma remove_reduce (a:elem) (l:velems) : List.length (removeElem a l) < S(List.length l).
Proof. intros. induction l.
       - unfold removeElem.  unfold List.length. 
         apply PeanoNat.Nat.lt_0_succ. 
       - simpl. destruct a0 as (a0, f). destruct (string_beq a a0). auto. 
         simpl. apply Lt.lt_n_S. auto. 
Qed.

Hint Resolve remove_reduce.

(*-------------------------------------------------------------------------------*)


(* Configuration Variational Set X[]c (see A3)*)
Fixpoint configVElemSet (vA : velems) (c : config) : elems :=
  match vA with
  | nil                  => nil
  | cons (ae a e) vas => if semE e c 
                             then (cons a (configVElemSet vas c))
                             else (           configVElemSet vas c )
  end.

Notation "X[[ vA ]] c" := (configVElemSet vA c) (at level 50).

Lemma In_config_true: forall a e A c, In (ae a e) A ->
           (E[[ e]]c) = true -> In a (configVElemSet A c).
Proof. intros. induction A. 
       - simpl in H. destruct H.
       - simpl in H. destruct H.
         + rewrite H. simpl. rewrite H0.
           simpl. eauto.
         + apply IHA in H. 
           destruct a0. simpl. destruct (E[[ f]] c) eqn:Hf.
           ++ simpl. eauto.
           ++ auto.
Qed.

Lemma In_config_exists_true: forall a A c, (exists e, In (ae a e) A /\
           (E[[ e]]c) = true) <-> In a (configVElemSet A c).
Proof. intros. split. 
       - induction A; intros; destruct H;
         destruct H.
         + simpl in H. destruct H.
         + destruct a0 as (a0, f). simpl in H.
           destruct H. inversion H; subst.
           ++ simpl. rewrite H0. simpl. eauto.
           ++ simpl.  destruct (E[[ f]] c) eqn:Hf.
              +++ simpl. right. apply IHA. 
                  exists x. eauto.
              +++ apply IHA. 
                  exists x. eauto.
       - induction A; intro H.
         + simpl in H. destruct H.
         + destruct a0 as (a0, f). simpl in H.
           destruct (E[[ f]] c) eqn:Hf.
           ++ destruct H. 
              +++ exists f. rewrite H. simpl. split. eauto.
                  assumption.
              +++ simpl. apply IHA in H. 
                  destruct H as [e H].
                  destruct H.
                  exists e. split. eauto.
                  assumption. 
           ++ apply IHA in H. destruct H as [e H].
              destruct H. exists e. split. 
              simpl. eauto. assumption.
Qed.


(*Lemma not_in_config: forall a A, (forall e, ~ In (ae a e) A) ->
      forall c,~ In a (configVElemSet A c).
Proof. intros. induction A. 
       - simpl. simpl in H. auto.
       - simpl in H. destruct a0 as (a', e'). specialize H with e'. 
         apply Classical_Prop.not_or_and in H. destruct H. 
         rewrite <- velemBEF.eqb_neq in H. simpl in H. 
         rewrite fexpBEF.eqb_refl in H. rewrite andb_true_r in H.
         rewrite stringBEF.eqb_neq in H.
         unfold configVElemSet; fold configVElemSet. destruct (E[[ e']] c).
         simpl. apply Classical_Prop.and_not_or. split.
         + assumption.
         + apply IHA. apply H0. 
         simpl in H. destruct (fexp_eq_dec f e). rewrite e0 in H. 
         destruct H. Admitted.*)




(* Lemma InElem_config: forall a A c, InElem a A <->
            exists e, ((E[[ e]]c) = true -> In a (configVElemSet A c)).
Proof. intros. split. 
intro H. rewrite InElem_In_exfexp in H. destruct H as [e He].
exists e. intros H.
apply (In_config _ _ _ c) in He. auto. auto.
intros. destruct H as [e He]. 
apply In_InElem_config with (c:=c). in He.
Qed. *)

(** -----------------------elems velems------------------------ **)



(** ------------------------------------------------------------
  Relations 
---------------------------------------------------------------*)
(*relName*)
Definition r : Type := string.

(* Plain Relation Schema - set of plain elemributes with a name *)
Definition relS : Type := (r * elems) % type.

(* Variational Relation Schema - annotated set of variational elemributes with a name *)
Definition vrelS : Type := (r * (velems * fexp) ) %type. (*assuming always annotated; could've used option*)

(* Plain Schema *)
Definition schema : Type := set relS.

(* Variational Schema (Implicit encoding) *)
Definition vschema : Type := ((set vrelS) * fexp) %type.

Definition getr  (vr:vrelS) : r      := fst vr. 
Definition getvs (vr:vrelS) : velems := fst (snd vr).
Definition getf  (vr:vrelS) : fexp   := snd (snd vr).


Definition getSvrelS (vs:vschema) : (set vrelS) := fst vs.
Definition getSf  (vs:vschema) : fexp  := snd vs.


(* Variational Relation Schema Configuration R[]c *)
Definition configVRelS (vr : vrelS) (c : config) : relS := if semE (snd (snd vr)) c
                                                            then  (fst vr, (configVElemSet (fst (snd vr)) c)) 
                                                             else  (fst vr, nil).
Notation "R[[ vr ]] c" := (configVRelS vr c) (at level 50).

(* Variational Relation Schema  Configuration R[]c *)
Definition configVRelS_ (vr : vrelS) (c : config) : relS := 
let r := fst vr in
 let A := fst(snd vr) in
  let e := snd (snd vr) in 
  if E[[ e]]c
   then  (r, (X[[A]]c)) 
    else  (r, []).
Notation "R_[[ vr ]] c" := (configVRelS_ vr c) (at level 50).

(* Variational Schema  Configuration S[]c *)
Definition configVS (vs : vschema) (c : config) : schema := 
let VR := fst vs in
 let m := snd vs in
   if E[[ m]]c
    then  map (fun vr => (R[[vr]]c)) VR
     else  [].
Notation "S[[ vs ]] c" := (configVS vs c) (at level 50).

(** ---------------------------Scheme equality for relS-------------------------- **)

Scheme Equality for list. 
Definition relS_beq (r1 r2:relS) : bool := string_beq (fst r1) (fst r2) && list_beq (string_beq) (snd r1) (snd r2).

Lemma relSeqb_eqb_eq : forall x y, relS_beq x y = true <-> x = y.
Proof. 
destruct x. destruct y. 
unfold relS_beq. simpl.
split. 
intro H.
apply andb_prop in H.
destruct H.
apply internal_string_dec_bl in H.
apply internal_list_dec_bl in H0.
rewrite H, H0. reflexivity.
apply internal_string_dec_bl.

intro H.
apply pair_equal_spec in H. 
destruct H.
rewrite H, H0.
rewrite andb_true_iff. split.
apply internal_string_dec_lb. auto.
apply internal_list_dec_lb. 
apply internal_string_dec_lb. auto. 
Qed.

Lemma existsb_In_relS : 
    forall a l, 
         existsb (relS_beq a) l = true <-> In a l.
Proof. intros. split.
- intro H. rewrite existsb_exists in H.
  destruct H. destruct H.
  rewrite relSeqb_eqb_eq in H0.
  rewrite H0. auto.
- intro H. rewrite existsb_exists.
  exists a. split. auto.
  rewrite relSeqb_eqb_eq. auto.
Qed.

(** ---------------------------relS-------------------------- **)

(** ------------------------------------------------------------
  Tables / Content
---------------------------------------------------------------*)
(* Plain Value *)
Definition val : Type := elem.

(* Variational Value *)
Definition vval : Type := velem. 

(* Plain Tuple *)
Definition tuple : Type := list elem.

(* Variational Tuple *)
Definition vtuple : Type := (list velem * fexp) % type.

(* Plain Relation Content *)
Definition rcontent : Type := set tuple.

(* Variational Relation Content *)
Definition vrcontent : Type := set vtuple.

(* Plain Relation Content *)
Definition table : Type := (relS * rcontent) %type.

(* Variational Relation Content *)
Definition vtable : Type := (vrelS * vrcontent) %type.

(* Plain Instance *)
Definition instance : Type := set table.

(* Variational Relation Content *)
Definition vinstance : Type := set vtable.

(* Configuration Variational List V[]c *)
Fixpoint configVElemList (vl : list velem) (c : config) : list elem :=
  match vl with
  | nil                  => nil
  | cons (ae a e) val => if semE e c 
                             then (cons a (configVElemList val c))
                             else (        configVElemList val c )
  end.

Notation "V[[ vl ]] c" := (configVElemList vl c) (at level 50).

(* Variational Tuple  Configuration U[]c *)
Definition configVTuple (vtup : vtuple) (c : config) : tuple := 
let VT := fst vtup in
 let e := snd vtup in
  if E[[ e]]c
   then  (V[[VT]]c)
    else  [].
Notation "U[[ vu ]] c" := (configVTuple vu c) (at level 50).

(* Variational Relation Content Configuration T[]c *)
Definition configVRContent (vrc : vrcontent) (c : config) : rcontent := 
map (fun v => (U[[v]]c)) vrc.
Notation "T[[ vrc ]] c" := (configVRContent vrc c) (at level 50).

(* (* Variational Table Configuration T[]c *)
Definition configVTable (vt : vtable) (c : config) : table := 
let vrs := fst vt in
 let vrc := snd vt in
  (R[[ vrs ]]c, RC[[ vrc ]]c).
Notation "T[[ vt ]] c" := (configVTable vt c) (at level 50). *)

(* Variational Databse Insatnce Configuration I[]c *)
Definition configVDBInsatnce (vins : vinstance) (c : config) : instance := 
map (fun vt => ((R[[(fst vt)]]c), (T[[ (snd vt) ]]c))) vins.
Notation "I[[ vt ]] c" := (configVDBInsatnce vt c) (at level 50).
(** ---------------------------tuple-------------------------- **)


(** ------------------------------------------------------------
  Properties/ Function defined on vrelS vschema (Implicit encoding)
---------------------------------------------------------------*)

(* InVR InRn NoDupRn findVR*)
(* In [va:= (ae a ear)] [vr:= (Ar, er) := ({(a, ea)}, er)] *)
Definition InVA (va:velem) (vr:vrelS) : Prop := 
 let a := fstVelem va in 
  let ear := sndVelem va in 
   let Ar := getvs vr in 
     let er := getf vr in
      exists ea, In (ae a ea) Ar /\ (ea /\(F) er) = ear.

Definition InVR (vr:vrelS) (vs:vschema) : Prop := 
let rn := getr vr in 
 let vas := getvs vr in 
  let e':= getf vr in
   exists e, In (rn, (vas, e)) (fst vs) /\ (e /\(F) (snd vs)) = e'.

Function InRn (rn:string) (l:list vrelS) {struct l}: Prop :=
    match l with
    | []           => False
    | (rn_, (_, _)) :: ls => rn_ = rn \/ InRn rn ls
    end.

Inductive NoDupRn : list vrelS -> Prop :=
  | NoDupRn_nil : NoDupRn nil
  | NoDupRn_cons : forall rn A e l, ~ InRn rn l -> NoDupRn l 
                            -> NoDupRn ((rn, (A, e))::l).


Fixpoint getVRAe (rn : string) (vrs:set vrelS) : vrelS := 
  match vrs with 
 | nil                 => (rn, (nil, litB false))
 |(rn_, (A, e)) :: vrs' => if stringDecF.eqb rn_ rn
                           then (rn_, (A, e))
                            else getVRAe rn vrs'
 end.

Definition findVR (rn : string) (vs:vschema) : vrelS := 
   let vr' := getVRAe rn (fst vs) in  (getr vr', (getvs vr', getf vr' /\(F) snd vs)).

(** ------------------------------------------------------------
  Condition(theta) 
---------------------------------------------------------------*)
(*EQ Neq*)
Inductive op : Type :=
  | eq | GTE | LTE | GT | LT | neq.

(* Plain Condition *)
Inductive cond : Type :=
  | litCB  : bool -> cond
  | elemOpV : op -> elem -> nat -> cond
  | elemOpA : op -> elem -> elem -> cond
  | negC   : cond -> cond 
  | conjC  : cond -> cond -> cond
  | disjC  : cond -> cond -> cond.

(* Varitational condition*)
Inductive vcond : Type :=
  | litCB_v  : bool -> vcond
  | elemOpV_v : op -> elem -> nat -> vcond
  | elemOpA_v : op -> elem -> elem -> vcond
  | negC_v   : vcond -> vcond
  | conjC_v  : vcond -> vcond -> vcond
  | disjC_v  : vcond -> vcond -> vcond
  | chcC     : fexp -> vcond -> vcond -> vcond.

(* Configuration Variational Condition C[]c *)
Fixpoint configVCond (vc : vcond) (c : config) : cond :=
  match vc with
  | litCB_v  b          => litCB b
  | elemOpV_v o   a   k  => elemOpV o a k
  | elemOpA_v  o  a1  a2 => elemOpA o a1 a2
  | negC_v  vc           => negC (configVCond vc  c) 
  | conjC_v  vc1 vc2     => conjC (configVCond vc1 c) (configVCond vc2 c)
  | disjC_v  vc1 vc2     => disjC (configVCond vc1 c) (configVCond vc2 c)
  | chcC e   vc1 vc2    => if semE e c then configVCond vc1 c else configVCond vc2 c
  end.
Notation "C[[ vc ]] c" := (configVCond vc c) (at level 50).
(** -----------------------cond vcond------------------------ **)

(* Annotated Variaitonal Set (Variaitonal Query Type) *)
Definition avelems : Type := (velems * fexp) %type. (*assuming always annotated; could've used option*)

(* Configuration Annotated Variaitonal Set (Variational Query Type) T[]c *)
Definition configaVelems (vqt : avelems) (c : config) : elems := 
      match vqt with 
      |(V, e) => if semE e c then  configVElemSet V c else  nil
      end.
Notation "AX[[ vqt ]] c" := (configaVelems vqt c) (at level 50).

(** -------------------------------------------------------
  Query 
-----------------------------------------------------------*)

Inductive setop : Type := union | inter.

(* Plain Query*)
Inductive query : Type :=
  | rel   : relS    -> query
  | proj  : elems   -> query -> query 
  | sel   : cond    -> query -> query 
  (*| join  : cond    -> query -> query -> query *)
  | prod  : query   -> query -> query 
  | setU  : setop   -> query -> query -> query
  | empty : query.

(* Variaitonal Query *)
Inductive vquery : Type :=
  | rel_v   : vrelS    -> vquery
  | proj_v  : avelems  -> vquery -> vquery 
  | sel_v   : vcond    -> vquery -> vquery 
  | chcQ    : fexp     -> vquery -> vquery -> vquery
  (*| join_v  : vcond    -> vquery -> vquery -> vquery *)
  | prod_v  : vquery   -> vquery -> vquery 
  | setU_v  : setop    -> vquery -> vquery -> vquery
  | empty_v : vquery.

(* Configuration Variational Query Q[]c *)
Fixpoint configVQuery (vq : vquery) (c : config) : query :=
  match vq with
  | rel_v  vr            => rel (R[[ vr]]c)
  | proj_v avelems vq    => proj (AX[[ avelems]] c) (configVQuery vq c)
  | sel_v  vc  vq        => sel (C[[ vc]]c) (configVQuery vq c)
  | chcQ e vq1 vq2       => if semE e c then configVQuery vq1 c else configVQuery vq2 c
  (*| join_v vc  vq1 vq2   => join (configVCond vc c) (configVQuery vq1 c) (configVQuery vq2 c)*)
  | prod_v vq1 vq2       => prod (configVQuery vq1 c) (configVQuery vq2 c) 
  | setU_v setop vq1 vq2 => setU setop (configVQuery vq1 c) (configVQuery vq2 c) 
  | empty_v              => empty
  end.

Notation "Q[[ vq ]] c" := (configVQuery vq c) (at level 50).

(** -----------------------query vquery------------------------ **)


(** ------------------------------------------------------------
  Query Type 
---------------------------------------------------------------*)
(* Plain Query Type *)
Definition qtype  : Type := (elems) %type.

(* Variaitonal Query Type *)
Definition vqtype : Type := avelems. (*(velems * fexp) %type.*) (*assuming always annotated; could've used option*)

(* Configuration Variational Query Type QT[]c *)
Definition configVQtype (vqt : vqtype) (c : config) : qtype := configaVelems vqt c.
      (*match vqt with 
      |(V, e) => if semE e c then  configVElemSet V c else  nil
      end.*)

Notation "QT[[ vqt ]] c" := (configVQtype vqt c) (at level 50).

Lemma configVQtype_nil: forall e c, (configVQtype ([], e) c) = [].
Proof. intros e c. simpl. destruct (E[[ e]] c); reflexivity. Qed.

Definition getvs_vqt (X:vqtype) : velems := fst X.
Definition getf_vqt (X:vqtype) : fexp := snd X.

(** ---------------------qtype vqtype---------------------- **)



(*-----------------------Functions----------------------------*)


(** ------------------------------------------------------------
  Plain and Variational Set Subsumption
---------------------------------------------------------------*)
(* Checks count
   Ex: subset_bool [1;1;2] [1;2] = false 
*)
(* Subset of Plain Set  *)
Fixpoint subset_bool (A A': elems): bool :=
    match A with
    | nil => true
    | cons x xs => match set_mem string_eq_dec x A' with 
                   | false => false
                   | true  => subset_bool xs (set_remove string_eq_dec x A')
                   end
    end. 

(* Also check count
   subset [1; 1; 2] [1; 2] doesn't hold
*)
Definition subset (A A': elems):= forall x, (In x A -> In x A') /\ (* In clause is redundant *)
           (count_occ string_eq_dec A x <= count_occ string_eq_dec A' x).

(* Subsumption of Plain Set (Query Type) *)
Definition subset_qtype_bool (A A': qtype) := subset_bool A A'.

(* Subsumption of Variational Set (Query Type) *)
Definition subset_vqtype ( X X': vqtype ) : Prop := forall c, 
    subset (configVQtype X c) (configVQtype X' c).

Definition subset_velems ( A A': velems ) : Prop := forall c, 
    subset (configVElemSet A c) (configVElemSet A' c).
      
Definition subset_avelems ( A A': avelems ) : Prop := forall c, 
   subset (AX[[ A]]c) (AX[[ A']]c).



(* current def (null is subset): forall x e,
(In (ae x e) A /\ (exists c, E[[e]]c = true) ) -> (exists e', (In (ae x e') A') /\  (~ sat (e /\(F) (~(F)(e')))) ).*)
(* should be: forall x e,
In (ae x e) A -> (exists e', (In (ae x e') A') /\  (~ sat (e /\(F) (~(F)(e')))) ). *)

(*
subset_velems_exp (<_e) : A <_e A' [need for proj_v A A']
  If it entails forall c, [A]c to be subset( <_a) of [A']c ... (1), where 
subset is defined as, forall x, count x [A]c <= count x [A']c [note: {} <_a {any}],
it would be a reasonable choice as then, after configuration, proj [A]c [A']c, is a valid plain query in RA.
  Therefore, forall (a,e), In (a, e) A we have two cases that would make [A]c valid configured subset of [A']c.
Case 1: ~ (sat e) 
  [ a will never be in [A]c, any c. thus, we don't need a elem-matching variational elemribute in A'. 
    i.e. It doesn't melemer whether there exists e', In (a, e') A']
Case 2: sat e -> exists e', In (a, e') A' /\ (e -> e'). (not true if A A' is not NoDupElem)
    Explanation: let A = {(a, e1) (a, e2) } and A' = {(a, e3, (a, e4)}
                 For count a [A]c <= count a [A']c to hold,
                 i.  e1 xor e2  -> ( e3 \/ e4 ) [ok if both]
                 ii. e1 /\ e2 -> e3 /\ e4 [both has to be true]
    For a single tuple, In (a, e1) A -> we don't need a single e' that is always true if e1 true i.e. e1 -> e'
                          any one e' in A' being true when e1 is true is enough. 
    Also, we need for all tuples with elemribute a condition. if all of them is true, at least same number of e' needs to true in A'.
    However, to make things easier we can assume A and A' is NoDupElem which can be safely assumed in our VDBMS.
    Then, e -> e' is sufficient. 
*)
(** ------------------------------
Definition subset_velems_exp A A': forall (a, e), [In (a, e) A /\ (sat e)] -> exists e', [In (a, e') A' /\ (e -> e')].
   where A A' is NoDupElem. 
================================= *)
(**  Lemma subset_velems_correctness (NoDupElem A)(NoDupElem A'): 
       subset_velems_exp A A' <-> subset (configVElemSet A c) (configVElemSet A' c). *)

(* [Note: forall (a, e), In (a, e) A  -> exists e', In (a, e') A' /\ (e -> e'). is unreasonable/ not necessary/ over restriction, 
      because if e is not sat, then, there is no reason to ask/check for elemribute a in A' with some e'.] *)
  
(* Now if we restrict our A to only hold satisfiable tuples, then definition seems to get simplified into below [close to above]. 
but it does NOT as definition then would hold for any not SatTuples A, potentially with few sat and few not_sat tuples. If none of 
the tuples is sat, then it's alright. but if there are some sat, we need exists clause for those sat. i.e. we need to check each 
tuple based on their satisfiability, if sat then need exists clause to be true otherwise not. An overall satiafiable clause doesn't
elemain that. *)

(** ------------------------------
Definition subset_velems_exp_Wrong A A' : Prop := SatTuples A -> forall (a, e), In (a, e) A  -> exists e', In (a, e') A' /\ (e -> e').
================================= *)

(** why don't we need  SatTuples A' as well? ==> A' doesn't not need to be SatTuples (all sat) but to have sat e's (exists sat) i.e.
exists e', [sat e' /\ In (a, e') A' /\ (e -> e')]. However, (e -> e' -> sat e') thus can remove sat e'*) 

(** ------------------------------ 
Definition subset_vqtype_exp X X': forall (a, e), [In (a, e) (fst X) /\ sat (e/\snd X)]  -> exists e', In (a, e') X' /\ (e/\snd X -> e'/\snd X').
   where (fst X) (fst X') is NoDupElem.
================================= *) 
(**  Lemma subset_vqtype_correctness (NoDupElem (fst X))(NoDupElem (fst X')): 
                subset_vqtype_exp X X' <-> subset (configVQtype X c) (configVQtype X' c). *)

(* SatATuples X := SatTuples (push_annot (fst X, snd X)).  [SatTuples (fst X) /\ Sat (snd X)] doesn't guarantee sat (e/\snd X). *)

(* Similar reasoning gives us *)
(** ------------------------------
Definition subset_velems_imp A A' : forall (a, e), In (a, e) A /\ sat(e) -> exists e', In (a, e') A' /\ sat(e /\ e').
       where A A' is NoDupElem.
==================================
Definition subset_velems_imp_Wrong A A' [HA: SatTuples A] : forall (a, e), In (a, e) A  -> exists e', In (a, e') A' /\ sat(e /\ e').
---------------------------------- 
Definition subset_vqtype_imp X X' : forall (a, e), In (a, e) A /\ sat (e/\snd X)  -> exists e', In (a, e') A' /\ sat(e/\snd X /\ e'/\snd X').
    where (fst X) (fst X') is NoDupElem.
================================= *)

(* Lemma : sat (A /\ B) -> sat A /\ sat B. but not <- *)

(*Definition subset_velems_exp (A A': velems) :Prop := forall x e,
In (ae x e) A /\ sat e  -> exists e', In (ae x e') A' /\  (~ sat (e /\(F) (~(F)(e')))).*)

Definition subset_velems_exp (A A': velems) :Prop := forall x e c,
In (ae x e) A /\ ((E[[ e]]c) = true)  -> 
       exists e', In (ae x e') A' /\  (E[[ e']]c) = true.

(* Definition subset_vqtype_exp (X X': vqtype) :Prop := 
let (A, ea) := X in 
  let (A', ea') := X' in 
    forall x e c,
      In (ae x e) A /\ ((E[[ e /\(F) ea]]c) = true)  -> 
       exists e', In (ae x e') A' /\  (E[[ e'/\(F) ea']]c) = true.*)



(** A and A' has to be NoDupElem *)
Definition subsump_velems (A A': velems) :Prop := 
forall x e, In (ae x e) A /\ sat e -> exists e', In (ae x e') A' /\ sat(e /\(F) e').
(*In (ae x e) A -> (exists e', (In (ae x e') A') /\ sat(e /\(F) e')).*)

(** (fst X) and (fst X') has to be NoDupElem *)
Definition subsump_vqtype ( X X': vqtype) : Prop := 
(*subsump_velems (fst X < snd X) (fst X' < snd X'). *)
let (A, ea) := X in 
  let (A', ea') := X' in 
    forall x e, In (ae x e) A /\ sat (e /\(F) ea) -> 
                       exists e', In (ae x e') A' /\ sat (e /\(F) ea /\(F) e' /\(F) ea').
(* subsump_velems (fst X) (fst X') /\ sat((snd X) /\(F) (snd X')). *)


(*Lemma subset_velems_exp_ind A a ea A': subset_velems_exp A (ae a ea :: A') ->
(forall x e, In (ae x e) A /\ sat e -> exists e', (ae x e') = (ae a ea) /\ sat(e /\(F) e'))
    \/ subset_velems_exp A A'.
Proof. intros H. 
unfold subset_velems_exp in H. simpl in H. 
rewrite and_distributes_over_or in H.*)


(*Lemma subsump_velems_refl A: subsump_velems A A.
Proof. unfold subsump_velems. intros x e H.
exists e. auto. (*destruct H as [HIn Hsat]. split. 
assumption. 
unfold sat. simpl. unfold sat in Hsat. 
destruct Hsat as [c Hsat]. exists c. 
rewrite Hsat. auto.*)
Qed.*)

(* Wrong move: restrict Schema and query to have following assumption so that, if In (a, e) A then, sat e *)
(* Definition SatTuples (A: velems) : Prop := forall a e, In (ae a e) A -> sat e.

Definition SatATuples (X: vqtype) : Prop := forall a e, In (ae a e) (fst X) -> sat (e /\(F) (snd X)).

Lemma SatATuples_SatTuples: forall X, SatATuples X -> SatTuples (fst X).
Proof. Admitted. *)

(*  Relating subsumpExp with subsumpImp *)


(*----------------------subsump--------------------------------*)


(** ------------------------------------------------------------
  Equivalence (of (Variational) Set) definition
---------------------------------------------------------------*)
(* Plain Set (Query Type) Equivalence*)
Fixpoint equiv_elems_bool (A A': qtype) : bool := 
    match A with
    | nil => match A' with 
             | nil => true
             | cons _ _ => false
             end
    | cons x xs => match set_mem string_eq_dec x A' with 
                   | false => false
                   | true  => equiv_elems_bool xs (set_remove string_eq_dec x A')
                   end
    end.

Definition equiv_elems : relation elems:= 
       fun A A' => forall a, (In a A <-> In a A') /\ 
                      ( count_occ string_eq_dec A a = count_occ string_eq_dec A' a).

Infix "=set=" := equiv_elems (at level 70) : type_scope.

(* Variational Set (non-annnot-Var Elemr) Equivalence (Only needed for next one)*)
Definition equiv_velems : relation velems := 
        fun A A' => forall c, configVElemSet A c =set= configVElemSet A' c.

Infix "=vset=" := equiv_velems (at level 70) : type_scope.

Definition equiv_avelems : relation vqtype := 
        fun X X' => forall c, AX[[ X]]c =set= AX[[ X']]c. 
Infix "=avset=" := equiv_avelems (at level 70) : type_scope.

Definition equiv_qtype_bool (A A': qtype) := equiv_elems_bool A A'.

Definition equiv_qtype : relation qtype := 
        fun A A' => A =set= A'.

Infix "=qtype=" := equiv_qtype (at level 70) : type_scope.

(* Variational Set (annotated-Var Query Type) Equivalence *)
Definition equiv_vqtype : relation vqtype := 
        fun X X' => X =avset= X'. 

Infix "=vqtype=" := equiv_vqtype (at level 70) : type_scope.

(* equiv_qtype is an Equivalence relation *)
Remark equiv_elems_refl: Reflexive equiv_elems.
Proof.
  intros A a. split; reflexivity.
Qed.

Remark equiv_elems_sym : Symmetric equiv_elems.
Proof.
  intros A A' H a.
  split; symmetry;
  apply H.
Qed.

Remark equiv_elems_trans : Transitive equiv_elems.
Proof.
  intros A A'' A' H1 H2 a.
  split; try (transitivity (In a A'')); 
         try (transitivity (count_occ string_eq_dec A'' a));
   try (apply H1);
   try (apply H2). 
Qed.

Instance elems_Equivalence : Equivalence equiv_elems := {
    Equivalence_Reflexive := equiv_elems_refl;
    Equivalence_Symmetric := equiv_elems_sym;
    Equivalence_Transitive := equiv_elems_trans }.

Instance qtype_Equivalence : Equivalence equiv_qtype := {
    Equivalence_Reflexive := equiv_elems_refl;
    Equivalence_Symmetric := equiv_elems_sym;
    Equivalence_Transitive := equiv_elems_trans }.

(* equiv_velems is Equivalence relation *)

Remark equiv_velems_refl: Reflexive equiv_velems.
Proof.
  intros A a. reflexivity.
Qed.

Remark equiv_velems_sym : Symmetric equiv_velems.
Proof.
  intros A A' H a.
  symmetry.
  apply H.
Qed.

Remark equiv_velems_trans : Transitive equiv_velems.
Proof.
  intros A A'' A' H1 H2 a.
  transitivity (configVElemSet A'' a).
    apply H1.
    apply H2.
Qed.

(** velems equivalence is an equivalence relation. *)
Instance velems_Equivalence : Equivalence equiv_velems := {
    Equivalence_Reflexive := equiv_velems_refl;
    Equivalence_Symmetric := equiv_velems_sym;
    Equivalence_Transitive := equiv_velems_trans }.

(* equiv_avelems is Equivalence relation *)

Remark equiv_avelems_refl: Reflexive equiv_avelems.
Proof.
  intro X. destruct X. unfold equiv_avelems. split; 
  reflexivity. 
Qed.

Remark equiv_avelems_sym : Symmetric equiv_avelems.
Proof.
  intros X Y. intros H. destruct X, Y. unfold equiv_avelems. 
  unfold equiv_avelems in H. symmetry. apply H.
Qed.


Remark equiv_avelems_trans : Transitive equiv_avelems.
Proof.
  intros X Y Z. intros H1 H2. 
  destruct X as (vx, fx), Y as (vy, fy), Z as (vz, fz). 
  unfold equiv_vqtype in H1. 
  unfold equiv_vqtype in H2. 
  unfold equiv_vqtype.
  intro c. transitivity (QT[[ (vy, fy)]] c); auto.
Qed.

(** avelems equivalence is an equivalence relation. *)
Instance avelems_Equivalence : Equivalence equiv_avelems := {
    Equivalence_Reflexive := equiv_avelems_refl;
    Equivalence_Symmetric := equiv_avelems_sym;
    Equivalence_Transitive := equiv_avelems_trans }.
    
(** vqtype equivalence is an equivalence relation. *)
Instance vqtype_Equivalence : Equivalence equiv_vqtype := {
    Equivalence_Reflexive := equiv_avelems_refl;
    Equivalence_Symmetric := equiv_avelems_sym;
    Equivalence_Transitive := equiv_avelems_trans }.

(*Lemma rewrite_equiv: forall a b c, a=set=b->
b=set=c-> a=set=c.
Proof. intros. rewrite <- H in H0. apply H0.
Qed.*)




(** ------------------------------------------------------------
  Restrict velems to have no duplicate elems 
                       i.e. same elems with diff fexp
---------------------------------------------------------------*)

(*stronger condition than mere NoDup velems*)

Inductive NoDupElem : velems -> Prop :=
  | NoDupElem_nil : NoDupElem nil
  | NoDupElem_cons : forall a e l, ~ InElem a l -> NoDupElem l 
                            -> NoDupElem ((ae a e)::l).



Definition get_annot (a : elem) (A: velems) : fexp :=  
                   fold_right Feature.join (litB false) (map (sndVelem) (filter (eqbElem a) A)). 

(*--------------------------------------------------------*)


(* -- nodupelem -- *)

(* remove duplicate elemributes - merging them through fexp_union *)
Function nodupelem (v : velems) {measure List.length v} : velems :=
   match v with 
   | nil          => nil
   | ae a e :: vs =>  match existsbElem a vs with
                      | false => ae a e :: nodupelem vs
                      | true  => let e' := get_annot a vs in
                         (ae a (e \/(F) e') ) :: nodupelem (removeElem a vs)
                      end
   end.
all:intros; simpl; eauto.
Defined.

Ltac simpl_nodupelem := rewrite nodupelem_equation.

Hint Resolve nodupelem_equation.

Lemma nodupelem_nil : nodupelem [] = [].
Proof. eauto. Qed.

Lemma nodupelem_not_in_cons : forall a e l,
      ~ InElem a l -> nodupelem (ae a e::l) = ae a e :: nodupelem l.
Proof. intros. simpl_nodupelem. 
simpl. destruct (existsbElem a l) eqn:Hf.
rewrite <- existsbElem_InElem in H. contradiction.
auto. Qed.

Lemma nodupelem_in_cons : forall a e l,
        InElem a l -> 
          nodupelem (ae a e::l) = ae a (e \/(F) get_annot a l) 
                     :: nodupelem (removeElem a l).
Proof. intros. simpl_nodupelem. simpl.
rewrite <- existsbElem_InElem in H. rewrite H. auto.
Qed.


(*Lemma nodup_fixed_point : forall (l : list A),
    NoDup l -> nodup l = l.*)


(*-----------------------NoDup_elems_in_velems--------------------------*)

(** ------------------------------------------------------------
  Push (elemribute list) annotation (to individual elemributes)
---------------------------------------------------------------*)
(* 
  |Push annotation/ fexp into Elemr List
  |A^e = {a^e1, b, c^e2,...}^e
  |push_annot A e = {a^(e1/\e), b^e, c^(e2/\e),...}
*)
Fixpoint push_annot (A: velems) (m: fexp) : (velems):=
  match A with
  | nil => nil
  | ae x e :: xs => (ae x (e /\(F) m)) :: push_annot xs m
  end.
Notation " Q < e " := (push_annot Q e) (at level 70). 

Definition avelems_velems (X:avelems) : velems := push_annot (fst X) (snd X).

Lemma fold_push_annot: forall x e xs m, 
(ae x (e /\(F) m)) :: push_annot xs m = push_annot ((ae x e) :: xs) m.
Proof. auto. Qed. 

Lemma push_annot_nil: forall e, push_annot [] e = [].
Proof. intros. reflexivity. Qed.

(* *)
Lemma configVQType_push_annot : forall A e1 e2 c, 
configVQtype (push_annot A e1, e2) c
= configVQtype (A, e1 /\(F) e2) c.
Proof. intros. induction A. 
       - simpl. destruct (E[[ e2]] c); 
         destruct (E[[ e1]] c); simpl; repeat (reflexivity).
       - destruct a as (x, e). unfold push_annot; fold push_annot. 
         simpl. 
         simpl in IHA. 
         destruct (E[[ e2]] c) eqn: E2.
          + destruct (E[[ e1]] c) eqn: E1; 
            destruct (E[[ e]] c) eqn: E; simpl; simpl in IHA;
              rewrite IHA; reflexivity. 
          + rewrite andb_false_r. reflexivity.
Qed.

(*Definition subsump_vqtype ( X X': vqtype) :Prop := 
subsump_velems (avelems_velems X) (avelems_velems X').*)

Definition subset_vqtype_exp (X X': vqtype) :Prop := 
subset_velems_exp (avelems_velems X) (avelems_velems X').

(*------------------------push_annot---------------------------*)

(** ------------------------------------------------------------
  Set Operation for Elemribute List(Set) & Query type(annotated elemr list)
  Union Intersection
---------------------------------------------------------------*)
(* Plain Elemr List *)
Definition elems_union (A A': elems) : elems := 
   set_union string_eq_dec A A'.

(* Variational Elemr List *)
Definition velems_union (A A': velems) : velems := 
    nodupelem (set_union velem_eq_dec A A').

(* Variational Query Type*)
Definition vqtype_union (Q Q': vqtype) : velems := 
     velems_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')). 

Definition avelems_union_vq (Q Q': avelems) : avelems := 
let (A, e) := Q in
 let (A', e') := Q' in
     (velems_union (A < e) (A' < e'), e \/(F) e').

Definition vqtype_union_vq (Q Q': vqtype) : vqtype := 
     (velems_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')), (snd Q) \/(F) (snd Q')).
     (* WRONG (velems_union (fst Q) (fst Q'), (snd Q) \/(F) (snd Q')).*)

(*------------------------------------------------------------------------------*)
(* Plain Elemr List *)
Definition elems_inter (A A': elems) : elems := 
   set_inter string_eq_dec A A'.

(* Variational Elemr List *)
(* NoDupElem A -> NoDupElem (velems_inter A A') *)
Function velems_inter (A A' : velems) {measure List.length A} : velems :=
   match A with 
   | nil          => nil
   | ae a e :: As =>  match existsbElem a A' with
                      | false => velems_inter As A'
                      | true  => let e' := get_annot a A' in
                         (ae a (e /\(F) e') ) :: velems_inter As A'
                      end
   end.
all:intros; simpl; eauto.
Defined.

(*Definition velems_inter (A A': velems) : velems := 
    set_inter velem_eq_dec A A'.*)

(* Variational Query Type*)
Definition vqtype_inter (Q Q': vqtype) : velems := 
     velems_inter (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')).

Definition avelems_inter_vq (Q Q': avelems) : avelems := 
let (A, e) := Q in
 let (A', e') := Q' in
     (velems_inter A A', e /\(F) e').

Definition vqtype_inter_vq (Q Q': vqtype) : vqtype := 
     (velems_inter (fst Q) (fst Q'), (snd Q) /\(F) (snd Q')).

(* Check whether sets are disjoint - A intersect A' = {}*)
Definition is_disjoint_bool (A A': elems) : bool :=
  match elems_inter A A' with
  | [] => true
  | _  => false
  end.


(*--------------------Set Operation End ---------------------------*)


(* ---------------------------------------------------------------
  | Schema property NODupElemRs NoDupElemvQ
   ---------------------------------------------------------------
*)

Definition empRelInempS rn: Prop:= 
forall (S:vschema) c A e, (E[[ snd S]]c) = false /\
In (rn, (A, e)) (fst S) -> In (rn, []) (S[[S]]c).

Definition SatTuples (avs:avelems) : Prop:= 
let A := fst avs in 
  let e := snd avs in 
    forall a ea, In (ae a ea) A -> sat (ea /\(F) e).

Definition SatTuplesR (vr:vrelS) : Prop:= 
let A := getvs vr in 
  let e := getf vr in 
    forall a ea, In (ae a ea) A -> sat (ea /\(F) e).

Definition SatTuplesRs (vs:vschema) : Prop:= forall vr, InVR vr vs -> SatTuplesR vr. (* InVR vr vs -> vr includes (snd vs) *)

Definition NODupElemRs (vs:vschema) : Prop:=
forall vr, InVR vr vs -> NoDupElem (getvs vr).

Inductive NoDupElemvQ: vquery -> Prop :=
  | NoDupElemvQ_rel_v    : forall rn A e, NoDupElem A -> NoDupElemvQ (rel_v (rn, (A, e)))
  | NoDupElemvQ_proj_v   : forall Q vq, NoDupElem (fst Q) -> NoDupElemvQ vq -> 
                                                NoDupElemvQ (proj_v Q vq)
  | NoDupElemvQ_sel_v    : forall vc vq, NoDupElemvQ vq -> 
                                         NoDupElemvQ (sel_v vc vq)
  | NoDupElemvQ_chcQ     : forall e' vq1 vq2, NoDupElemvQ vq1 ->
                             NoDupElemvQ vq2 -> NoDupElemvQ (chcQ e' vq1 vq2)
  | NoDupElemvQ_prod_v   : forall vq1 vq2, NoDupElemvQ vq1 ->
                             NoDupElemvQ vq2 -> NoDupElemvQ (prod_v vq1 vq2)
  | NoDupElemvQ_setU_v   : forall op vq1 vq2, NoDupElemvQ vq1 ->
                             NoDupElemvQ vq2 -> NoDupElemvQ (setU_v op vq1 vq2)
  | NoDupElemvQ_empty_v  : NoDupElemvQ (empty_v).

(*--------------------Schema Property End ---------------------------*)

(* ---------------------------------------------------------------
  | Type of (|-c ) variational condition
   ---------------------------------------------------------------
*)

Inductive vcondtype :fexp -> vqtype -> vcond -> Prop :=
 | litCB_vC : forall e Q b,
     vcondtype e Q (litCB_v b)

  | elemOpV_vC : forall e Q o a k,
  
     (*InElem a ((fst Q) < (snd Q)) ->*)
    (exists e : fexp, In (ae a e) ((fst Q) < (snd Q)) /\ sat(e)) ->
     vcondtype e Q (elemOpV_v o a k)
     (*vcondtype e Q (chcC e' (elemOpV_v o a k) (litCB_v false))*)

  | elemOpA_vC : forall e Q o a1 a2,
    
     (*InElem a1 ((fst Q) < (snd Q)) -> 
     InElem a2 ((fst Q) < (snd Q)) ->*)
    (exists e1 : fexp, In (ae a1 e1) ((fst Q) < (snd Q)) /\ sat(e1)) ->
    (exists e2 : fexp, In (ae a2 e2) ((fst Q) < (snd Q)) /\ sat(e2)) ->
     vcondtype e Q (elemOpA_v o a1 a2) 
     (*vcondtype e Q (chcC (e1 /\(F) e2) (elemOpA_v o a1 a2) (litCB_v false))*)

  | NegC_vC : forall e Q c,
     vcondtype e Q c ->
     vcondtype e Q (negC_v c)
  
  | ConjC_vC : forall e Q c1 c2,
     vcondtype e Q c1 ->
     vcondtype e Q c2 ->
     vcondtype e Q (conjC_v c1 c2)

  | DisjC_vC : forall e Q c1 c2,
     vcondtype e Q c1 ->
     vcondtype e Q c2 ->
     vcondtype e Q (disjC_v c1 c2)

  | ChcC_vC : forall e e' Q c1 c2,
     vcondtype (e /\(F) e') Q c1 ->
     vcondtype (e /\(F) (~(F) e')) Q c2 ->
     vcondtype e Q (chcC e' c1 c2).

Notation "{ e , Q |- vc }" := (vcondtype e Q vc) (e at level 200).

(* ---------------------------------------------------------------
  | Type of (Explicit |= ) variational query
   ---------------------------------------------------------------
*)

Definition addannot (Q:vqtype) (e:fexp): vqtype := (fst Q, (snd Q) /\(F) e).
Notation " Q ^^ e " := (addannot Q e) (at level 70). 


Inductive vtype :fexp -> vschema -> vquery -> vqtype -> Prop :=
  (*   -- EMPTYRELATION-E --  *)
  | EmptyRelation_vE : forall e S {HndpRS:NoDupRn (fst S)} 
                                  {HndpAS: NODupElemRs S}, 
       vtype e S (empty_v) ([], litB false)
  (*  -- intro LESS specific context --
    S |= rn : A^e'  ~sat(e' /\ (~m))
    ------------------------------------ intro less specific context
               m  |= rn : A^e'
   *)
  (*| Relation_vE_fm : forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S}
                           rn A {HA: NoDupElem A} e',
        InVR (rn, (A, e')) S ->
        ~ sat (  e'    /\(F)   (~(F) (e)) ) ->
       vtype e S (rel_v (rn, (A, e'))) (A, e') *)(** variational context is initialized with feature_model which is more general than the overall pc of any relation in vdbms *)
  (*   -- intro MORE specific context --
    S`` |= rn : A^e'  ~sat(e /\ (~e'))
    ------------------------------------  RELATION-E 
               e  |= rn : A^e
   *)
  (*   -- RELATION-E --  *)
  | Relation_vE : forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                          rn {Hrn: empRelInempS rn} A {HA: NoDupElem A} e',
        InVR (rn, (A, e')) S -> 
        sat (e /\(F) e') ->
       (*~ sat (  e    /\(F)   (~(F) (e')) ) ->*) (* why are we restricting ourselves to introduce only more specific context? It's not even maintained in the type system e.g. choice will have less specif context evemn if we start with more specific ones. *)
       vtype e S (rel_v (rn, (A, e' ))) (A, (e /\(F) e'))
  (*   -- PROJECT-E --  *)
  | Project_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} vq {HndpvQ: NoDupElemvQ vq} e' A' 
                           {HndpAA': NoDupElem A'} Q {HndpQ: NoDupElem (fst Q)},
       vtype e S vq (A', e') -> 
       subset_vqtype (Q^^e) (A', e') ->
       vtype e S (proj_v Q vq) (Q^^e)
  (*  -- SELECT-E --  *)
  | Select_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                           vq {HndpvQ: NoDupElemvQ vq}
                            A {HndpAA: NoDupElem A} e' vc,
       vtype e S vq (A, e') ->
       { e, (A, e') |- vc } ->
       vtype e S (sel_v vc vq) (A, e')
  (*  -- CHOICE-E --  *)
  | Choice_vE: forall e e' S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                              vq1 {HndpvQ1: NoDupElemvQ vq1} vq2 {HndpvQ2: NoDupElemvQ vq2} 
                              A1 {HndpAA1: NoDupElem A1} e1 A2 {HndpAA2: NoDupElem A2} e2,
       vtype (e /\(F) e') S vq1 (A1, e1) ->
       vtype (e /\(F) (~(F) e')) S vq2 (A2, e2) ->
       vtype e S (chcQ e' vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
            (*e1 and e2 can't be simultaneously true.*)
  (*  -- PRODUCT-E --  *)
  | Product_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                           vq1 {HndpvQ1: NoDupElemvQ vq1} vq2 {HndpvQ2: NoDupElemvQ vq2}
                            A1 {HndpAA1: NoDupElem A1} e1 A2 {HndpAA2: NoDupElem A2} e2 ,
       vtype e  S vq1 (A1, e1) ->
       vtype e  S vq2 (A2, e2) ->
       vqtype_inter_vq (A1, e1) (A2, e2) =vqtype= (nil, litB false) ->
       (*velems_inter A1 A2 =vset= nil ->*)
       vtype e S (prod_v vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
  (*  -- SETOP-E --  *)
  | SetOp_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                         vq1 {HndpvQ1: NoDupElemvQ vq1} vq2 {HndpvQ2: NoDupElemvQ vq2}
                          A1 {HndpAA1: NoDupElem A1} e1 A2 {HndpAA2: NoDupElem A2} e2 op,
       vtype e S vq1 (A1, e1) ->
       vtype e S vq2 (A2, e2) ->
       equiv_vqtype (A1, e1) (A2, e2) ->
       vtype e S (setU_v op vq1 vq2) (A1, e1).

Notation "{ e , S |= vq | vt }" := (vtype e S vq vt) (e at level 200).

(*Definition vs : vschema := (nil, litB false).
Definition vt : vqtype := (nil, litB false).



Check ({(litB false) , vs |= empty_v | vt }).*)



(*-----------------------Explicit vqtype--------------------------------*)


(* ---------------------------------------------------------------
  | Type of (Implicit |- ) variational query
   ---------------------------------------------------------------
*)

Inductive vtypeImp :fexp -> vschema -> vquery -> vqtype -> Prop :=
  (*   -- EMPTYRELATION-E --  *)
  | EmptyRelation_vE_imp : forall e S {HndpRS:NoDupRn (fst S)} 
                                      {HndpAS: NODupElemRs S}, 
       vtypeImp e S (empty_v) ([], litB false)
  (*| Relation_vE_imp_empty : forall S (HS:NoDupRn (fst S)) rn A_ A' {HA: NoDupElem A'} e_ e',
       InVR (rn, (A', e')) S ->
       vtypeImp (litB true) S (rel_v (rn, (A_, e_))) (A', e')*)
  
  (*   -- RELATION-E --  
    empty |- rn : A^e'  
    ------------------------------------  RELATION-E 
               e  |- rn : A^e
  *)
  (*   -- RELATION-E --  *)
  | Relation_vE_imp : forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                              rn {Hrn: empRelInempS rn} A_ A' {HndpA': NoDupElem A'} e_ e',
       InVR (rn, (A', e')) S ->
       sat (e /\(F) e') ->
       (*SatTuples (A, (e /\(F) e')) ->*)
       vtypeImp e S (rel_v (rn, (A_, e_))) (A', (e /\(F) e')) 
  (*   -- PROJECT-E --  *)
  | Project_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                            vq {HndpvQ: NoDupElemvQ vq} e' A' 
                               {HndpAA': NoDupElem A'} Q {HndpQ: NoDupElem (fst Q)},
       vtypeImp e S vq (A', e') -> 
       subsump_vqtype Q (A', e') -> (* see below why subsump_vqtype is not needed? *)
       vtypeImp e S (proj_v Q vq) (vqtype_inter_vq Q (A', e'))
  (*  -- SELECT-E --  *)
  | Select_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                           vq {HndpvQ: NoDupElemvQ vq}
                            A {HndpAA: NoDupElem A} e' vc,
       vtypeImp e S vq (A, e') ->
       { e, (A, e') |- vc } ->
       vtypeImp e S (sel_v vc vq) (A, e')
  (*  -- CHOICE-E --  *)
  | Choice_vE_imp: forall e e' S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                             vq1 {HndpvQ1: NoDupElemvQ vq1} vq2 {HndpvQ2: NoDupElemvQ vq2}
                              A1 {HndpAA1: NoDupElem A1} e1 A2 {HndpAA2: NoDupElem A2} e2,
       vtypeImp (e /\(F) e') S vq1 (A1, e1) ->
       vtypeImp (e /\(F) (~(F) e')) S vq2 (A2, e2) ->
       vtypeImp e S (chcQ e' vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
            (*e1 and e2 can't be simultaneously true.*)
  (*  -- PRODUCT-E --  *)
  | Product_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                           vq1 {HndpvQ1: NoDupElemvQ vq1} vq2 {HndpvQ2: NoDupElemvQ vq2}
                            A1 {HndpAA1: NoDupElem A1} e1 A2 {HndpAA2: NoDupElem A2} e2 ,
       vtypeImp e  S vq1 (A1, e1) ->
       vtypeImp e  S vq2 (A2, e2) ->
       vqtype_inter_vq (A1, e1) (A2, e2) =vqtype= (nil, litB false) ->
       (*vqtype_inter (A1, e1) (A2, e2) = nil ->*)
       (* velems_inter A1 A2 =vset= nil -> *)
       vtypeImp e  S (prod_v vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
  (*  -- SETOP-E --  *)
  | SetOp_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupElemRs S} 
                         vq1 {HndpvQ1: NoDupElemvQ vq1} vq2 {HndpvQ2: NoDupElemvQ vq2}
                          A1 {HndpAA1: NoDupElem A1} e1 A2 {HndpAA2: NoDupElem A2} e2 op,
       vtypeImp e S vq1 (A1, e1) ->
       vtypeImp e S vq2 (A2, e2) ->
       equiv_vqtype (A1, e1) (A2, e2) ->
       vtypeImp e S (setU_v op vq1 vq2) (A1, e1).  

Notation "{ e , S |- vq | vt }" := (vtypeImp e S vq vt) (e at level 200).

(*-----------------------vqtype--------------------------------*)

(* WHY subsump_vqtype IS NOT NEEDED in Implicit but in Explicit? *)
(* 
-  First let's look at why do we use subsump in Explicit?
-  Explicit Project rule:
-  Project_vE:
       { e S |= vq | (A', e')} -> 
       subset_vqtype (Q^^e) (A', e') ->
       { e S |= (proj_v Q vq) | (Q^^e)

-  subset_vqtype (Q^^e) (A', e') implies
-  forall c, subset (QT[[Q^^e]]c) (QT[[(A', e')]]c) 
-  so that plain projection query: proj QT[[Q^^e]]c QT[[(A', e')]]c is valid

-  So, what is different in Implicit that we don't need it?

-  In Implicit settings, before getting processed, queries go through an additional 
-  explicit annotation stage []S where annotation from not only schema but also 
-  sub-queries gets propagated. For example, annotation for (proj_v Q vq) : 

-  Given { S |- [vq]_S | (As, es)} 
         [ proj_v Q vq ]_S => proj_v (Q /-\ (As, es)) [vq]_S 
  

-  From defn of /-\, forall c, subset (QT[[(Q /-\ (As, es))]]c) (QT[[(As, es)]]c)  *)

(** In context e, forall c, subset (QT[[(Q /-\ (As, es))^^e]]c) (QT[[(As, es/\e)]]c) *) (*

-  So even if, user provided a not subsumpImp Q that would make configured Q, before annotaion
-  to not be subset of configured vq's type for some c, after going though the explicit annotation 
-  stage subset forall c requirement for projection is bound to be fullfilled. Therefore
-  THERE IS NO NEED TO CHECK SUBSUMP CONDITION IN INPLICIT TYPE SYSTEM. IT is guaranteed by the process.
*)
(* ------------------------------------------------------------
  | Type check of plain cond
   ------------------------------------------------------------
*)

Fixpoint condtype (c:cond) (A:elems) : bool :=
  match c with
  | litCB b         => true
  | elemOpV o a n   => true (*if (existsb (string_beq a) A) then true else false *)
  | elemOpA o a1 a2 => true (*if (existsb (string_beq a1) A) 
                                       && (existsb (string_beq a2) A) then true else false *)
  | negC  c     => if (condtype c  A)                   then true else false
  | conjC c1 c2 => if (condtype c1 A) && (condtype c2 A) then true else false
  | disjC c1 c2 => if (condtype c1 A) && (condtype c2 A) then true else false
  end.
Notation "A ||- c " := (condtype c A) (at level 49).

(* ------------------------------------------------------------
  | Type of plain query
   ------------------------------------------------------------
*) 

Fixpoint type_ (q:query) (s:schema) : qtype :=
 match q with
 | (empty)       => []
 | (rel (rn, A)) => if (existsb (relS_beq (rn, A)) s) then A else []
 | (sel c q) => let A := type_ q s in 
                     if (condtype c A) then A else []
 | (proj A q)    => let A' := type_ q s in 
                      if subset_qtype_bool A A' then A else [] 
 | (setU op q1 q2) => if equiv_qtype_bool (type_ q1 s) (type_ q2 s) then type_ q1 s else []
 | (prod  q1 q2) => if (is_disjoint_bool (type_ q1 s) (type_ q2 s)) then 
                          elems_union (type_ q1 s) (type_ q2 s) else []
 end.

Notation "s ||= q " := (type_ q s) (at level 49).

(*------------------------------type'-----------------------------*)





End VDBMS_Encoding.

(*
--------------------------------------------------------------
Appendix.

A1. less_implies_gless (x < nth l) -> (x < (n-end) of l) 
    |forall (a, e) ((a', e')::l), if a <= a', 
    |then a is less than (first element of) all components in l 
    |l is a unique list of paired elements (asscend))ordered on 
    |the first element of each pair 

A2. 
    |asuumption: list elem is non-dup(set) 
    |thus string_comp ( a) ( b) = EQc can't happen

A3.
    | variational elemribute list from queries are explicitly typed. 
    | Assuming variational elemribute list from schema are also explicitly typed.
    | Thus not looking up pc(rel(a)) 

A4. 
    |Using Ackermann Function - computable but not primitive recursive
    |Different argument decreases in different recursive calls
    |Terminates but Coq is not smart enough to figure this out
    |Thus the following trick: inlining a structurally recursive 
    |for the second arguemnt


*)


(* Module SSet := FSetAVL.Make String_as_OT. 

Definition v : Type := SSet.t.*)

(* Locate union. 

Locate eq.

Example s1:string :="Hello".
Example s2:string :="World".

Example l1:list string := nil.

Example l2:list string := cons s1 nil.

Example eq_wl :=
eq (add s2 (add s1 empty)) (add s1 (add s2 empty)).
Eval compute in eq_wl.

Lemma equivE: eq (add s2 (add s1 empty)) (add s1 (add s2 empty)).
Proof. simpl. unfold eq. unfold Equal. intros. split.
intro. 

Print symmetry.

Example string_wl :=
Raw.union Raw add (Raw.add s1 Raw.empty) (l1).
Eval compute in string_wl.

Print SSet.MSet.Raw.inv_ok.

Definition elemss : Type := Raw.t.


(*Definition no_dup l := List.fold_left (fun s x => add x s) l empty.


Lemma union_nil_r: forall (l:Raw.t), Raw.union (no_dup l) [] = no_dup l.
Proof. intros. unfold Raw.union. assert (I: NoDup A). induction A. *)

Check LocallySorted.

Check String_as_OT.compare.

Locate string_dec.

Definition s3 : list string := nil.  *)

(*Lemma veqb_refl:*)

(*Definition vfeqb (v v' : velem) := String.eqb (fst v) (fst v').

Definition veqb (v v' : velem) := String.eqb (fst v) (fst v') && eqb (snd v) (snd v').*)

(*Scheme Equality for velem'. Print velem'_beq. Print fexp_beq. Print string_beq. *)

(*Lemma veqb_refl: forall (a:velem), veqb a a = true.
Proof. destruct a. unfold veqb. simpl. rewrite String.eqb_refl.
rewrite eqb_refl. reflexivity. Qed. *)

(*Definition s : string := "ba".
Definition s' : string := "ab". 
Compute (veqb (s, e) (s, e)).*)

(** Elemribute (string-)comparison function and associated lemmas *)

(* String_as_OT.compare *)
