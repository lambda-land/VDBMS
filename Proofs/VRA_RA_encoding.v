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
Require Import Coq_extended_logic.


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

Module VRA_RA_encoding.


(** -------------------------------------------------------------
  Attribute: Type and Comparison Function, Lemmas
-----------------------------------------------------------------*)
(* Plain Attribute *)
Definition att : Type := string.

Inductive comp : Type := 
  | EQc | LTc | GTc.

(* Variational Attribute *)
(*Definition vatt : Type := (att * fexp)%type.*) (*  assuming always annotated; could've used option*)

Inductive vatt : Type :=
   | ae : att -> fexp -> vatt. 

(* Shorthands for finding/accessing elements *)
Definition fstVatt (v:vatt) : att  := let  'ae x e := v  in x.
Definition sndVatt (v:vatt) : fexp := let  'ae x e := v  in e.

(*----------------------Equality Schemes----------------------------*)

(* Comment :- why not using equality and relevant facts from string libary?
vatt (string, fexp) equality scheme, generates equality scheme for string and fexp.
Although string library provides string equality and all relevant facts, 
I don't know how to make scheme command use that when scheming equality for vatt.
Thus for the sake of consistency i.e. not using two types of string equality, we will
use schemed equality and equality facts from equality module for string like fexp and vatt 
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


Scheme Equality for vatt. 
(* Equalities for vatt*)

(* Decidable Module for vatt *)
Module DT_vatt.
Definition t := vatt.
Definition eq_dec := vatt_eq_dec.
Definition eqb := vatt_beq.
Definition eq :=  @Logic.eq t.
Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
Proof. split. 
       apply internal_vatt_dec_bl.
       apply internal_vatt_dec_lb. 
Qed.
End DT_vatt.

(** Usual Decidable Type Full for vatt *)
Module vattDecF := Equalities.Make_UDTF(DT_vatt).
(* Generate Boolean Equality Facts (e.g. eqb_neq, eqb_refl) for Vatt*)
Module vattBEF := Equalities.BoolEqualityFacts(vattDecF). 

(*----------------------Equality Schemes End----------------------------*)

(** -----------------------att vatt-------------------------- **)


(** ------------------------------------------------------------
  Attribute List
---------------------------------------------------------------*)

(* Plain Attribute List *)
Definition atts : Type := set att.

(*------------------------------------------------------------------------*)

(* Variational Attribute List *)
Definition vatts : Type := set vatt.

(*Lemma not_equal: forall a a' e', a' <> a -> ae a' e' <> ae a e'.
Proof. intros. rewrite <- vattBEF.eqb_neq. simpl.  Admitted.*)

(** ------------------------------------------------------------
  Operations on att element in vatts 
---------------------------------------------------------------*)

(* list Logic specific list of vatts*)

Lemma existsb_In : 
    forall a l, 
         existsb (vatt_beq a) l = true <-> In a l.
Proof. intros. split.
- intro H. rewrite existsb_exists in H.
  destruct H. destruct H.
  rewrite vattDecF.eqb_eq in H0.
  rewrite H0. auto.
- intro H. rewrite existsb_exists.
  exists a. split. auto.
  rewrite vattDecF.eqb_eq. auto.
Qed.

Lemma not_existsb_In : 
    forall a l, 
         existsb (vatt_beq a) l = false <-> ~ In a l.
Proof. intros.  split.
- intro H. rewrite <- existsb_In.
rewrite not_true_iff_false. auto.
- intro H. rewrite <- existsb_In in H.
rewrite not_true_iff_false in H. auto.
Qed.


(* count occurances of attribite a in given list vatt *)
Fixpoint count_occ_Att (a : att) (v:vatts) : nat := 
   match v with
   | []           => O
   | ae x e :: xs => 
       match (string_beq a x) with
       | true  => S (count_occ_Att a xs)
       | false => count_occ_Att a xs
       end
   end.

(* -- eqbAtt --*)

Definition eqbAtt (a: att) (v:vatt) : bool := string_beq a (fstVatt v).

Tactic Notation "simpl_eqbAtt"  := unfold eqbAtt; simpl.
Tactic Notation "eqbAtt_eq" := simpl_eqbAtt; rewrite stringDecF.eqb_eq.

Tactic Notation "simpl_eqbAtt" "in" hyp(H) := unfold eqbAtt in H; simpl in H.
Tactic Notation "eqbAtt_eq" "in" hyp(H) := simpl_eqbAtt in H; rewrite stringDecF.eqb_eq in H.

(* lemma eqbAtt *)
Lemma ex_vatt_fexp : forall A a, (exists x, In x A /\ (eqbAtt a) x = true) <-> (exists e, In (ae a e) A).
Proof. intros. split. 
       - induction A; intro H;
         destruct H as [v Hv];
         simpl in Hv; destruct Hv. 
       + destruct H.
       + destruct H.
         ++ destruct v.
         eqbAtt_eq in H0. 
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
           simpl in He. rewrite He. eqbAtt_eq.
           auto.
        ++ apply IHA in H. destruct H as [v Hv];
           simpl in Hv; destruct Hv. exists v.
           split. simpl. eauto. auto.
Qed.

(* -- existsbAtt -- *)

(* check whether att a exists in list vatt l - existsb from lib *)
Definition existsbAtt (a : att) (l : list vatt) := existsb (eqbAtt a) l.


Lemma existsbAtt_filter: forall a A, existsbAtt a A = false -> 
                           (forall x, ~ In x (filter (eqbAtt a) A)).
Proof. intros. 
unfold existsbAtt in H. 
rewrite <- not_true_iff_false in H.
assert (Hab: ~(exists x, In x A /\ ((eqbAtt a)) x = true)). 
rewrite <- existsb_exists. auto. 
rewrite <- dist_not_exists in Hab. 
rewrite filter_In. apply Hab.
Qed.

(*  -- InAtt  -- *)

Function InAtt (a:att) (l:list vatt) {struct l}: Prop :=
    match l with
    | []           => False
    | ae x e :: xs => x = a \/ InAtt a xs
    end.

(* -- InAtt cons intro -- *)
Lemma InAtt_cons_intro: forall a l, InAtt a l -> forall e, InAtt a ((ae a e)::l).
Proof. intros. simpl. auto. Qed.

(* -- InAtt inversion -- *)
Lemma InAtt_inv_noteq : forall a b l, (fstVatt a) <>  b -> InAtt b (a :: l)
-> InAtt b l.
Proof. intros. destruct a. simpl in *.
destruct H0. contradiction. auto.
Qed.


(* -- InAtt existsbAtt lemma -- *)

Lemma existsbAtt_InAtt : 
    forall a l, existsbAtt a l = true <-> InAtt a l.
Proof. unfold existsbAtt. intros; split; 
functional induction (InAtt a l) using InAtt_ind.
- simpl. congruence. 
- intro H. simpl in H. apply orb_true_iff in H.
  destruct H. 
  ++ eqbAtt_eq in H. 
     eauto.
  ++ eauto.
- eauto. 
- intro H. simpl. apply orb_true_iff.
  destruct H.
  ++ eqbAtt_eq.
     eauto.
  ++ eauto.
Qed.

Lemma not_existsbAtt_InAtt : 
    forall a l, existsbAtt a l = false <-> ~InAtt a l.
Proof. intros.  split.
- intro H. rewrite <- existsbAtt_InAtt.
rewrite not_true_iff_false. auto.
- intro H. rewrite <- existsbAtt_InAtt in H.
rewrite not_true_iff_false in H. auto.
Qed.


Hint Resolve existsbAtt_InAtt not_existsbAtt_InAtt.

Ltac existsbAtt_InAtt := rewrite existsbAtt_InAtt.
Ltac InAtt_existsbAtt := rewrite <- existsbAtt_InAtt.

Tactic Notation "existsbAtt_InAtt" "in" hyp(H) := rewrite existsbAtt_InAtt in H.
Tactic Notation "InAtt_existsbAtt" "in" hyp(H) := rewrite <- existsbAtt_InAtt in H.

Ltac not_existsbAtt_InAtt := rewrite not_existsbAtt_InAtt.
Ltac not_InAtt_existsbAtt := rewrite <- not_existsbAtt_InAtt.

Tactic Notation "not_existsbAtt_InAtt" "in" hyp(H) := rewrite not_existsbAtt_InAtt in H.
Tactic Notation "not_InAtt_existsbAtt" "in" hyp(H) := rewrite <- not_existsbAtt_InAtt in H.

(* -- InAtt Deciadability -- *)

Lemma InAtt_reflect : forall x y, reflect (InAtt x y) (existsbAtt x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply existsbAtt_InAtt.
Qed.


Definition InAtt_dec (a: att) (b: vatts) : {InAtt a b}+{~(InAtt a b)}.
  destruct (InAtt_reflect a b) as [P|Q]. left. apply P. right. apply Q.
Defined.

(* -- InAtt In lemmas -- *)

Lemma existsbAtt_exists :
      forall a l, existsbAtt a l = true <-> exists x, In x l /\ (eqbAtt a) x = true.
Proof. unfold existsbAtt. intros. apply existsb_exists. Qed.

Hint Resolve existsbAtt_exists.

(* R.S. is equiv. to (exists e, In (ae a e) A. *)
Lemma InAtt_In_exvatt : 
      forall a A, InAtt a A  <-> exists x, In x A /\ (eqbAtt a) x = true.
Proof.  intros. InAtt_existsbAtt. eauto. Qed.

Lemma InAtt_In_exfexp : forall (a:att) (A:vatts), InAtt a A  <-> exists e, In (ae a e) A.
Proof.  intros. rewrite <- ex_vatt_fexp. InAtt_existsbAtt. eauto. Qed.

(*Lemma InAtt_In_a : forall (A:vatts), (exists a, In a A <-> InAtt (fstVatt a) A ).
Proof. intros. exists a. InAtt_existsbAtt. eauto. Qed.*)

Lemma In_InAtt_fstVatt : forall (a:vatt) (A:vatts), In a A  -> InAtt (fstVatt a) A.
Proof. intros. rewrite InAtt_In_exvatt. 
       exists a. split. auto.
       unfold eqbAtt. rewrite stringBEF.eqb_refl. reflexivity.
Qed.

(* -- removeAtt  --*)

(* remove all occurances of att a from list vatt A *)
Function removeAtt (a : att) (A: vatts) {struct A} : vatts := 
    match A with 
   | nil => nil
   | ae a' e' :: A' => match (string_beq a a') with
                     | true => removeAtt a A'
                     | false => ae a' e' :: removeAtt a A'
                     end
   end.

(* --InAtt removeAtt lemmas -- *)

(* not used yet but might need them later *)
Theorem notInAtt_removeAtt : forall l x, ~ InAtt x (removeAtt x l).
Proof. intros. 
functional induction (removeAtt x l) using removeAtt_ind.
- simpl. apply neg_false. reflexivity.
- auto.
- simpl. apply Classical_Prop.and_not_or.
  split. + rewrite stringBEF.eqb_neq in e0. 
  eauto. + auto.
Qed.

Lemma InAtt_InAtt_removeAtt : forall l x y, x <> y ->
InAtt x l <-> InAtt x (removeAtt y l).
Proof. intros l x y H. split; induction l; intros  H0. 
- simpl in H0. destruct H0.
- destruct a. simpl. destruct (string_beq y a) eqn: Hya. 
  + simpl in H0. destruct H0.
    ++ rewrite stringDecF.eqb_eq in Hya. 
    rewrite Hya in H . symmetry in H0. contradiction.
    ++ eauto. 
  + simpl. simpl in H0. 
    destruct H0. eauto. 
    eauto.
- simpl in H0. destruct H0.
- destruct a. simpl. simpl in H0.
  destruct (string_beq y a) eqn: Hya.
  ++ eauto.
  ++ simpl in H0. destruct H0.
     +++ eauto.
     +++ eauto.
Qed.


Lemma notInAtt_removeAtt_eq: forall l x, ~ InAtt x l -> removeAtt x l = l.
Proof.
intros l x. induction l; intro H. 
- eauto.
- destruct a as (a, e). simpl. simpl in H. 
  apply Classical_Prop.not_or_and in H. destruct H as [H1 H2].
  destruct(string_beq x a) eqn:Hxa. rewrite stringDecF.eqb_eq in Hxa.
  destruct H1. eauto. rewrite (IHl H2). reflexivity.
Qed.

Lemma In_removeAtt a a' e' A: a <> a' -> 
      In (ae a' e') A <-> In (ae a' e') (removeAtt a A).
Proof. intros H. split; induction A; intros  H0. 
- simpl in H0. destruct H0.
- destruct a0. simpl. destruct (string_beq a a0) eqn: Hya. 
  + simpl in H0. destruct H0.
    ++ rewrite stringDecF.eqb_eq in Hya. 
    inversion H0; subst. destruct H. reflexivity.
    ++ eauto. 
  + simpl. simpl in H0. 
    destruct H0. eauto. 
    eauto.
- simpl in H0. destruct H0.
- destruct a0. simpl. simpl in H0.
  destruct (string_beq a a0) eqn: Hya.
  ++ eauto.
  ++ simpl in H0. destruct H0.
     +++ eauto.
     +++ eauto.
Qed.

Theorem notIn_removeAtt : forall l x e, ~ In (ae x e) (removeAtt x l).
Proof. intros. 
functional induction (removeAtt x l) using removeAtt_ind.
- simpl. apply neg_false. reflexivity.
- auto.
- simpl. apply Classical_Prop.and_not_or.
  split. + rewrite stringBEF.eqb_neq in e1. 
  unfold not. intro e2. unfold not in e1. apply e1.
  inversion e2. reflexivity. + auto.
Qed.

Lemma notIn_notInremoveAtt a a' A: 
~ In a' A -> ~ In a' (removeAtt a A).
Proof. destruct a' as (a', e'). 
destruct (string_eq_dec a a').
- rewrite e. intro H. apply notIn_removeAtt.
- apply In_removeAtt with (e':=e') (A:=A) in n.
intro H. rewrite n in H. assumption.
Qed.


(* not used yet but might need them later *)
(*Lemma InAtt_removeAtt: forall l x y, InAtt x (removeAtt y l) -> InAtt x l /\ x <> y.
Admitted.

Lemma removeAtt_removeAtt_comm : forall l x y,
    removeAtt x (removeAtt y l) = removeAtt y (removeAtt x l).
Admitted.

Lemma removeAtt_removeAtt_eq : forall l x, removeAtt x (removeAtt x l) = removeAtt x l.
Admitted.*)


(*  -- removeAtt List.length -- *)
Lemma remove_reduce (a:att) (l:vatts) : List.length (removeAtt a l) < S(List.length l).
Proof. intros. induction l.
       - unfold removeAtt.  unfold List.length. 
         apply PeanoNat.Nat.lt_0_succ. 
       - simpl. destruct a0. destruct (string_beq a a0). auto. 
         simpl. apply Lt.lt_n_S. auto. 
Qed.

Hint Resolve remove_reduce.

(*-------------------------------------------------------------------------------*)


(* Configuration Variational Attribute List(Set) A[]c (see A3)*)
Fixpoint configVAttSet (vA : vatts) (c : config) : atts :=
  match vA with
  | nil                  => nil
  | cons (ae a e) vas => if semE e c 
                             then (cons a (configVAttSet vas c))
                             else (           configVAttSet vas c )
  end.

Notation "A[[ vA ]] c" := (configVAttSet vA c) (at level 70).

Lemma In_config_true: forall a e A c, In (ae a e) A ->
           (E[[ e]]c) = true -> In a (configVAttSet A c).
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
           (E[[ e]]c) = true) <-> In a (configVAttSet A c).
Proof. intros. split. 
       - induction A; intros; destruct H;
         destruct H.
         + simpl in H. destruct H.
         + destruct a0. simpl in H.
           destruct H. inversion H; subst.
           ++ simpl. rewrite H0. simpl. eauto.
           ++ simpl.  destruct (E[[ f]] c) eqn:Hf.
              +++ simpl. right. apply IHA. 
                  exists x. eauto.
              +++ apply IHA. 
                  exists x. eauto.
       - induction A; intro H.
         + simpl in H. destruct H.
         + destruct a0. simpl in H.
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
      forall c,~ In a (configVAttSet A c).
Proof. intros. induction A. 
       - simpl. simpl in H. auto.
       - simpl in H. destruct a0 as (a', e'). specialize H with e'. 
         apply Classical_Prop.not_or_and in H. destruct H. 
         rewrite <- vattBEF.eqb_neq in H. simpl in H. 
         rewrite fexpBEF.eqb_refl in H. rewrite andb_true_r in H.
         rewrite stringBEF.eqb_neq in H.
         unfold configVAttSet; fold configVAttSet. destruct (E[[ e']] c).
         simpl. apply Classical_Prop.and_not_or. split.
         + assumption.
         + apply IHA. apply H0. 
         simpl in H. destruct (fexp_eq_dec f e). rewrite e0 in H. 
         destruct H. Admitted.*)




(* Lemma InAtt_config: forall a A c, InAtt a A <->
            exists e, ((E[[ e]]c) = true -> In a (configVAttSet A c)).
Proof. intros. split. 
intro H. rewrite InAtt_In_exfexp in H. destruct H as [e He].
exists e. intros H.
apply (In_config _ _ _ c) in He. auto. auto.
intros. destruct H as [e He]. 
apply In_InAtt_config with (c:=c). in He.
Qed. *)

(** -----------------------atts vatts------------------------ **)


(** ------------------------------------------------------------
  Relations 
---------------------------------------------------------------*)
(*relName*)
Definition r : Type := string.

(* Plain Relation Schema - set of plain attributes with a name *)
Definition relS : Type := (r * atts) % type.

(* Variational Relation Schema - annotated set of variational attributes with a name *)
Definition vrelS : Type := (r * (vatts * fexp) ) %type. (*assuming always annotated; could've used option*)

(* Variational Schema (Implicit encoding) *)
Definition vschema : Type := ((set vrelS) * fexp) %type.

Definition getr  (vr:vrelS) : r     := fst vr. 
Definition getvs (vr:vrelS) : vatts := fst (snd vr).
Definition getf  (vr:vrelS) : fexp  := snd (snd vr).


Definition getSvrelS (vs:vschema) : (set vrelS) := fst vs.
Definition getSf  (vs:vschema) : fexp  := snd vs.


(* Configuration Variational Relation R[]c *)
Definition configVRelS (vr : vrelS) (c : config) : relS := if semE (snd (snd vr)) c
                                                         then  (fst vr, (configVAttSet (fst (snd vr)) c)) 
                                                           else  (fst vr, nil).
Notation "R[[ vr ]] c" := (configVRelS vr c) (at level 70).

(** ---------------------------relS-------------------------- **)

(** ------------------------------------------------------------
  Properties/ Function defined on vrelS vschema (Implicit encoding)
---------------------------------------------------------------*)

(* InVR InRn NoDupRn findVR*)
(* In [va:= (ae a ear)] [vr:= (Ar, er) := ({(a, ea)}, er)] *)
Definition InVA (va:vatt) (vr:vrelS) : Prop := 
 let a := fstVatt va in 
  let ear := sndVatt va in 
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
  | relOPI : op -> att -> nat -> cond
  | relOP  : op -> att -> att -> cond
  | compT  : cond -> cond 
  | meetT  : cond -> cond -> cond
  | joinT  : cond -> cond -> cond.

(* Varitational condition*)
Inductive vcond : Type :=
  | litCB_v  : bool -> vcond
  | relOPI_v : op -> att -> nat -> vcond
  | relOP_v  : op -> att -> att -> vcond
  | compT_v  : vcond -> vcond
  | meetT_v  : vcond -> vcond -> vcond
  | joinT_v  : vcond -> vcond -> vcond
  | chcT     : fexp -> vcond -> vcond -> vcond.

(* Configuration Variational Condition C[]c *)
Fixpoint configVCond (vc : vcond) (c : config) : cond :=
  match vc with
  | litCB_v  b          => litCB b
  | relOPI_v o   a   k  => relOPI o a k
  | relOP_v  o   a1  a2 => relOP o a1 a2
  | compT_v  vc         => compT (configVCond vc  c) 
  | meetT_v  vc1 vc2    => meetT (configVCond vc1 c) (configVCond vc2 c)
  | joinT_v  vc1 vc2    => joinT (configVCond vc1 c) (configVCond vc2 c)
  | chcT e   vc1 vc2    => if semE e c then configVCond vc1 c else configVCond vc2 c
  end.

(** -----------------------cond vcond------------------------ **)

(* Variaitonal Query Type *)
Definition avatts : Type := (vatts * fexp) %type. (*assuming always annotated; could've used option*)

(* Configuration Variational Query Type T[]c *)
Definition configaVatts (vqt : avatts) (c : config) : atts := 
      match vqt with 
      |(V, e) => if semE e c then  configVAttSet V c else  nil
      end.

(** -------------------------------------------------------
  Query 
-----------------------------------------------------------*)

Inductive setop : Type := union | inter.

(* Plain Query*)
Inductive query : Type :=
  | rel   : relS    -> query
  (*| sel   : cond    -> query -> query *)
  | proj  : atts    -> query -> query 
  (*| join  : cond    -> query -> query -> query *)
  | prod  : query   -> query -> query 
  | setU  : setop   -> query -> query -> query
  (*| empty : query*).

(* Variaitonal Query *)
Inductive vquery : Type :=
  | rel_v   : vrelS    -> vquery
  (*| sel_v   : vcond    -> vquery -> vquery *)
  | proj_v  : avatts   -> vquery -> vquery 
  | chcQ    : fexp     -> vquery -> vquery -> vquery
  (*| join_v  : vcond    -> vquery -> vquery -> vquery *)
  | prod_v  : vquery   -> vquery -> vquery 
  | setU_v  : setop    -> vquery -> vquery -> vquery
  (*| empty_v : vquery*).

(* Configuration Variational Query Q[]c *)
Fixpoint configVQuery (vq : vquery) (c : config) : query :=
  match vq with
  | rel_v  vr            => rel (configVRelS vr c)
  (*| sel_v  vc  vq        => sel (configVCond vc c) (configVQuery vq c)*)
  | proj_v avatts vq     => proj (configaVatts avatts c) (configVQuery vq c)
  | chcQ e vq1 vq2       => if semE e c then configVQuery vq1 c else configVQuery vq2 c
  (*| join_v vc  vq1 vq2   => join (configVCond vc c) (configVQuery vq1 c) (configVQuery vq2 c)*)
  | prod_v vq1 vq2       => prod (configVQuery vq1 c) (configVQuery vq2 c) 
  | setU_v setop vq1 vq2 => setU setop (configVQuery vq1 c) (configVQuery vq2 c) 
  (*| empty_v              => empty*)
  end.

Notation "Q[[ vq ]] c" := (configVQuery vq c) (at level 70).

(** -----------------------query vquery------------------------ **)


(** ------------------------------------------------------------
  Query Type 
---------------------------------------------------------------*)
(* Plain Query Type *)
Definition qtype  : Type := (atts) %type.

(* Variaitonal Query Type *)
Definition vqtype : Type := avatts. (*(vatts * fexp) %type.*) (*assuming always annotated; could've used option*)

(* Configuration Variational Query Type T[]c *)
Definition configVQtype (vqt : vqtype) (c : config) : qtype := configaVatts vqt c.
      (*match vqt with 
      |(V, e) => if semE e c then  configVAttSet V c else  nil
      end.*)

Notation "AE[[ vqt ]] c" := (configVQtype vqt c) (at level 70).

Lemma configVQtype_nil: forall e c, (configVQtype ([], e) c) = [].
Proof. intros e c. simpl. destruct (E[[ e]] c); reflexivity. Qed.

Definition getvs_vqt (X:vqtype) : vatts := fst X.
Definition getf_vqt (X:vqtype) : fexp := snd X.

(** ---------------------qtype vqtype---------------------- **)



(*-----------------------Functions----------------------------*)


(** ------------------------------------------------------------
  Subsumption (of Variational Set) defintion
---------------------------------------------------------------*)
(* Checks count
   Ex: sublist_bool [1;1;2] [1;2] = false 
*)
Fixpoint sublist_bool (A A': list string): bool :=
    match A with
    | nil => true
    | cons x xs => match set_mem string_eq_dec x A' with 
                   | false => false
                   | true  => sublist_bool xs (set_remove string_eq_dec x A')
                   end
    end. 

(* Also check count
   sublist [1; 1; 2] [1; 2] doesn't hold
*)
Definition sublist (A A': list string):= forall x, (In x A -> In x A') /\ (* In clause is redundant *)
           (count_occ string_eq_dec A x <= count_occ string_eq_dec A' x).

(* Subsumption of Plain Set (Query Type) *)
Definition subsump_qtype_bool (A A': qtype) := sublist_bool A A'.

(* Subsumption of Variational Set (Query Type) *)
Definition subsump_vqtype ( X X': vqtype ) : Prop := forall c, 
    sublist (configVQtype X c) (configVQtype X' c).

(* current def (null is sublist): forall x e,
(In (ae x e) A /\ (exists c, E[[e]]c = true) ) -> (exists e', (In (ae x e') A') /\  (~ sat (e /\(F) (~(F)(e')))) ).*)
(* should be: forall x e,
In (ae x e) A -> (exists e', (In (ae x e') A') /\  (~ sat (e /\(F) (~(F)(e')))) ). *)

(*
subsump_vatts_exp (<_e) : A <_e A' [need for proj_v A A']
  If it entails forall c, [A]c to be sublist( <_a) of [A']c ... (1), where 
sublist is defined as, forall x, count x [A]c <= count x [A']c [note: {} <_a {any}],
it would be a reasonable choice as then, after configuration, proj [A]c [A']c, is a valid plain query in RA.
  Therefore, forall (a,e), In (a, e) A we have two cases that would make [A]c valid configured sublist of [A']c.
Case 1: ~ (sat e) 
  [ a will never be in [A]c, any c. thus, we don't need a att-matching variational attribute in A'. 
    i.e. It doesn't matter whether there exists e', In (a, e') A']
Case 2: sat e -> exists e', In (a, e') A' /\ (e -> e'). (not true if A A' is not NoDupAtt)
    Explanation: let A = {(a, e1) (a, e2) } and A' = {(a, e3, (a, e4)}
                 For count a [A]c <= count a [A']c to hold,
                 i.  e1 xor e2  -> ( e3 \/ e4 ) [ok if both]
                 ii. e1 /\ e2 -> e3 /\ e4 [both has to be true]
    For a single tuple, In (a, e1) A -> we don't need a single e' that is always true if e1 true i.e. e1 -> e'
                          any one e' in A' being true when e1 is true is enough. 
    Also, we need for all tuples with attribute a condition. if all of them is true, at least same number of e' needs to true in A'.
    However, to make things easier we can assume A and A' is NoDupAtt which can be safely assumed in our VDBMS.
    Then, e -> e' is sufficient. 
*)
(** ------------------------------
Definition subsump_vatts_exp A A': forall (a, e), [In (a, e) A /\ (sat e)] -> exists e', [In (a, e') A' /\ (e -> e')].
   where A A' is NoDupAtt. 
================================= *)
(**  Lemma subsump_vatts_correctness (NoDupAtt A)(NoDupAtt A'): 
       subsump_vatts_exp A A' <-> sublist (configVAttSet A c) (configVAttSet A' c). *)

(* [Note: forall (a, e), In (a, e) A  -> exists e', In (a, e') A' /\ (e -> e'). is unreasonable/ not necessary/ over restriction, 
      because if e is not sat, then, there is no reason to ask/check for attribute a in A' with some e'.] *)
  
(* Now if we restrict our A to only hold satisfiable tuples, then definition seems to get simplified into below [close to above]. 
but it does NOT as definition then would hold for any not SatTuples A, potentially with few sat and few not_sat tuples. If none of 
the tuples is sat, then it's alright. but if there are some sat, we need exists clause for those sat. i.e. we need to check each 
tuple based on their satisfiability, if sat then need exists clause to be true otherwise not. An overall satiafiable clause doesn't
attain that. *)

(** ------------------------------
Definition subsump_vatts_exp_Wrong A A' : Prop := SatTuples A -> forall (a, e), In (a, e) A  -> exists e', In (a, e') A' /\ (e -> e').
================================= *)

(** why don't we need  SatTuples A' as well? ==> A' doesn't not need to be SatTuples (all sat) but to have sat e's (exists sat) i.e.
exists e', [sat e' /\ In (a, e') A' /\ (e -> e')]. However, (e -> e' -> sat e') thus can remove sat e'*) 

(** ------------------------------ 
Definition subsump_vqtype_exp X X': forall (a, e), [In (a, e) (fst X) /\ sat (e/\snd X)]  -> exists e', In (a, e') X' /\ (e/\snd X -> e'/\snd X').
   where (fst X) (fst X') is NoDupAtt.
================================= *) 
(**  Lemma subsump_vqtype_correctness (NoDupAtt (fst X))(NoDupAtt (fst X')): 
                subsump_vqtype_exp X X' <-> sublist (configVQtype X c) (configVQtype X' c). *)

(* SatATuples X := SatTuples (push_annot (fst X, snd X)).  [SatTuples (fst X) /\ Sat (snd X)] doesn't guarantee sat (e/\snd X). *)

(* Similar reasoning gives us *)
(** ------------------------------
Definition subsump_vatts_imp A A' : forall (a, e), In (a, e) A /\ sat(e) -> exists e', In (a, e') A' /\ sat(e /\ e').
       where A A' is NoDupAtt.
==================================
Definition subsump_vatts_imp_Wrong A A' [HA: SatTuples A] : forall (a, e), In (a, e) A  -> exists e', In (a, e') A' /\ sat(e /\ e').
---------------------------------- 
Definition subsump_vqtype_imp X X' : forall (a, e), In (a, e) A /\ sat (e/\snd X)  -> exists e', In (a, e') A' /\ sat(e/\snd X /\ e'/\snd X').
    where (fst X) (fst X') is NoDupAtt.
================================= *)

(* Lemma : sat (A /\ B) -> sat A /\ sat B. but not <- *)

(*Definition subsump_vatts_exp (A A': vatts) :Prop := forall x e,
In (ae x e) A /\ sat e  -> exists e', In (ae x e') A' /\  (~ sat (e /\(F) (~(F)(e')))).*)

Definition subsump_vatts_exp (A A': vatts) :Prop := forall x e c,
In (ae x e) A /\ ((E[[ e]]c) = true)  -> 
       exists e', In (ae x e') A' /\  (E[[ e']]c) = true.


(** A and A' has to be NoDupAtt *)
Definition subsumpImp_vatts (A A': vatts) :Prop := 
forall x e, In (ae x e) A (*/\ sat e*) -> exists e', In (ae x e') A'. (*/\ sat(e /\(F) e').*)
(*In (ae x e) A -> (exists e', (In (ae x e') A') /\ sat(e /\(F) e')).*)

(** (fst X) and (fst X') has to be NoDupAtt *)
Definition subsumpImp_vqtype ( X X': vqtype) : Prop := 
let (A, ea) := X in 
  let (A', ea') := X' in 
    forall x e, In (ae x e) A (*/\ sat (e /\(F) ea)*) -> 
                       exists e', In (ae x e') A'. (* /\ sat (e /\(F) ea /\(F) e' /\(F) ea').*)
(* subsumpImp_vatts (fst X) (fst X') /\ sat((snd X) /\(F) (snd X')). *)


(*Lemma subsump_vatts_exp_ind A a ea A': subsump_vatts_exp A (ae a ea :: A') ->
(forall x e, In (ae x e) A /\ sat e -> exists e', (ae x e') = (ae a ea) /\ sat(e /\(F) e'))
    \/ subsump_vatts_exp A A'.
Proof. intros H. 
unfold subsump_vatts_exp in H. simpl in H. 
rewrite and_distributes_over_or in H.*)


Lemma subsumpImp_vatts_refl A: subsumpImp_vatts A A.
Proof. unfold subsumpImp_vatts. intros x e H.
exists e. auto. (*destruct H as [HIn Hsat]. split. 
assumption. 
unfold sat. simpl. unfold sat in Hsat. 
destruct Hsat as [c Hsat]. exists c. 
rewrite Hsat. auto.*)
Qed.

(* Wrong move: restrict Schema and query to have following assumption so that, if In (a, e) A then, sat e *)
(* Definition SatTuples (A: vatts) : Prop := forall a e, In (ae a e) A -> sat e.

Definition SatATuples (X: vqtype) : Prop := forall a e, In (ae a e) (fst X) -> sat (e /\(F) (snd X)).

Lemma SatATuples_SatTuples: forall X, SatATuples X -> SatTuples (fst X).
Proof. Admitted. *)

(*  Relating subsumpExp with subsumpImp *)


(*----------------------subsump--------------------------------*)


(** ------------------------------------------------------------
  Equivalence (of (Variational) Set) definition
---------------------------------------------------------------*)
(* Plain Set (Query Type) Equivalence*)
Fixpoint equiv_atts_bool (A A': qtype) : bool := 
    match A with
    | nil => match A' with 
             | nil => true
             | cons _ _ => false
             end
    | cons x xs => match set_mem string_eq_dec x A' with 
                   | false => false
                   | true  => equiv_atts_bool xs (set_remove string_eq_dec x A')
                   end
    end.

Definition equiv_atts : relation atts:= 
       fun A A' => forall a, (In a A <-> In a A') /\ 
                      ( count_occ string_eq_dec A a = count_occ string_eq_dec A' a).

Infix "=a=" := equiv_atts (at level 50) : type_scope.

(* Variational Set (non-annnot-Var Attr) Equivalence (Only needed for next one)*)
Definition equiv_vatts : relation vatts := 
        fun A A' => forall c, configVAttSet A c =a= configVAttSet A' c.

Infix "=va=" := equiv_vatts (at level 50) : type_scope.


Definition equiv_qtype_bool (A A': qtype) := equiv_atts_bool A A'.

Definition equiv_qtype : relation qtype := 
        fun A A' => A =a= A'.

Infix "=t=" := equiv_qtype (at level 50) : type_scope.

(* Variational Set (annotated-Var Query Type) Equivalence *)
Definition equiv_vqtype : relation vqtype := 
        (*fun X X' => forall c, configVQtype A c =a= configVAttSet A' c. *)
        fun X X' => (fst X) =va= (fst X') /\ (snd X) =e= (snd X').

Infix "=T=" := equiv_vqtype (at level 50) : type_scope.

(* equiv_qtype is Equivalence relation *)
Remark equiv_atts_refl: Reflexive equiv_atts.
Proof.
  intros A a. split; reflexivity.
Qed.

Remark equiv_atts_sym : Symmetric equiv_atts.
Proof.
  intros A A' H a.
  split; symmetry;
  apply H.
Qed.

Remark equiv_atts_trans : Transitive equiv_atts.
Proof.
  intros A A'' A' H1 H2 a.
  split; try (transitivity (In a A'')); 
         try (transitivity (count_occ string_eq_dec A'' a));
   try (apply H1);
   try (apply H2). 
Qed.

Instance atts_Equivalence : Equivalence equiv_atts := {
    Equivalence_Reflexive := equiv_atts_refl;
    Equivalence_Symmetric := equiv_atts_sym;
    Equivalence_Transitive := equiv_atts_trans }.

Instance qtype_Equivalence : Equivalence equiv_qtype := {
    Equivalence_Reflexive := equiv_atts_refl;
    Equivalence_Symmetric := equiv_atts_sym;
    Equivalence_Transitive := equiv_atts_trans }.

(* equiv_vatts is Equivalence relation *)

Remark equiv_vatts_refl: Reflexive equiv_vatts.
Proof.
  intros A a. reflexivity.
Qed.

Remark equiv_vatts_sym : Symmetric equiv_vatts.
Proof.
  intros A A' H a.
  symmetry.
  apply H.
Qed.

Remark equiv_vatts_trans : Transitive equiv_vatts.
Proof.
  intros A A'' A' H1 H2 a.
  transitivity (configVAttSet A'' a).
    apply H1.
    apply H2.
Qed.

(** vatts equivalence is an equivalence relation. *)
Instance vatts_Equivalence : Equivalence equiv_vatts := {
    Equivalence_Reflexive := equiv_vatts_refl;
    Equivalence_Symmetric := equiv_vatts_sym;
    Equivalence_Transitive := equiv_vatts_trans }.

(* equiv_vqtype is Equivalence relation *)

Remark equiv_vqtype_refl: Reflexive equiv_vqtype.
Proof.
  intro X. destruct X. unfold equiv_vqtype. split; 
  reflexivity. 
Qed.

Remark equiv_vqtype_sym : Symmetric equiv_vqtype.
Proof.
  intros X Y. intros H. destruct X, Y. unfold equiv_vqtype. 
  unfold equiv_vqtype in H. destruct H. split. symmetry. 
  apply H. symmetry. 
  apply H0.
Qed.


Remark equiv_vqtype_trans : Transitive equiv_vqtype.
Proof.
  intros X Y Z. intros H1 H2. 
  destruct X as (vx, fx), Y as (vy, fy), Z as (vz, fz). 
  unfold equiv_vqtype in H1. destruct H1 as [H11 H12].
  unfold equiv_vqtype in H2. destruct H2 as [H21 H22].
  unfold equiv_vqtype. split.
  transitivity (fst (vy, fy)).
    apply H11.
    apply H21.
  transitivity (snd (vy, fy)).
    apply H12.
    apply H22.
Qed.

(** vatts equivalence is an equivalence relation. *)
Instance vqtype_Equivalence : Equivalence equiv_vqtype := {
    Equivalence_Reflexive := equiv_vqtype_refl;
    Equivalence_Symmetric := equiv_vqtype_sym;
    Equivalence_Transitive := equiv_vqtype_trans }.

(*Lemma rewrite_equiv: forall a b c, a=a=b->
b=a=c-> a=a=c.
Proof. intros. rewrite <- H in H0. apply H0.
Qed.*)




(** ------------------------------------------------------------
  Restrict vatts to have no duplicate atts 
                       i.e. same atts with diff fexp
---------------------------------------------------------------*)

(*stronger condition than mere NoDup vatts*)

Inductive NoDupAtt : list vatt -> Prop :=
  | NoDupAtt_nil : NoDupAtt nil
  | NoDupAtt_cons : forall a e l, ~ InAtt a l -> NoDupAtt l 
                            -> NoDupAtt ((ae a e)::l).



Definition extract_e (a : att) (A: vatts) : fexp :=  
                   fold_right Feature.join (litB false) (map (sndVatt) (filter (eqbAtt a) A)). 

(*--------------------------------------------------------*)


(* -- nodupatt -- *)

(* remove duplicate attributes - merging them through fexp_union *)
Function nodupatt (v : list vatt) {measure List.length v} : list vatt :=
   match v with 
   | nil          => nil
   | ae a e :: vs =>  match existsbAtt a vs with
                      | false => ae a e :: nodupatt vs
                      | true  => let e' := extract_e a vs in
                         (ae a (e \/(F) e') ) :: nodupatt (removeAtt a vs)
                      end
   end.
all:intros; simpl; eauto.
Defined.

Ltac simpl_nodupatt := rewrite nodupatt_equation.

Hint Resolve nodupatt_equation.

Lemma nodupatt_nil : nodupatt [] = [].
Proof. eauto. Qed.

Lemma nodupatt_not_in_cons : forall a e l,
      ~ InAtt a l -> nodupatt (ae a e::l) = ae a e :: nodupatt l.
Proof. intros. simpl_nodupatt. 
simpl. destruct (existsbAtt a l) eqn:Hf.
rewrite <- existsbAtt_InAtt in H. contradiction.
auto. Qed.

Lemma nodupatt_in_cons : forall a e l,
        InAtt a l -> 
          nodupatt (ae a e::l) = ae a (e \/(F) extract_e a l) 
                     :: nodupatt (removeAtt a l).
Proof. intros. simpl_nodupatt. simpl.
rewrite <- existsbAtt_InAtt in H. rewrite H. auto.
Qed.



(*Lemma nodup_fixed_point : forall (l : list A),
    NoDup l -> nodup l = l.*)


(*-----------------------NoDup_atts_in_vatts--------------------------*)

(** ------------------------------------------------------------
  Push (attribute list) annotation (to individual attributes)
---------------------------------------------------------------*)
(* 
  |Push annotation/ fexp into Attr List
  |A^e = {a^e1, b, c^e2,...}^e
  |push_annot A e = {a^(e1/\e), b^e, c^(e2/\e),...}
*)
Fixpoint push_annot (A: vatts) (m: fexp) : (vatts):=
  match A with
  | nil => nil
  | ae x e :: xs => (ae x (e /\(F) m)) :: push_annot xs m
  end.

Definition avatts_vatts (X:avatts) : vatts := push_annot (fst X) (snd X).

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

(*Definition subsumpImp_vqtype ( X X': vqtype) :Prop := 
subsumpImp_vatts (avatts_vatts X) (avatts_vatts X').*)

(*------------------------push_annot---------------------------*)

(** ------------------------------------------------------------
  Set Operation for Attribute List(Set) & Query type(annotated attr list)
  Union Intersection
---------------------------------------------------------------*)
(* Plain Attr List *)
Definition atts_union (A A': atts) : atts := 
   set_union string_eq_dec A A'.

(* Variational Attr List *)
Definition vatts_union (A A': vatts) : vatts := 
    nodupatt (set_union vatt_eq_dec A A').

(* Variational Query Type*)
Definition vqtype_union (Q Q': vqtype) : vatts := 
     vatts_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')). 

Definition vqtype_union_vq (Q Q': vqtype) : vqtype := 
     (vatts_union (fst Q) (fst Q'), (snd Q) \/(F) (snd Q')).

(*------------------------------------------------------------------------------*)
(* Plain Attr List *)
Definition atts_inter (A A': atts) : atts := 
   set_inter string_eq_dec A A'.

(* Variational Attr List *)
(* NoDupAtt A -> NoDupAtt (vatts_inter A A') *)
Function vatts_inter (A A' : list vatt) {measure List.length A} : list vatt :=
   match A with 
   | nil          => nil
   | ae a e :: As =>  match existsbAtt a A' with
                      | false => vatts_inter As A'
                      | true  => let e' := extract_e a A' in
                         (ae a (e /\(F) e') ) :: vatts_inter As A'
                      end
   end.
all:intros; simpl; eauto.
Defined.

(*Definition vatts_inter (A A': vatts) : vatts := 
    set_inter vatt_eq_dec A A'.*)

(* Variational Query Type*)
Definition vqtype_inter (Q Q': vqtype) : vatts := 
     vatts_inter (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')).

Definition vqtype_inter_vq (Q Q': vqtype) : vqtype := 
     (vatts_inter (fst Q) (fst Q'), (snd Q) /\(F) (snd Q')).

(* Check whether sets are disjoint - A intersect A' = {}*)
Definition is_disjoint_bool (A A': atts) : bool :=
  match atts_inter A A' with
  | [] => true
  | _  => false
  end.


(*--------------------Set Operation End ---------------------------*)


(* ---------------------------------------------------------------
  | Schema property NODupAttRs NoDupAttvQ
   ---------------------------------------------------------------
*)

Definition SatTuples (avs:avatts) : Prop:= 
let A := fst avs in 
  let e := snd avs in 
    forall a ea, In (ae a ea) A -> sat (ea /\(F) e).

Definition SatTuplesR (vr:vrelS) : Prop:= 
let A := getvs vr in 
  let e := getf vr in 
    forall a ea, In (ae a ea) A -> sat (ea /\(F) e).

Definition SatTuplesRs (vs:vschema) : Prop:= forall vr, InVR vr vs -> SatTuplesR vr. (* InVR vr vs -> vr includes (snd vs) *)

Definition NODupAttRs (vs:vschema) : Prop:=
forall vr, InVR vr vs -> NoDupAtt (getvs vr).

Inductive NoDupAttvQ: vquery -> Prop :=
  | NoDupAttvQ_proj_v : forall Q vq, NoDupAtt (fst Q) -> NoDupAttvQ vq -> 
                                                NoDupAttvQ (proj_v Q vq)
  | NoDupAttvQ_rel_v : forall rn A e, NoDupAttvQ (rel_v (rn, (A, e)))
  | NoDupAttvQ_chcQ : forall e' vq1 vq2, NoDupAttvQ vq1 ->
                             NoDupAttvQ vq2 -> NoDupAttvQ (chcQ e' vq1 vq2)
  | NoDupAttvQ_prod_v : forall vq1 vq2, NoDupAttvQ vq1 ->
                             NoDupAttvQ vq2 -> NoDupAttvQ (prod_v vq1 vq2)
  | NoDupAttvQ_setU_v : forall op vq1 vq2, NoDupAttvQ vq1 ->
                             NoDupAttvQ vq2 -> NoDupAttvQ (setU_v op vq1 vq2).

(*--------------------Schema Property End ---------------------------*)


(* ---------------------------------------------------------------
  | Type of (Explicit |= ) variational query
   ---------------------------------------------------------------
*)

Definition addannot (Q:vqtype) (e:fexp): vqtype := (fst Q, (snd Q) /\(F) e).
Notation " Q ^^ e " := (addannot Q e) (at level 70). 


Inductive vtype :fexp -> vschema -> vquery -> vqtype -> Prop :=
  (*  -- intro LESS specific context --
    S |= rn : A^e'  ~sat(e' /\ (~m))
    ------------------------------------ intro less specific context
               m  |= rn : A^e'
   *)
  (*| Relation_vE_fm : forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S}
                           rn A {HA: NoDupAtt A} e',
        InVR (rn, (A, e')) S ->
        ~ sat (  e'    /\(F)   (~(F) (e)) ) ->
       vtype e S (rel_v (rn, (A, e'))) (A, e') *)(** variational context is initialized with feature_model which is more general than the overall pc of any relation in vdbms *)
  (*   -- intro MORE specific context --
    S`` |= rn : A^e'  ~sat(e /\ (~e'))
    ------------------------------------  RELATION-E 
               e  |= rn : A^e
   *)
  | Relation_vE : forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                        rn A {HA: NoDupAtt A} e',
        InVR (rn, (A, e')) S ->
       ~ sat (  e    /\(F)   (~(F) (e')) ) ->
       vtype e S (rel_v (rn, (A, e' ))) (A, e)
  (*   -- PROJECT-E --  *)
  | Project_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} vq {HndpvQ: NoDupAttvQ vq} e' A' 
                           {HndpAA': NoDupAtt A'} Q {HndpQ: NoDupAtt (fst Q)},
       vtype e S vq (A', e') -> 
       subsump_vqtype (Q^^e) (A', e') ->
       vtype e S (proj_v Q vq) (Q^^e)
  (*  -- CHOICE-E --  *)
  | Choice_vE: forall e e' S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                              vq1 {HndpvQ1: NoDupAttvQ vq1} vq2 {HndpvQ2: NoDupAttvQ vq2} 
                              A1 {HndpAA1: NoDupAtt A1} e1 A2 {HndpAA2: NoDupAtt A2} e2,
       vtype (e /\(F) e') S vq1 (A1, e1) ->
       vtype (e /\(F) (~(F) e')) S vq2 (A2, e2) ->
       vtype e S (chcQ e' vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
            (*e1 and e2 can't be simultaneously true.*)
  (*  -- PRODUCT-E --  *)
  | Product_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                           vq1 {HndpvQ1: NoDupAttvQ vq1} vq2 {HndpvQ2: NoDupAttvQ vq2}
                            A1 {HndpAA1: NoDupAtt A1} e1 A2 {HndpAA2: NoDupAtt A2} e2 ,
       vtype e  S vq1 (A1, e1) ->
       vtype e  S vq2 (A2, e2) ->
       vqtype_inter (A1, e1) (A2, e2) = nil ->
       vtype e S (prod_v vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
  (*  -- SETOP-E --  *)
  | SetOp_vE: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                         vq1 {HndpvQ1: NoDupAttvQ vq1} vq2 {HndpvQ2: NoDupAttvQ vq2}
                          A1 {HndpAA1: NoDupAtt A1} e1 A2 {HndpAA2: NoDupAtt A2} e2 op,
       vtype e S vq1 (A1, e1) ->
       vtype e S vq2 (A2, e2) ->
       equiv_vqtype (A1, e1) (A2, e2) ->
       vtype e S (setU_v op vq1 vq2) (A1, e1).
(* (*  -- SELECT-E --  *)
   | Select_vE: forall e S vq A e',
       vtype e S vq (A, e') ->
       vtype e S (sel_v c vq) (A, e'). *) 

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
  (*| Relation_vE_imp_empty : forall S (HS:NoDupRn (fst S)) rn A_ A' {HA: NoDupAtt A'} e_ e',
       InVR (rn, (A', e')) S ->
       vtypeImp (litB true) S (rel_v (rn, (A_, e_))) (A', e')*)
  (*   -- intro MORE specific context --
    empty |- rn : A^e'  ~sat(e /\ (~e'))
    ------------------------------------  RELATION-E 
               e  |- rn : A^e
  *)
  | Relation_vE_imp : forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} rn A_ A' 
                                 {HndpA': NoDupAtt A'} e_ e',
       InVR (rn, (A', e')) S ->
       (*sat (e /\(F) e') *)
       (*SatTuples (A, (e /\(F) e')) ->*)
       vtypeImp e S (rel_v (rn, (A_, e_))) (A', (e /\(F) e')) (** variational context is initialized with feature_model which is more general than the overall pc of any relation in vdbms *)
  (*   -- PROJECT-E --  *)
  | Project_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} vq {HndpvQ: NoDupAttvQ vq} e' A' 
                               {HndpAA': NoDupAtt A'} Q {HndpQ: NoDupAtt (fst Q)},
       vtypeImp e S vq (A', e') -> 
       subsumpImp_vqtype Q (A', e') ->
       vtypeImp e S (proj_v Q vq) (vqtype_inter_vq Q (A', e'))
  (*  -- CHOICE-E --  *)
  | Choice_vE_imp: forall e e' S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                             vq1 {HndpvQ1: NoDupAttvQ vq1} vq2 {HndpvQ2: NoDupAttvQ vq2}
                              A1 {HndpAA1: NoDupAtt A1} e1 A2 {HndpAA2: NoDupAtt A2} e2,
       vtypeImp (e /\(F) e') S vq1 (A1, e1) ->
       vtypeImp (e /\(F) (~(F) e')) S vq2 (A2, e2) ->
       vtypeImp e S (chcQ e' vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
            (*e1 and e2 can't be simultaneously true.*)
  (*  -- PRODUCT-E --  *)
  | Product_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                           vq1 {HndpvQ1: NoDupAttvQ vq1} vq2 {HndpvQ2: NoDupAttvQ vq2}
                            A1 {HndpAA1: NoDupAtt A1} e1 A2 {HndpAA2: NoDupAtt A2} e2 ,
       vtypeImp e  S vq1 (A1, e1) ->
       vtypeImp e  S vq2 (A2, e2) ->
       vqtype_inter (A1, e1) (A2, e2) = nil ->
       vtypeImp e  S (prod_v vq1 vq2)
        (vqtype_union_vq (A1, e1) (A2, e2))
  (*  -- SETOP-E --  *)
  | SetOp_vE_imp: forall e S {HndpRS:NoDupRn (fst S)} {HndpAS: NODupAttRs S} 
                         vq1 {HndpvQ1: NoDupAttvQ vq1} vq2 {HndpvQ2: NoDupAttvQ vq2}
                          A1 {HndpAA1: NoDupAtt A1} e1 A2 {HndpAA2: NoDupAtt A2} e2 op,
       vtypeImp e S vq1 (A1, e1) ->
       vtypeImp e S vq2 (A2, e2) ->
       equiv_vqtype (A1, e1) (A2, e2) ->
       vtypeImp e S (setU_v op vq1 vq2) (A1, e1).
(* (*  -- SELECT-E --  *)
   | Select_vE: forall e S vq A e',
       vtype e S vq (A, e') ->
       vtype e S (sel_v c vq) (A, e'). *) 

Notation "{ e , S |- vq | vt }" := (vtypeImp e S vq vt) (e at level 200).

(*-----------------------vqtype--------------------------------*)

(* ------------------------------------------------------------
  | Type of plain query
   ------------------------------------------------------------
*)
Fixpoint type_ (q:query) : qtype :=
 match q with
 | (rel (rn, A)) => A
 | (proj A q)    => let A' := type_ q in 
                      if subsump_qtype_bool A A' then A else nil 
 | (setU op q1 q2) => if equiv_qtype_bool (type_ q1) (type_ q2) then type_ q1 else nil
 | (prod  q1 q2) => if (is_disjoint_bool (type_ q1) (type_ q2)) then 
                          atts_union (type_ q1) (type_ q2) else nil
 end.

Notation "||= q " := (type_ q) (at level 49).

(*------------------------------type'-----------------------------*)





End VRA_RA_encoding.

(*
--------------------------------------------------------------
Appendix.

A1. less_implies_gless (x < nth l) -> (x < (n-end) of l) 
    |forall (a, e) ((a', e')::l), if a <= a', 
    |then a is less than (first element of) all components in l 
    |l is a unique list of paired elements (asscend))ordered on 
    |the first element of each pair 

A2. 
    |asuumption: list att is non-dup(set) 
    |thus string_comp ( a) ( b) = EQc can't happen

A3.
    | variational attribute list from queries are explicitly typed. 
    | Assuming variational attribute list from schema are also explicitly typed.
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

Definition attss : Type := Raw.t.


(*Definition no_dup l := List.fold_left (fun s x => add x s) l empty.


Lemma union_nil_r: forall (l:Raw.t), Raw.union (no_dup l) [] = no_dup l.
Proof. intros. unfold Raw.union. assert (I: NoDup A). induction A. *)

Check LocallySorted.

Check String_as_OT.compare.

Locate string_dec.

Definition s3 : list string := nil.  *)

(*Lemma veqb_refl:*)

(*Definition vfeqb (v v' : vatt) := String.eqb (fst v) (fst v').

Definition veqb (v v' : vatt) := String.eqb (fst v) (fst v') && eqb (snd v) (snd v').*)

(*Scheme Equality for vatt'. Print vatt'_beq. Print fexp_beq. Print string_beq. *)

(*Lemma veqb_refl: forall (a:vatt), veqb a a = true.
Proof. destruct a. unfold veqb. simpl. rewrite String.eqb_refl.
rewrite eqb_refl. reflexivity. Qed. *)

(*Definition s : string := "ba".
Definition s' : string := "ab". 
Compute (veqb (s, e) (s, e)).*)

(** Attribute (string-)comparison function and associated lemmas *)

(* String_as_OT.compare *)
