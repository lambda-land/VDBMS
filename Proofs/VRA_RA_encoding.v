(** Variational relational algebra *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
(*Require Import Maps.*)
Require Export List.
(*Require Export Arith.
Require Export String.*)
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
Import Coq.Lists.List.ListNotations.
Load CpdtTactics.


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

(** -------------------------------------------------------------
  Logic Lemmas
-----------------------------------------------------------------*)

(* ~ exists x, P -> forall x, ~ P x *)
Lemma dist_not_exists {X:Type} (P:X->Prop): 
         ~(exists x, P x) -> forall x, ~ P x.
Proof. intro H.
 pose proof (fun x Px => H (ex_intro _ x Px)) as H'; simpl in H'.
 auto.
Qed.

(*---------------------------------------------------------------*)

(** -------------------------------------------------------------
  Attribute: Type and Comparison Function, Lemmas
-----------------------------------------------------------------*)
(* Plain Attribute *)
Definition att : Type := string.

Inductive comp : Type := 
  | EQc | LTc | GTc.

(* Variational Attribute *)
(*Definition vatt : Type := (att * fexp)%type.*) (*assuming always annotated; could've used option*)

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

(** -----------------------att vatt-------------------------- **)


(** ------------------------------------------------------------
  Attribute List
---------------------------------------------------------------*)

(* Plain Attribute List *)
Definition atts : Type := set att.

(*------------------------------------------------------------------------*)

(* Variational Attribute List *)
Definition vatts : Type := set vatt.

Fixpoint count_occ_Att (a : att) (v:vatts) : nat := 
   match v with
   | []           => O
   | ae x e :: xs => 
       match (string_beq a x) with
       | true  => S (count_occ_Att a xs)
       | false => count_occ_Att a xs
       end
   end.

Definition eqbAtt (a: att) (v:vatt) : bool := string_beq a (fstVatt v).

(* similar to list existsb *)
Definition existsbAtt (a : att) (l : list vatt) := existsb (eqbAtt a) l.

Lemma existsbAtt_exists :
      forall a l, existsbAtt a l = true <-> exists x, In x l /\ (eqbAtt a) x = true.
Proof. unfold existsbAtt. intros. apply existsb_exists. Qed.

Hint Resolve existsbAtt_exists.

(*Fixpoint existsbAtt (a : att) (l : list vatt) : bool := 
   match l with
   | []           => false
   | ae x e :: xs => (string_beq a x) || existsbAtt a xs
   end.*)

(* similar to list In *)
Function InAtt (a:att) (l:list vatt) {struct l}: Prop :=
    match l with
    | []           => False
    | ae x e :: xs => x = a \/ InAtt a xs
    end.

Check InAtt_ind.

Lemma existsbAtt_InAtt : 
    forall a l, existsbAtt a l = true <-> InAtt a l.
Proof. unfold existsbAtt. intros; split; 
functional induction (InAtt a l) using InAtt_ind.
- simpl. congruence. 
- intro H. simpl in H. apply orb_true_iff in H.
  destruct H. 
  ++ unfold eqbAtt in H. rewrite stringDecF.eqb_eq in H.
     eauto.
  ++ eauto.
- eauto. 
- intro H. simpl. apply orb_true_iff.
  destruct H.
  ++ unfold eqbAtt. simpl. rewrite stringDecF.eqb_eq.
     eauto.
  ++ eauto.
Qed.

Hint Resolve existsbAtt_InAtt.

Ltac existsbAtt_InAtt := rewrite existsbAtt_InAtt.
Ltac InAtt_existsbAtt := rewrite <- existsbAtt_InAtt.

(* relate InAtt with In from library *)
Lemma InAtt_In : forall (a:att) (A:vatts), InAtt a A  <-> exists x, In x A /\ (eqbAtt a) x = true.
Proof.  intros. InAtt_existsbAtt. eauto. Qed.

(*Lemma InAtt_In_a : forall (A:vatts), (exists a, In a A <-> InAtt (fstVatt a) A ).
Proof. intros. exists a. InAtt_existsbAtt. eauto. Qed.*)

Lemma In_InAtt_fstVatt : forall (a:vatt) (A:vatts), In a A  -> InAtt (fstVatt a) A.
Proof. intros. rewrite InAtt_In. 
       exists a. split. auto.
       unfold eqbAtt. rewrite stringBEF.eqb_refl. reflexivity.
Qed.

(* exists x, In x A /\ (eqbAtt a) x = true <-> exists e, In (ae a e) A *)

(*Lemma InAtt_In : forall (a:att) (A:vatts), InAtt a A  <-> exists e, In (ae a e) A.
Proof. intros. split. 
       - induction A as [|a' A' IHa']. 
         + intro H. unfold InAtt in H. simpl in H. discriminate H.
         + intro H. unfold InAtt in H. unfold InAtt in IHa'. destruct a' as (a', e'). 
           simpl. simpl in H. destruct (string_beq a a') eqn: Heq.
           rewrite stringDecF.eqb_eq in Heq.
           ++ exists e'. simpl. left. rewrite <- vattDecF.eqb_eq.
           simpl. rewrite fexpBEF.eqb_refl. rewrite andb_true_r.
           rewrite stringDecF.eqb_eq. auto.
           ++ apply IHa' in H. destruct H as [e'' H]. exists e''.
              right. auto.
      - induction A as [|a' A' IHa']; intro H; destruct H as [e H]; simpl in H;
        destruct H.
        + rewrite H. unfold InAtt. simpl. rewrite stringBEF.eqb_refl. reflexivity.
        + destruct a' as (a', e'). unfold InAtt. simpl. destruct (string_beq a a') eqn: Haeq. 
          auto. unfold InAtt in IHa'. apply IHa'. exists e. auto.
Qed.*)
 
Lemma InAtt_cons: forall a l, InAtt a l -> forall e, InAtt a ((ae a e)::l).
Proof. intros. simpl. auto. Qed.


(*-------------------------------------------------------------------------------*)

(* Configuration Variational Attribute List(Set) A[]c (see A3)*)
Fixpoint configVAttSet (vA : vatts) (c : config) : atts :=
  match vA with
  | nil                  => nil
  | cons (ae a e) vas => if semE e c 
                             then (cons a (configVAttSet vas c))
                             else (           configVAttSet vas c )
  end.

(** -----------------------atts vatts------------------------ **)


(** ------------------------------------------------------------
  Relations 
---------------------------------------------------------------*)
(*relName*)
Definition r : Type := string.

(* Plain Relation *)
Definition relS : Type := (r * atts) % type.

(* Variational Relation *)
Definition vrelS : Type := (r * (vatts * fexp) ) %type. (*assuming always annotated; could've used option*)

(* Configuration Variational Relation R[]c *)
(* helper function for fst fst *)
Definition configVRelS (vr : vrelS) (c : config) : relS := if semE (snd (snd vr)) c
                                                         then  (fst vr, (configVAttSet (fst (snd vr) ) c)) 
                                                           else  (fst vr, nil).
(** ---------------------------relS-------------------------- **)

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

(** -------------------------------------------------------
  Query 
-----------------------------------------------------------*)

Inductive setop : Type := union | inter.

(* Plain Query*)
Inductive query : Type :=
  | rel   : relS    -> query
  | sel   : cond    -> query -> query 
  | proj  : atts    -> query -> query 
  | join  : cond    -> query -> query -> query 
  | prod  : query   -> query -> query 
  | setU  : setop   -> query -> query -> query.

(* Variaitonal Query *)
Inductive vquery : Type :=
  | rel_v   : vrelS    -> vquery
  | sel_v   : vcond    -> vquery -> vquery 
  | proj_v  : vatts    -> vquery -> vquery 
  | chcQ    : fexp     -> vquery -> vquery -> vquery
  | join_v  : vcond    -> vquery -> vquery -> vquery 
  | prod_v  : vquery   -> vquery -> vquery 
  | setU_v  : setop    -> vquery -> vquery -> vquery.

(* Configuration Variational Query Q[]c *)
Fixpoint configVQuery (vq : vquery) (c : config) : query :=
  match vq with
  | rel_v  vr          => rel (configVRelS vr c)
  | sel_v  vc  vq      => sel (configVCond vc c) (configVQuery vq c)
  | proj_v vatts vq    => proj (configVAttSet vatts c) (configVQuery vq c)
  | chcQ e vq1 vq2     => if semE e c then configVQuery vq1 c else configVQuery vq2 c
  | join_v vc  vq1 vq2 => join (configVCond vc c) (configVQuery vq1 c) (configVQuery vq2 c)
  | prod_v vq1 vq2     => prod (configVQuery vq1 c) (configVQuery vq2 c) 
  | setU_v setop vq1 vq2 => setU setop (configVQuery vq1 c) (configVQuery vq2 c) 
  end.

(** -----------------------query vquery------------------------ **)


(** ------------------------------------------------------------
  Query Type 
---------------------------------------------------------------*)
(* Plain Query Type *)
Definition qtype  : Type := (atts) %type.

(* Variaitonal Query Type *)
Definition vqtype : Type := (vatts * fexp) %type. (*assuming always annotated; could've used option*)

(* Configuration Variational Query Type T[]c *)
Definition configVQtype (vqt : vqtype) (c : config) : qtype := 
      match vqt with 
      |(V, e) => if semE e c then  configVAttSet V c else  nil
      end.

Lemma configVQtype_nil: forall e c, (configVQtype ([], e) c) = [].
Proof. intros e c. simpl. destruct (E[[ e]] c); reflexivity. Qed.
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
    | cons x xs => match set_mem string_dec x A' with 
                   | false => false
                   | true  => sublist_bool xs (set_remove string_dec x A')
                   end
    end. 

(* Also check count
   sublist [1; 1; 2] [1; 2] doesn't hold
*)
Definition sublist (A A': list string):= forall x, (In x A -> In x A') /\ 
           (count_occ string_dec A x = count_occ string_dec A' x).


(* Subsumption of Plain Set (Query Type) *)
Definition subsump_qtype_bool (A A': qtype) := sublist_bool A A'.

(* Subsumption of Variational Set (Query Type) *)
Definition subsump_vqtype ( X X': vqtype ) : Prop := forall c, 
    sublist (configVQtype X c) (configVQtype X' c).

(*----------------------subsump--------------------------------*)




(** ------------------------------------------------------------
  Equivalence (of Variational Set) definition
---------------------------------------------------------------*)
(* Plain Set (Query Type) Equivalence*)
Fixpoint equiv_atts_bool (A A': qtype) : bool := 
    match A with
    | nil => match A' with 
             | nil => true
             | cons _ _ => false
             end
    | cons x xs => match set_mem string_dec x A' with 
                   | false => false
                   | true  => equiv_atts_bool xs (set_remove string_dec x A')
                   end
    end.

Definition equiv_atts : relation atts:= 
       fun A A' => forall a, (In a A <-> In a A') /\ 
                      ( count_occ string_dec A a = count_occ string_dec A' a).

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
         try (transitivity (count_occ string_dec A'' a));
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

(** atts equivalence is an equivalence relation. *)
(*Instance equiv_attsE : Equivalence equiv_atts.
Proof.
  split.
    apply equiv_atts_refl.
    apply equiv_atts_sym.
    apply equiv_atts_trans.
Qed.

(** atts equivalence is an equivalence relation. *)
Instance equiv_qtypeE : Equivalence equiv_qtype.
Proof.
  split.
    apply equiv_atts_refl.
    apply equiv_atts_sym.
    apply equiv_atts_trans.
Qed.*)

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


(*---------------------------equiv-----------------------------*)

(** ------------------------------------------------------------
  Restrict vatts to have no duplicate atts 
                       i.e. same atts with diff fexp
---------------------------------------------------------------*)

(*stronger condition than mere NoDup vatts*)

Inductive NoDupAtt : list vatt -> Prop :=
  | NoDupAtt_nil : NoDupAtt nil
  | NoDupAtt_cons : forall a e l, ~ InAtt a l -> NoDupAtt l 
                            -> NoDupAtt ((ae a e)::l).

(* relate NoDupAtt with NoDup from library *)


Lemma NoDupAtt_NoDup: forall A, NoDupAtt A -> NoDup A.
Proof. intros A H. induction H as [| a e l H1 H2 IHa]. 
       + apply NoDup_nil.
       + apply NoDup_cons.
         ++ rewrite (InAtt_In) in H1. 
            apply dist_not_exists with (x:= (ae a e)) in H1.
            apply Classical_Prop.not_and_or in H1.
            destruct H1. auto.
            unfold eqbAtt in H. simpl in H.
            rewrite stringBEF.eqb_refl in H.
            eauto.
         ++ auto.
Qed.

Definition hasAtt (a : att) (v:vatt)  : bool := let  'ae x e := v  in (string_beq a x). 

Definition extract_e (a : att) (A: vatts) : fexp :=  
                   fold_right Feature.join (litB false) (map (sndVatt) (filter (hasAtt a) A)). 

Fixpoint removeAtt (a : att) (A: vatts) : vatts := 
    match A with 
   | nil => nil
   | ae a' e' :: A' => match (string_beq a a') with
                     | true => removeAtt a A'
                     | false => ae a' e' :: removeAtt a A'
                     end
   end.



(* InAtt removeAtt Corollary *)

Theorem removeAtt_InAtt : forall l x, ~ InAtt x (removeAtt x l).
Proof. Admitted.

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

Lemma notInAtt_removeAtt: forall l x, ~ InAtt x l -> removeAtt x l = l.
Admitted.

Lemma InAtt_removeAtt: forall l x y, InAtt x (removeAtt y l) -> InAtt x l /\ x <> y.
Admitted.

Lemma removeAtt_removeAtt_comm : forall l x y,
    removeAtt x (removeAtt y l) = removeAtt y (removeAtt x l).
Admitted.

Lemma removeAtt_removeAtt_eq : forall l x, removeAtt x (removeAtt x l) = removeAtt x l.
Admitted.



(* function to merge duplicate atts in vatts *)

Lemma remove_reduce (a:att) (l:vatts) : List.length (removeAtt a l) < S(List.length l).
Proof. intros. induction l.
       - unfold removeAtt.  unfold List.length. 
         apply PeanoNat.Nat.lt_0_succ. 
       - simpl. destruct a0. destruct (string_beq a a0). auto. 
         simpl. apply Lt.lt_n_S. auto. 
Qed.

Hint Resolve remove_reduce.

Lemma cons_injective: forall (A : Type)(a a' : A)(l l' : list A),
   (a = a') /\ (l = l') -> (a :: l) = (a' :: l').
Proof. intros. destruct H. rewrite H, H0. reflexivity. Qed.



Function nodupatt (v : list vatt) {measure List.length v} : list vatt :=
   match v with 
   | nil          => nil
   | ae a e :: vs =>  match existsbAtt a vs with
                      | false => ae a e :: nodupatt vs
                      | true  => let e' := extract_e a vs in
                         (ae a (e /\(F) e') ) :: nodupatt (removeAtt a vs)
                      end
   end.
all:intros; simpl; eauto.
Defined.

Ltac simpl_nondupatt := rewrite nodupatt_equation.

Hint Resolve nodupatt_equation.

Check nodupatt_rec.

(* Functional Scheme nondupatt_ind := Induction for nodupatt Sort Prop.
 with removeAtt_ind := Induction for removeAtt Sort Prop.*)



Lemma nodupatt_nil : nodupatt [] = [].
Proof. eauto. Qed.

Lemma nodupatt_not_in_cons : forall a e l,
      ~ InAtt a l -> nodupatt (ae a e::l) = ae a e :: nodupatt l.
Proof. intros. simpl_nondupatt. 
simpl. destruct (existsbAtt a l) eqn:Hf.
rewrite <- existsbAtt_InAtt in H. contradiction.
auto. Qed.


Lemma nodupatt_in_cons : forall a e l,
        InAtt a l -> 
          nodupatt (ae a e::l) = ae a (e /\(F) extract_e a l) 
                     :: nodupatt (removeAtt a l).
Proof. intros. simpl_nondupatt. simpl.
rewrite <- existsbAtt_InAtt in H. rewrite H. auto.
Qed.


Lemma InAtt_nodupatt_removeAtt: forall x y l, x <> y ->
InAtt x (nodupatt l) <-> InAtt x (nodupatt (removeAtt y l)).
Proof. 
intros x y l Hxy. split.
- induction l as  [|v ls IHl]; intro H. 
  + rewrite nodupatt_equation in H. eauto. 
  + destruct v.  
    simpl. 
    destruct (string_beq y a) eqn: Hya.
    ++ rewrite stringDecF.eqb_eq in Hya.
       rewrite nodupatt_equation in H.
       destruct (existsbAtt a ls) eqn:Hex.
       +++ simpl in H. destruct H.
           ++++ rewrite <- Hya in H. symmetry in H. contradiction.
           ++++ rewrite <- Hya in H. auto.
       +++ simpl in H. destruct H.
           ++++ rewrite <- Hya in H. symmetry in H. contradiction.
           ++++ apply IHl. auto.
    ++ rewrite stringBEF.eqb_neq in Hya.
       rewrite nodupatt_equation in H.
       destruct (existsbAtt a ls) eqn:Hex.
       +++ simpl in H. destruct H.
           ++++ rewrite nodupatt_equation. 
                
                rewrite existsbAtt_InAtt in Hex. 
                rewrite (InAtt_InAtt_removeAtt) with (y:=y) in Hex.
                rewrite <- existsbAtt_InAtt in Hex. rewrite Hex.
                simpl. left. auto. auto.
           ++++ rewrite nodupatt_equation. 
                rewrite existsbAtt_InAtt in Hex. 
                rewrite (InAtt_InAtt_removeAtt) with (y:=y) in Hex.
                rewrite <- existsbAtt_InAtt in Hex. rewrite Hex.
                simpl.  
Admitted.

Lemma In_inv : forall (A:Type) (a b:A) (l:list A), In b (a :: l) -> a = b \/ (a <> b /\ In b l).
Admitted.

Lemma InAtt_inv : forall a b l, InAtt b (a :: l) -> (fstVatt a) = b \/ 
       ((fstVatt a) <> b /\ InAtt b l).
Admitted.


Lemma nodupatt_removeAtt: forall a l, nodupatt (removeAtt a l) = removeAtt a (nodupatt l).
Proof. intros. generalize dependent a. induction l. 
- simpl_nondupatt. simpl. auto. 
- intro a0.
  destruct a. simpl. destruct (string_beq a0 a) eqn: Haa0.
  + rewrite stringDecF.eqb_eq in Haa0. rewrite Haa0.
    destruct (existsbAtt a l) eqn: Hal.
    ++ rewrite nodupatt_in_cons.
       simpl. rewrite stringBEF.eqb_refl.
       rewrite IHl. rewrite removeAtt_removeAtt_eq.
       reflexivity.
       rewrite <- existsbAtt_InAtt. auto.
    ++ rewrite nodupatt_not_in_cons. 
       simpl. rewrite stringBEF.eqb_refl. auto.
       rewrite <- existsbAtt_InAtt. rewrite Hal.
       eauto.
  + 
    symmetry. rewrite nodupatt_equation. 
    destruct (existsbAtt a l) eqn:Ha0l.
    ++ simpl. rewrite Haa0. symmetry.
       rewrite nodupatt_equation. 
       rewrite existsbAtt_InAtt in Ha0l. 
       rewrite (InAtt_InAtt_removeAtt) with (y:=a0) in Ha0l.
       rewrite <- existsbAtt_InAtt in Ha0l. rewrite Ha0l.
       rewrite IHl.
Admitted.





Lemma InAtt_nondupatt: forall x l, InAtt x (nodupatt l) <-> InAtt x l.
Proof. 
intros. split.
- functional induction (nodupatt l) using nodupatt_ind.
+ eauto.
+ intro H. simpl. simpl in H.
destruct H. ++ eauto.
            ++ eauto.
+ intro H. simpl. simpl in H.
destruct H. 
 ++ eauto.
 ++ right. destruct (string_beq x a) eqn: Hxa.
     +++ rewrite stringDecF.eqb_eq in Hxa.
     rewrite  existsbAtt_InAtt in e1.
     rewrite Hxa. auto.
     +++ rewrite stringBEF.eqb_neq in Hxa. 
     apply IHl0 in H. 
     rewrite <- (InAtt_InAtt_removeAtt) in H.
     auto. auto.
- functional induction (nodupatt l) using nodupatt_ind.
+ eauto.
+ intro H. simpl. simpl in H.
destruct H. ++ eauto.
            ++ eauto.
+ intro H. simpl. simpl in H.
destruct H. 
 ++ eauto.
 ++ right. 
     rewrite  existsbAtt_InAtt in e1. Check removeAtt_rec.
     pose (removeAtt_InAtt) as Hc.
     specialize Hc with vs a.
     
     destruct (string_beq x a) eqn: Hxa.
     +++ rewrite stringDecF.eqb_eq in Hxa.
     rewrite Hxa in IHl0.
     Search (~(_->_)).
      
     rewrite  existsbAtt_InAtt in e1.
     rewrite Hxa. auto.
     +++ rewrite stringBEF.eqb_neq in Hxa. 
     apply IHl0 in H. 
     rewrite <- (InAtt_InAtt_removeAtt) in H.
     auto. auto.

(* 
rewrite stringDecF.eqb_eq in Hxa. 
     apply IHl0 in H. rewrite Hxa in H.
     pose (removeAtt_InAtt) as Hc.
     specialize Hc with vs a. contradiction.

induction l; intro H. 
- simpl in H. destruct H.
- destruct a. simpl. 
  rewrite nodupatt_equation in H.   
  destruct (existsbAtt a l) eqn: Hal.
  ++ apply InAtt_inv in H. simpl in H. destruct H.
     +++ eauto.
     +++ destruct H. admit.
Admitted.*)


Lemma In_InAtt_nodupatt : forall a l,
           In a l -> InAtt (fstVatt a) (nodupatt l).
Proof. intros. 
- intros. 
  rewrite InAtt_nondupatt. rewrite InAtt_In.
  exists a. split. auto.
  destruct a eqn:Ha. simpl. 
  unfold eqbAtt. simpl.
  rewrite stringBEF.eqb_refl. auto.
Qed.

(* don't prove this now, straightforward but don't need it*)
Lemma In_eqbAtt_InAtt_nodupatt : forall a l,
           InAtt a (nodupatt l) <-> exists x, In x l /\ eqbAtt a x = true.
Proof.
(*intros. split.
- intros. 
  rewrite InAtt_nondupatt. rewrite InAtt_In.
  exists a. split. auto.
  destruct a eqn:Ha. simpl. 
  unfold eqbAtt. simpl.
  rewrite stringBEF.eqb_refl. auto.
- intro. rewrite InAtt_nondupatt in H. 
  rewrite InAtt_In in H. destruct H as [a' H].
  destruct H. unfold eqbAtt in H0. simpl in H0.
  rewrite stringDecF.eqb_eq in H0. 
  apply In_InAtt_fstVatt in H.
  rewrite <- H0 in H. *)

Admitted.

(*intros. split. 
+ intros. generalize dependent a.
induction l as [| a' l' IHl']. 
++ intros. simpl in H. destruct H.
++ intros. 
   simpl in H. 
   destruct H. 
   +++ rewrite H.
       simpl. simpl_nondupatt.
       destruct a. simpl.
       destruct (existsbAtt a l');
       unfold InAtt; simpl;
       rewrite stringBEF.eqb_refl;
       reflexivity.
   +++ simpl_nondupatt. simpl. 
       destruct (existsbAtt (fstVatt a') l') eqn: Hf.
       unfold InAtt. simpl.
       destruct (string_beq (fstVatt a) (fstVatt a')) eqn: Haa'.
       reflexivity. 
       fold (InAtt (fstVatt a) (nodupatt (removeAtt (fstVatt a') l'))).
       rewrite <- InAtt_InAtt_removeAtt_nodupatt.
       auto. rewrite <- stringBEF.eqb_neq. auto. 
       unfold InAtt. destruct a'.
       destruct (string_beq (fstVatt a) a0) eqn: Hax.
       simpl. rewrite Hax. reflexivity. simpl. rewrite Hax. 
       rewrite IHl'. auto. auto.
+ intros. generalize dependent a.
induction l as [| a' l' IHl']; intros. 
       - rewrite nodupatt_nil in H. unfold InAtt in H. simpl in H.
         discriminate H.
       - simpl.
         unfold InAtt in H. 
         destruct (string_beq x a) eqn: Hxa.
         reflexivity. rewrite nodupatt_eq, removeAtt_hd in H.
         simpl in H. destruct (existsbAtt a l) eqn:Hal. 
         unfold InAtt in H. simpl in H. rewrite Hxa in H.     
         





specialize IHl' with a'. 
rewrite H in IHl'. simpl in IHl'.
apply InAtt_In in IHl'.
rewrite <- InAtt_In in IHl'.
apply (InAtt_cons _ (sndVatt a)) in IHl'.



rewrite nodupatt_eq. simpl.
destruct (existsbAtt (fstVatt a) l) eqn:Hf.
unfold InAtt in H. contradiction.
auto. Qed. *)

(* apply well_founded_induction.*)

Lemma NoDupAtt_nodupatt (v:vatts) : NoDupAtt (nodupatt v).
Proof. induction v; rewrite nodupatt_equation. 
+ simpl. apply NoDupAtt_nil.
+ simpl. destruct a. simpl. 
destruct (existsbAtt a v) eqn:Hf.
apply NoDupAtt_cons. Admitted.



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

(*------------------------push_annot---------------------------*)

(** ------------------------------------------------------------
  Set Operation for Attribute List(Set) & Query type(annotated attr list)
  Union Intersection
---------------------------------------------------------------*)
(* Plain Attr List *)
Definition atts_union (A A': atts) : atts := 
   set_union string_dec A A'.

(* Variational Attr List *)
Definition vatts_union (A A': vatts) : vatts := 
    set_union vatt_eq_dec A A'.

(* Variational Query Type*)
Definition vqtype_union (Q Q': vqtype) : vatts := 
     vatts_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')). 

(*------------------------------------------------------------------------------*)
(* Plain Attr List *)
Definition atts_inter (A A': atts) : atts := 
   set_inter string_dec A A'.

(* Variational Attr List *)
Definition vatts_inter (A A': vatts) : vatts := 
    set_inter vatt_eq_dec A A'.

(* Variational Query Type*)
(* Variational Query Type*)
Definition vqtype_inter (Q Q': vqtype) : vatts := 
     vatts_inter (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')).

(* Check whether sets are disjoint - A intersect A' = {}*)
Definition is_disjoint_bool (A A': atts) : bool :=
  match atts_inter A A' with
  | [] => true
  | _  => false
  end.

(** lemmas to expand second recursive function used for ackermann *)
(* better name *)

(*-------------------------------------------------------------------------------*)

(** lemmas for set OP with identity and union commutivity *)
(*Lemma union_l_nil_r: forall X f (A: list X), union_l f A [] = A.
Proof. intros X f A. induction A as [|a A IHA]. auto. 
simpl. rewrite IHA. reflexivity. Qed. *)

(*Lemma atts_union_c_nil_r: forall A, atts_union_c A [] = [].
Proof. intro A. induction A; auto. Qed.

Lemma atts_union_l_nil_r: forall (A: atts), atts_union_l A [] = A.
Proof. intro A. induction A as [|a A IHA]. auto. 
simpl. rewrite IHA. reflexivity. Qed. 

Lemma atts_union_nil_r: forall A, atts_union A [] = A.
Proof. intros. unfold atts_union. 
rewrite atts_union_c_nil_r. rewrite atts_union_l_nil_r. simpl. 
rewrite app_nil_r. reflexivity. Qed.

Lemma atts_union_nil_l: forall A, atts_union [] A = A.
Proof. intros. unfold atts_union. simpl. 
rewrite atts_union_l_nil_r. reflexivity. Qed.*)

(*Lemma eq_equiv_atts: forall A A', A = A' -> A =a= A'.
Proof. intros. rewrite H. reflexivity. Qed.*)
(* count_occ_cons_eq, count_occ_cons_neq *)
Lemma count_occ_set_add_eq: forall l x y,
    x = y -> ~(In x l) -> (count_occ string_dec (set_add string_dec x l) y 
                           = S (count_occ string_dec l y)).
Proof. intros. rewrite H. induction l as [ |a l IHal]. 
       - simpl. destruct (string_dec y y). 
         reflexivity. destruct n. reflexivity. 
       - simpl. 
         rewrite not_in_cons in H0. destruct H0.
         destruct (string_dec a y); subst.
         + destruct H0. reflexivity. 
         + destruct (string_dec y a); subst. 
           ++ destruct n. reflexivity.
           ++ simpl. destruct (string_dec a y); subst. 
              +++ destruct n. reflexivity.
              +++ apply IHal. auto.
Qed.

Lemma count_occ_set_add_neq : forall l x y,
    x <> y -> count_occ string_dec (set_add string_dec x l) y = count_occ string_dec l y.
Proof. 
   intros l x y Hxy. induction l as [ |a l IHal]. 
   - simpl. destruct (string_dec x y); subst.  
      + destruct Hxy. reflexivity.
      + reflexivity.
   - simpl. destruct (string_dec x a). 
      + destruct (string_dec a y); subst. destruct Hxy. reflexivity.
           simpl. destruct (string_dec a y); subst. destruct n. 
           destruct Hxy. reflexivity. reflexivity.
      + destruct (string_dec a y); subst. simpl. 
        ++ destruct (string_dec y y); subst.
            +++ auto.
            +++ destruct n0. reflexivity. 
        ++ simpl. destruct (string_dec a y); subst. 
            destruct n0. reflexivity. auto. 
Qed.


Lemma count_occ_set_add_cons l x y:
         ~(In x l) -> (count_occ string_dec (set_add string_dec x l) y =
                count_occ string_dec (x::l) y).
Proof. intros H0. destruct (string_dec x y) as [H | H]. 
       + apply (count_occ_set_add_eq l x y) in H as H1. rewrite H1.
         symmetry. apply count_occ_cons_eq. auto. auto.
       + apply (count_occ_set_add_neq l x y) in H as H1. rewrite H1.
         symmetry. apply count_occ_cons_neq. auto. 
Qed.

Lemma equiv_atts_set_add_cons a A:
         ~ In a A -> (set_add string_dec a A) =a= (a::A) .
Proof. unfold equiv_atts. intros Ha a0. split.
       - split.
         + intro H. simpl. rewrite set_add_iff in H. 
           destruct H. ++ left. auto.
                       ++ right. auto.
         + intro H. rewrite set_add_iff. simpl in H. 
           destruct H. ++ left. auto.
                       ++ right. auto.
      - apply (count_occ_set_add_cons A a a0).
        auto.
Qed.

Lemma atts_union_nil_r: forall A, atts_union A [] =a= A.
Proof. intros. simpl. reflexivity. Qed.

(* atts_union use set_add; thus bag A will become set A on LHS*)
Lemma atts_union_nil_l: forall A (H: NoDup A), atts_union [] A =a= A.
Proof. intros. induction A. apply atts_union_nil_r.
       simpl. unfold equiv_atts in IHA. rewrite NoDup_cons_iff in H.
       destruct H as [H1 H2].
       split; intros; destruct (IHA H2 a0) as [IHA1 IHA2].
       ++ split; intro H. 
          - apply set_add_elim  in H. 
            destruct H. 
            -- left. auto. 
            -- right. 
               rewrite <- IHA1. apply H. 
          - simpl in H.  destruct H. 
            -- apply set_add_intro2. auto.
            -- apply set_add_intro1. 
               rewrite IHA1. assumption.
       ++ destruct (string_dec a a0) as [H | H].
          +++ apply (count_occ_set_add_eq (atts_union [] A) a a0) in H as H'.
              rewrite H'. rewrite IHA2. symmetry. apply count_occ_cons_eq.
              auto. rewrite H in H1. rewrite <- IHA1 in H1. rewrite H. apply H1.
          +++ apply (count_occ_set_add_neq (atts_union [] A) a a0) in H as H'.
              rewrite H'. rewrite IHA2. symmetry. apply count_occ_cons_neq.
              auto.
Qed.

Lemma atts_inter_nil_r: forall A, atts_inter A [] =a= [].
Proof. intro A. induction A. simpl. reflexivity. simpl.
       assumption.
Qed.

Lemma atts_inter_nil_l: forall A, atts_inter [] A =a= [].
Proof. intros. simpl. reflexivity. Qed.

(*Lemma vatts_union_c_nil_r: forall A, vatts_union_c A [] = [].
Proof. intro A. induction A as [|a A IHA]; 
try (destruct a as (a,e)); try(auto). Qed.

Lemma vatts_union_l_nil_r: forall (A: vatts), vatts_union_l A [] = A.
Proof. intro A. induction A as [|a A IHA]. auto. 
destruct a as (a,e). simpl. rewrite IHA. reflexivity. Qed.

Lemma vatts_union_nil_r : forall A, vatts_union A [] = A.
Proof. intros. unfold vatts_union. 
rewrite vatts_union_c_nil_r. rewrite vatts_union_l_nil_r. simpl. 
rewrite app_nil_r. reflexivity. Qed.

Lemma vatts_union_nil_l : forall A, vatts_union [] A = A.
Proof. intros. unfold vatts_union. simpl. 
rewrite vatts_union_l_nil_r. reflexivity. Qed.*)

Lemma eq_equiv_vatts: forall A A', A = A' -> A =va= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma vatts_union_nil_r : forall A, vatts_union A [] =va= A.
Proof. intro A. induction A as [|a A IHA]. simpl. reflexivity.
destruct a as (a,e). simpl. reflexivity. Qed.

Lemma configVAttSet_set_add: forall a e A c, 
        configVAttSet (set_add vatt_eq_dec (ae a e) A) c =a=
           if (E[[ e]] c) then set_add string_dec a (configVAttSet A c)
                                   else                  (configVAttSet A c).
Proof. Admitted.

Lemma equiv_atts_set_add: forall a A A', A =a= A' -> 
       set_add string_dec a A =a=  set_add string_dec a A'.
Proof. Admitted.

Lemma vatts_union_nil_l : forall A (H: NoDup A), vatts_union [] A =va= A.
Proof. induction A. 
      simpl. reflexivity. simpl.  
      unfold equiv_vatts in IHA. intro H.
      rewrite NoDup_cons_iff in H.
      destruct H as [H1 H2].
      unfold equiv_vatts. 
      intros. destruct a as (a, e). unfold configVAttSet; fold configVAttSet.
      rewrite configVAttSet_set_add. destruct (E[[ e]] c) eqn: He. 
      + rewrite (equiv_atts_set_add _ _ _ (IHA H2 c)). 
        apply equiv_atts_set_add_cons.
      + apply (IHA c).
Qed. 

Lemma not_in_configVAttSet: forall a A, (forall e, ~ In (ae a e) A) ->
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
         destruct H. Admitted.

Lemma not_equal: forall a a' e', a' <> a ->ae a' e' <> ae a e'.
Proof. intros. rewrite <- vattBEF.eqb_neq. simpl.  Admitted.

Lemma vatts_inter_nil_r : forall A, vatts_inter A [] =va= [].
Proof. intro A. induction A as [|(a, e)]. reflexivity. simpl. 
       assumption. Qed.

Lemma vatts_inter_nil_l : forall A, vatts_inter [] A =va= [].
Proof. intros. simpl. reflexivity. Qed. 


(* atts_union_comm is not commutative anymore*)

(*Lemma atts_union_comm: forall A A', 
   atts_union A A' = atts_union A' A.
Proof. intros A A'. destruct A.
       + rewrite atts_union_nil_r. 
         rewrite atts_union_nil_l.
         reflexivity.
       + unfold atts_union. 
Qed.*)

(*--------------------Set Operation End ---------------------------*)


(* ---------------------------------------------------------------
  | Type of variational query
   ---------------------------------------------------------------
*)

Inductive vtype :fexp -> vquery -> vqtype -> Prop :=
  (*  -- intro LESS specific context --
    empty |- rn : A^e'  ~sat(e' /\ (~m))
    ------------------------------------ intro less specific context
               m  |- rn : A^e'
   *)
  | Relation_vE_fm : forall e rn A {HA: NoDup A} e',
        ~ sat (  e'    /\(F)   (~(F) (e)) ) ->
       vtype e (rel_v (rn, (A, e'))) (A, e') (** variational context is initialized with feature_model which is more general than the overall pc of any relation in vdbms *)
  (*   -- intro MORE specific context --
    empty |- rn : A^e'  ~sat(e /\ (~e'))
    ------------------------------------  RELATION-E 
               e  |- rn : A^e
   *)
  | Relation_vE : forall e rn A {HA: NoDup A} e',
       ~ sat (  e    /\(F)   (~(F) (e')) ) ->
       vtype e (rel_v (rn, (A, e'))) (A, e)
  (*   -- PROJECT-E --  *)
  | Project_vE: forall e vq e' A' {HA': NoDup A'} A {HA: NoDup A},
       vtype e vq (A', e') -> 
       subsump_vqtype (A, e) (A', e') ->
       vtype e (proj_v A vq) (A, e)
  (*  -- CHOICE-E --  *)
  | Choice_vE: forall e e' vq1 vq2 A1 {HA1: NoDup A1} e1 A2 {HA2: NoDup A2} e2,
       vtype (e /\(F) e') vq1 (A1, e1) ->
       vtype (e /\(F) (~(F) e')) vq2 (A2, e2) ->
       vtype e (chcQ e' vq1 vq2)
        (vqtype_union (A1, e1) (A2, e2) , e1 \/(F) e2)
            (*e1 and e2 can't be simultaneously true.*)
  (*  -- PRODUCT-E --  *)
  | Product_vE: forall e vq1 vq2 A1 {HA1: NoDup A1} e1 A2 {HA2: NoDup A2} e2 ,
       vtype e  vq1 (A1, e1) ->
       vtype e  vq2 (A2, e2) ->
       vqtype_inter (A1, e1) (A2, e2) = nil ->
       vtype e  (prod_v vq1 vq2)
        (vqtype_union (A1, e1) (A2, e2) , e1 \/(F) e2)
  (*  -- SETOP-E --  *)
  | SetOp_vE: forall e vq1 vq2 A1 {HA1: NoDup A1} e1 A2 {HA2: NoDup A2} e2 op,
       vtype e vq1 (A1, e1) ->
       vtype e vq2 (A2, e2) ->
       equiv_vqtype (A1, e1) (A2, e2) ->
       vtype e (setU_v op vq1 vq2) (A1, e1).
(* (*  -- SELECT-E --  *)
   | Select_vE: forall e S vq A e',
       vtype e S vq (A, e') ->
       vtype e S (sel_v c vq) (A, e'). *) 
 
(*-----------------------vqtype--------------------------------*)

(* ------------------------------------------------------------
  | Type of plain query
   ------------------------------------------------------------
*)
Fixpoint type' (q:query) : qtype :=
 match q with
 | (rel (rn, A)) => A
 | (proj A q)    => let A' := type' q in 
                      if subsump_qtype_bool A A' then A else nil 
 | (setU op q1 q2) => if equiv_qtype_bool (type' q1) (type' q2) then type' q1 else nil
 | (prod  q1 q2) => if (is_disjoint_bool (type' q1) (type' q2)) then 
                          atts_union (type' q1) (type' q2) else nil
 | _ => nil
 end.
 
(*------------------------------type'-------------------------*)

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

(*Lemma configVAttSet_dist_vatts_union_v1 : forall A c, (forall A' , configVAttSet (vatts_union A A') c =
      atts_union (configVAttSet A c)
        (configVAttSet A' c) )  -> forall a1 e1 A', configVAttSet
        (vatts_union ((a1, e1) :: A) ( A')) c =
           atts_union (configVAttSet ((a1, e1) :: A) c)
             (configVAttSet ( A') c) .

Proof. (* intros. 
  assert (I: forall a e A, configVAttSet ( (a, e) :: A ) c = 
      if semE e c then a :: (configVAttSet A c) else configVAttSet A c ).
  { intros. simpl. reflexivity. }
  rewrite I.  destruct (E[[ e1]] c) eqn: E1.
  + destruct A' as [|(a2, e2)].
    ++ simpl. rewrite E1. reflexivity.
    ++ rewrite I. destruct (E[[ e2]] c) eqn: E2.  
       +++ simpl. destruct (string_comp a1 a2) eqn: SC. 
          { rewrite I. simpl. rewrite E1. simpl. rewrite H. reflexivity. }
          { destruct n. 
           - rewrite I. rewrite E1. rewrite H. rewrite I. rewrite E2. reflexivity.
           - admit.
          }
       +++ simpl. destruct (string_comp a1 a2) eqn: SC. 
          { rewrite I. simpl. rewrite E1. simpl. rewrite H. reflexivity. }
          { destruct n. 
           - rewrite I. rewrite E1. rewrite H. rewrite I. rewrite E2. reflexivity.
           - admit.
          }*)
Admitted.*)

(*
   destruct v as (a, e).
       - simpl in H0. 
         destruct v' as (a',e') eqn:V'. 
         destruct xs' as [|(x',ex') ] eqn: XS'.
         + admit.
         + remember ((a', e') :: (x', ex') :: v ) as V. 
           assert (I: (LocallySortedVAtts V) /\ (NoDup V)). { admit. }
           rewrite HeqV in I.  inversion I; subst. inversion H2; subst.  
           simpl in H6.
           simpl in H1. destruct H1. simpl in H0. simpl in H8.
           rewrite hack_control_simpl. rewrite H1.
           rewrite hack_control_simpl. rewrite H4. unfold fst.
           rewrite hack_control_simpl. 
           destruct (E[[ ex']] c) eqn: EX'.
           ++ apply (string_comp_trans a a' x') in H8. 
               simpl. rewrite H8. reflexivity. assumption.
           ++ rewrite hack_control_simpl.
              rewrite H0. rewrite hack_control_simpl.
              rewrite H1. reflexivity.
         + destruct H. 
  ++ simpl. rewrite H. 
*)

(*Fixpoint vatts_union (A A': vatts) : vatts := 
  match A, A' with
  | nil, _ => A'
  | _, nil => A
  | cons (a, e) xs, cons (a', e') xs' =>
          match (string_comp a a') with
          | 0 => cons (a, e \/(F) e') (vatts_union xs xs')
          | S 0 => cons (a', e') (vatts_union (cons (a, e) xs) xs')
          | S (S 0) => cons (a, e) (vatts_union xs (cons (a', e') xs'))
          | _ => nil
          end
  end.*)

(* Theorem mutual_excl: forall e e' vq1 vq2 A1 e1 A2 e2,
     vtype (e /\(F) e') vq1 (A1, e1) ->
       vtype (e /\(F) (~(F) e')) vq2 (A2, e2) ->
           ~ sat (  e1   /\(F)   e2 ) /\ taut (e1 \/(F) e2).
   Proof. Admitted.
*)
(*- unfold configVQuery. unfold configVRelS. 
    unfold configVQtype. simpl. destruct (E[[e]] c); 
    reflexivity.*)

(*- unfold configVQuery. unfold configVRelS. simpl. unfold configVQtype. simpl.
    rewrite not_sat_not_prop in H. rewrite <- sat_taut_comp in H.  
    destruct (E[[e']] c) eqn: HsemE'.
    + unfold configVQtype. 
      rewrite Heqe. simpl. reflexivity.
    + unfold sat in H. simpl in H. unfold not in H. apply ex_falso_quodlibet. 
      apply H. exists c. rewrite HsemE'. rewrite Heqe. simpl. reflexivity.*)

(*simpl. simpl in IHvtype1. simpl in IHvtype2. 
   apply (mutual_excl e e' vq1 vq2 A1 e1 A2 e2) in H.
   destruct (E[[ e']] c) eqn: E'. 
      ++  simpl in IHvtype1. simpl in IHvtype2. rewrite H0 in IHvtype1, IHvtype2.
          rewrite configVQType_dist_vatts_union.
          rewrite configVQType_push_annot. rewrite configVQType_push_annot.
          destruct H. assert (I1: forall e, (e /\(F) (litB true)) =e= e  ). { admit. }
          assert (I2: forall e1 e2 A c, e1 =e= e2 -> 
          configVQtype (A, e1) c = configVQtype (A, e2) c). { admit. }
          specialize I1 with e2 as I12.
          apply (I2 _ _ A2 c) in I12.
          specialize I1 with e1 as I11.
          apply (I2 _ _ A1 c) in I11. rewrite I11. rewrite I12. 
          inversion H1; subst.
          +++ rewrite not_sat_not_prop in H6. rewrite <- sat_taut_comp_inv in H6.
              specialize H6 with c. 
              simpl in H6. rewrite H0, E' in H6. simpl in H6. 
              assert (Ihack: false = false). { reflexivity. } 
              apply H6 in Ihack. unfold configVQtype at 2. simpl. rewrite Ihack.
              rewrite atts_union_nil_r. apply IHvtype1. reflexivity.
          +++ unfold configVQtype at 2. simpl. rewrite H0, E'. simpl. 
              rewrite atts_union_nil_r. apply IHvtype1. reflexivity.  
          +++ unfold configVQtype at 2. simpl. rewrite H0, E'. simpl. 
              rewrite atts_union_nil_r. apply IHvtype1. reflexivity. 
          +++ *)  
              
(*07-22-2020*)
(*| (setU op q1 q2) => let A1 := type q1 in
                          let A2 := type q2 in
                              if equiv_atts A1 A2 && *)

(*
   (vatts_union (push_annot A1 (litB true)) (push_annot A2 (litB true)), (e1 /\(F) e2) ).
*)

(** (E[[ e']] c) = true -> (E[[ e]] c) = true.*)

(*if semE (snd vqt) c
then  configVAttSet (fst vqt) c
else  nil. *)

(*-------------------------------------------------------------------------------*)
(** Remove replace with List.remove *)

(* it's bag remove but once *)

(*Fixpoint remove {X:Type} (f:X->X->bool) (a : X) (A : list X) : list X :=
    match A with
      | [] => []
      | x::xs => 
         match (f a x) with
        | true  => xs (*(remove f a xs)*)
        | false => x :: (remove f a xs)
        end
    end. 


Lemma in_remove_atts: forall l x y, In x (remove String.eqb y l) 
                                -> x <> y -> In x l.
Proof. intro l. induction l. intros. simpl in H. simpl. assumption.
simpl. intros. destruct ((y =? a)%string). right. assumption. simpl in H.
destruct H. left. assumption. apply IHl in H. right. assumption. assumption.
Qed.

(*Definition  listElEq {X:Type} (A B: list X):= forall (x: X), In x A <-> In x B.

Lemma ListElEq_refl_atts: forall (A:list att), listElEq A A.
Proof. intro A. split; destruct A; repeat(auto). Qed. *)


Fixpoint listElEq {X:Type} (f:X->X->bool) (A1 : list X) (A2 : list X) : bool :=
    match A1 with
      | [] => match A2 with
              | []  => true
              | _   => false
              end
      | x::xs => match (existsb (f x) A2) with
                  | true  => listElEq f xs (remove f x A2)
                  | false => false
                  end
    end. 

Lemma ListElEq_refl_atts: forall (A:list att), listElEq String.eqb A A = true.
Proof. intro A. induction A. - auto. - simpl. rewrite String.eqb_refl.
simpl. apply IHA. Qed.

Lemma ListElEq_refl_vatts: forall (A:list vatt), listElEq veqb A A = true.
Proof. intro A. induction A. 
       - auto. 
       - simpl. rewrite veqb_refl. simpl. apply IHA.
Qed.

Lemma ListElEq_In: forall (A B: atts), listElEq String.eqb A B = true <->
forall (x: att), In x A -> In x B.
Proof. intros. split. 
       - (*->*)
         generalize dependent B. induction A; intros. 
         + simpl in H. destruct B. intros. assumption.
           discriminate H.
         + simpl in H0. destruct H0.
           ++ rewrite <- H0. simpl in H. destruct (existsb (String.eqb a) B) eqn:HaB.
              +++ apply (existsb_exists (String.eqb a)) in HaB. 
                  destruct HaB as [x' HaBx]. destruct HaBx as [HaBx1 HaBx2].  
                  rewrite String.eqb_eq in HaBx2. rewrite <- HaBx2 in HaBx1. assumption.
              +++ discriminate H.
           ++ simpl in H. destruct (existsb (String.eqb a) B) eqn:HaB. 

Admitted.*)
     (*      rewrite <- H0. assumption.
         + destruct (existsb (String.eqb a) B) eqn:HaB. rewrite HaB in H.
           ++ apply (existsb_exists (String.eqb a)) in HaB. 
           destruct HaB as [x' HaBx]. destruct HaBx as [HaBx1 HaBx2].  
           rewrite String.eqb_eq in HaBx2. rewrite <- HaBx2 in HaBx1.
           
           simpl in H. intros x H1. simpl in H1. destruct H1.
           rewrite <- H0. assumption.
           
           


Lemma ListElEq_trans_atts: forall (A B C:list att), listElEq String.eqb A B = true
    -> listElEq String.eqb B C = true -> listElEq String.eqb A C = true.
Proof. intro A. induction A as [|a As IHA].
       - intros B C H1 H2. destruct B as [|b Bs]; simpl in H1. assumption. discriminate H1. 
       - intros B C H1 H2. destruct B as [|b Bs]. 
         + discriminate H1. 
         + simpl in H1. destruct ((a =? b)%string) eqn:Hab. 
           ++ simpl in H1. apply String.eqb_eq in Hab. destruct Hab. 
              simpl in H2. destruct (existsb (String.eqb a) C) eqn: HaC.
              +++ simpl. rewrite HaC. apply (IHA Bs). assumption. assumption.
              +++ discriminate H2.
           ++ simpl in H1. destruct (existsb (String.eqb a) Bs) eqn: HaBs.
              
Check (listElEq String.eqb [] []). *)

(** ---------------------------------------------------------------------------------
  Set Operations
-----------------------------------------------------------------------------------*)

(** Union *)
(* Plain Attr List *)
(*Fixpoint atts_union_c (A A': atts) : atts :=
  match A with
  | []      => []
  | a :: xs =>
     match (existsb (String.eqb a) A') with
        | true  => a :: (atts_union_c xs A')
        | false => (atts_union_c xs A')
     end
  end.

Fixpoint vatts_union_c (A A': vatts) : vatts :=
  match A with
  | []           => []
  | (a, e) :: xs =>
     match (findIfExists a A') with
        | Some e'  => (a, e \/(F) e') :: (vatts_union_c xs A')
        | None => (vatts_union_c xs A')
     end
  end.


Fixpoint atts_union_l (A A': atts) : atts :=
  match A with
  | []           => []
  | x :: xs =>
     match (existsb (String.eqb x) A') with
        | true  => (atts_union_l xs A')
        | false =>  x :: (atts_union_l xs A')
     end
  end. 

Fixpoint vatts_union_l (A A': vatts) : vatts :=
  match A with
  | []           => []
  | (a, e) :: xs =>
     match (findIfExists a A') with
        | Some _  => (vatts_union_l xs A')
        | None    => (a, e) :: (vatts_union_l xs A')
     end
  end. 

Fixpoint atts_union (A A': atts) : atts :=
  match A with
  | []           => A'
  | x :: xs =>
     match (existsb (String.eqb x) A') with
        | true  => x :: (atts_union xs (remove String.eqb x A'))
        | false => x :: (atts_union xs A')
     end
  end. 

Fixpoint vatts_union (A A': vatts) : vatts :=
  match A with
  | []           => A'
  | (a, e) :: xs =>
     match (findIfExists a A') with
        | Some e'  => (a, e \/(F) e') ::(vatts_union xs (remove veqb (a, e') A'))
        | None    =>  (a, e)          ::(vatts_union xs A')
     end
  end. 

(*
(* Plain Attr List *)
Definition atts_union (A A': atts) : atts := 
    atts_union_c A  A' ++
    atts_union_l A  A' ++
    atts_union_l A' A.

(* Variational Attr List *)
Definition vatts_union (A A': vatts) : vatts := 
    vatts_union_c A  A' ++
    vatts_union_l A  A' ++
    vatts_union_l A' A.
*)

(* Variational Query Type*)
Definition vqtype_union (Q Q': vqtype) : vatts := 
     vatts_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')). *)

(** Intersection *)
(* Plain Attr List *)
(*Fixpoint atts_inter (A A': atts) : atts :=
  match A with
  | []      => []
  | a :: xs =>
     match (existsb (String.eqb a) A') with
        | true  => a :: (atts_inter xs A')
        | false => (atts_inter xs A')
     end
  end.

(* Variational Attr List *)
Fixpoint vatts_inter (A A': vatts) : vatts :=
  match A with
  | []           => []
  | (a, e) :: xs =>
     match (findIfExists a A') with
        | Some e'  => (a, e /\(F) e') :: (vatts_inter xs A')
        | None => (vatts_inter xs A')
     end
  end.

(* Variational Query Type*)
Definition vqtype_inter (Q Q': vqtype) : vatts := 
     vatts_inter (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')). *)




(** ---------------------------------------------------------------------------------
  nodupatt
-----------------------------------------------------------------------------------*)

(*Definition rm_hd_never_fail (lst : list vatt) (safety_proof : lst <> nil) : vatts :=
  (match lst as b return (lst = b -> vatts) with
    | nil => (fun foo : lst = nil =>
                   match (safety_proof foo) return vatts with
                   end
                )
    | (ae a e) :: _ => (fun foo : lst = (ae a e) :: _ =>
                   removeAtt a lst
                )
  end) eq_refl. *)

(* stops search when the first occurence is hit *)
(*Fixpoint extract_e (x : att) (v : vatts) : option fexp := 
   match v with 
   | nil          => None
   | ae a e :: vs => 
          match (string_beq x a) with
          | true  => Some e
          | false => extract_e x vs
          end
   end.*)


(*Fixpoint nodupatt (v: vatts) : vatts := 
   match v with 
   | nil          => nil
   | ae a e :: vs =>  match existsbAtt a vs with
                      | false => ae a e :: nodupatt vs
                      | true  => let e' := extract_e a v in
                         (ae a e') :: nodupatt (removeAtt a vs)
                      end
   end.*)


(* Fixpoint nodupatt (v: vatts) : vatts := 
   match v with 
   | nil          => nil
   | ae a e :: vs => 
          match (find (string_beq a) found) with
          | Some _  => nodupatt found vs
          | None => let e' := (extract_e a v) in
                         (ae a e') :: nodupatt (found ++ [a]) vs
          end
   end.



Fixpoint removeAtt (a : att) (A: vatts) : vatts := 
    match A with 
   | nil => nil
   | ae a' e' :: A' => match (string_beq a a') with
                     | true => removeAtt a A'
                     | false => ae a' e' :: removeAtt a A'
                     end
   end.

Fixpoint nodupatt (A: vatts) : vatts := 
   match A with 
   | nil => nil
   | ae a e :: A => match (extract_e a A) with
                   | (litB false) => (ae a e) :: nodupatt A
                   | (e'        ) => (ae a (e \/(F) e')) :: nodupatt (removeAtt a A)
                   end
   end.
*)
 
