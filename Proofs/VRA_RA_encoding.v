(** Variational relational algebra *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Import Maps.
Require Export List.
(*Require Export Arith.
Require Export String.*)
Require Export Logic.

Load Feature.
Import Feature.

Module VRA_RA_encoding.


(** nat ascii comparison*)

Lemma nat_of_ascii_injective:
  forall c1 c2, Ascii.nat_of_ascii c1 = Ascii.nat_of_ascii c2 -> c1 = c2.
Proof.
  intros; simpl.
  assert (Ascii.ascii_of_nat (Ascii.nat_of_ascii c1) =
          Ascii.ascii_of_nat (Ascii.nat_of_ascii c2))
      as Hinvol. auto.
  repeat rewrite Ascii.ascii_nat_embedding in Hinvol.
  trivial.
Qed.


(** -------------------------------------------------------------
  Attribute: Type and Comparison Function, Lemmas
-----------------------------------------------------------------*)
(* Plain Attribute *)
Definition att : Type := string.

Inductive comp : Type := 
  | EQc | LTc | GTc.

(* Variational Attribute *)
Definition vatt : Type := (att * fexp)%type. (*assuming always annotated; could've used option*)

(** Attribute (string-)comparison function and associated lemmas *)
Fixpoint string_comp (s1 s2: att): comp :=
   match s1, s2 with
 | EmptyString, EmptyString => EQc
 | String c1 s1', String c2 s2' => 
             match (compare (Ascii.nat_of_ascii c1) (Ascii.nat_of_ascii c2)) with
             | Eq => string_comp s1' s2'
             | Lt => LTc
             | Gt => GTc
             end
 | EmptyString,_ => LTc
 | _, EmptyString => GTc
 end.

Lemma string_compEq_refl: forall s, string_comp s s = EQc.
Proof. intros. induction s. - reflexivity. 
       - simpl. induction (Ascii.nat_of_ascii a). simpl. assumption. simpl.
         assumption.
Qed.
         
Lemma string_compEq_eq : forall a a0, string_comp a a0 = EQc <-> a = a0.
Proof. 
     split. 
     - intros. generalize dependent a0.
       induction a as [|c a].
       + destruct a0 as [|c0 a0]. 
         ++ simpl. reflexivity.
         ++ intro. discriminate H.
       + destruct a0 as [|c0 a0].
         ++ intro. discriminate H.
         ++ intro. simpl in H. 
            destruct (Ascii.nat_of_ascii c ?= Ascii.nat_of_ascii c0) eqn: C.
            +++ apply nat_compare_eq in C. apply nat_of_ascii_injective in C.
                apply IHa in H. rewrite C, H. reflexivity.
            +++ discriminate H. +++ discriminate H.
     - intros. destruct a as [|c a].
       + intros. destruct a0 as [|c0 a0]. 
         ++ simpl. reflexivity. 
         ++ discriminate H. 
       + intros. destruct a0 as [|c0 a0]. 
         ++ discriminate H. 
         ++ inversion H. rewrite string_compEq_refl. reflexivity.
Qed.

Lemma string_comp_eqc_symm : forall a a0, string_comp a a0 = EQc
    -> string_comp a0 a = EQc.
Proof. intros. apply string_compEq_eq in H.  symmetry in H. rewrite string_compEq_eq.
       assumption. 
Qed.

Lemma string_comp_lt_trans : forall a a1 a2, 
      (string_comp a1 a = EQc \/ string_comp a1 a = LTc)
      /\ string_comp a a2 = LTc -> string_comp a1 a2 = LTc.
Proof. intros. destruct H as [H1 H2].
       destruct H1 as [H1 | H1].
       - destruct a as [|b]; try (destruct a1 as [|b1]);  
         try (destruct a1 as [|b1]); try (discriminate H2);
         try (discriminate H1); try (assumption); try (discriminate H1).
         + rewrite string_compEq_eq in H1.
           rewrite <- H1 in H2. assumption.
       - generalize dependent a2. generalize dependent a1. induction a as [|b];
         destruct a1 as [|b1]; destruct a2 as [|b2]; intros; try (discriminate H2);
         try (discriminate H1); try (assumption); try (reflexivity).
         + simpl in H1, H2. simpl. 
           destruct (Ascii.nat_of_ascii b1 ?= Ascii.nat_of_ascii b) eqn: b1b.
           ++ destruct (Ascii.nat_of_ascii b ?= Ascii.nat_of_ascii b2) eqn: bb2.
              +++ apply nat_compare_eq in b1b. apply nat_compare_eq in bb2.
                  eapply Nat.eq_trans in b1b. apply b1b in bb2.
                  rewrite bb2.
                  rewrite Nat.compare_refl.
                  apply IHa. assumption. assumption.
              +++ apply nat_compare_eq in b1b. 
                  apply nat_of_ascii_injective in b1b.
                  apply nat_compare_lt in bb2.
                  rewrite <- b1b in bb2. 
                  rewrite nat_compare_lt in bb2. rewrite bb2.
                  reflexivity.
              +++ discriminate H2.
           ++ destruct (Ascii.nat_of_ascii b ?= Ascii.nat_of_ascii b2) eqn: bb2.
              +++ apply nat_compare_eq in bb2. 
                 apply nat_of_ascii_injective in bb2.
                 apply nat_compare_lt in b1b.
                 rewrite bb2 in b1b. 
                 rewrite nat_compare_lt in b1b. rewrite b1b.
                 reflexivity.
              +++ apply nat_compare_lt in bb2.
                 apply nat_compare_lt in b1b. 
                 eapply Nat.lt_trans in bb2. 
                 rewrite nat_compare_lt in bb2.
                 rewrite bb2. reflexivity. assumption.
              +++ discriminate H2.
           ++ destruct (Ascii.nat_of_ascii b ?= Ascii.nat_of_ascii b2) eqn: bb2.
              +++ discriminate H1.
              +++ discriminate H1.
              +++ discriminate H2. 
Qed.

Lemma string_comp_lt_gt: forall a a0, string_comp a a0 = LTc
    <-> string_comp a0 a = GTc.
Proof. intros. split. 
       - intros. generalize dependent a. induction a0 as [| b0]. 
         + intros. destruct a as [|b]; simpl in H; discriminate H. 
         + intros. destruct a as [|b]. ++ simpl. reflexivity.
           ++ simpl.
            destruct (Ascii.nat_of_ascii b ?= Ascii.nat_of_ascii b0) eqn: anat.
            +++ simpl in H. rewrite anat in H. apply nat_compare_eq in anat. 
             rewrite anat. rewrite Nat.compare_refl.
             apply IHa0 in H.  assumption.
             +++ apply nat_compare_lt in anat.
                 apply nat_compare_gt in anat.  
                 rewrite anat. 
                 reflexivity. 
             +++ simpl in H. 
                 rewrite anat in H. discriminate H. 
      - intros. generalize dependent a. induction a0 as [| b0]. 
         + intros. destruct a as [|b]; simpl in H; discriminate H. 
         + intros. destruct a as [|b]. ++ simpl. reflexivity.
           ++ simpl.
            destruct (Ascii.nat_of_ascii b0 ?= Ascii.nat_of_ascii b) eqn: anat.
            +++ simpl in H. rewrite anat in H. apply nat_compare_eq in anat. 
             rewrite anat.
             rewrite Nat.compare_refl. apply IHa0 in H.  assumption.
             +++ simpl in H. 
                 rewrite anat in H. discriminate H. 
             +++ apply nat_compare_gt in anat.
                 apply nat_compare_lt in anat.  
                 rewrite anat. 
                 reflexivity.
Qed. 

(** -----------------------att vatt-------------------------- **)


(** ------------------------------------------------------------
  Attribute List
---------------------------------------------------------------*)

(* Plain Attribute List *)
Definition atts : Type := list att.

(** Properties *)
(* List of attributes are Locally sorted (see A2) *)
Inductive LocallySortedAtts : list att -> Prop :=
  | LSorted_nil : LocallySortedAtts []
  | LSorted_cons1 a : LocallySortedAtts [a]
  | LSorted_consn a b l :
      LocallySortedAtts (b :: l) -> string_comp a b = LTc
       -> LocallySortedAtts (a :: b :: l).

(* List of attributes are set (non-dup)*)
Inductive NoDup {A: Type}: list A -> Prop :=
 | NoDup_nil : NoDup nil
 | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

(** Assumption *)
Definition assumption_atts (a:atts): Prop:= 
forall (a:atts), LocallySortedAtts a /\ NoDup a.
(*------------------------------------------------------------------------*)

(* Variational Attribute List *)
Definition vatts : Type := list vatt.

(** Properties *)
(* List of variational attributes are Locally sorted *)
Inductive LocallySortedVAtts : list vatt -> Prop :=
  | LSorted_nil_v : LocallySortedVAtts []
  | LSorted_cons1_v a : LocallySortedVAtts [a]
  | LSorted_consn_v a b l :
      LocallySortedVAtts (b :: l) ->  string_comp (fst a) (fst b) = LTc
       -> LocallySortedVAtts (a :: b :: l).

(** Assumption*)
Lemma assumption_vatts : forall (v:vatts), (LocallySortedVAtts v)  /\ (NoDup v).
Proof. Admitted.
(*---------------------------------------------------------------------------*)

(* Configuration Variational Attribute List(Set) A[]c (see A3)*)
Fixpoint configVAttSet (vA : vatts) (c : config) : atts :=
  match vA with
  | nil                  => nil
  | cons (a, e) vas => if semE e c 
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
Proof. intros. simpl. destruct (E[[ e]] c); reflexivity. Qed.
(** ---------------------qtype vqtype---------------------- **)



(*-----------------------Functions----------------------------*)


(** ------------------------------------------------------------
  Subsumption (of Variational Set) defintion
---------------------------------------------------------------*)
Fixpoint sublist (X X': list string): bool :=
    match X with
    | nil => match X' with 
             | nil => true
             | cons _ _ => false
             end
    | cons x xs => match X' with 
                   | nil => false
                   | cons x' xs' => if eqb_string x x' then sublist xs xs'
                                         else sublist (x::xs) xs'
                   end
    end.

(* Subsumption of Plain Set (Query Type) *)
Definition subsump_qtype_bool (A A': qtype) : bool := sublist A A'.

(* Subsumption of Variational Set (Query Type) *)
Definition subsump_vqtype ( X X': vqtype ) : Prop := forall c, 
    sublist (configVQtype X c) (configVQtype X' c) = true.

(*----------------------subsump--------------------------------*)


(** ------------------------------------------------------------
  Equivalence (of Variational Set) definition
---------------------------------------------------------------*)
(* Plain Set (Query Type) Equivalence*)
Fixpoint equiv_qtype_bool (A A': qtype) : bool := 
    match A with
    | nil => match A' with 
             | nil => true
             | cons _ _ => false
             end
    | cons x xs => match A' with 
                   | nil => false
                   | cons x' xs' => eqb_string x x' && equiv_qtype_bool xs xs'
                   end
    end.

(* Variational Set (non-annnot-Var Attr) Equivalence (Only needed for next one)*)
Definition equiv_vatts ( X X': vatts ) : Prop := forall c, configVAttSet X c = configVAttSet X' c.

(* Variational Set (annotated-Var Query Type) Equivalence *)
Definition equiv_vqtype ( X X': vqtype ) : Prop := equiv_vatts (fst X) (fst X') /\ equivE (snd X) (snd X').

(* Type Equivalence is reflexive*)
Lemma equiv_qtype_bool_refl: forall A, equiv_qtype_bool A A = true.
Proof.
  intros. induction A. 
  + reflexivity. 
  + simpl. rewrite <- eqb_string_refl. simpl. apply IHA.
Qed.

(*---------------------------equiv-----------------------------*)

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
  | (x, e) :: xs => (x, e /\(F) m) :: push_annot xs m
  end.

Lemma fold_push_annot: forall x e xs m, 
(x, e /\(F) m) :: push_annot xs m = push_annot ((x, e) :: xs) m.
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

(* see A4. Ackermann Function *)

(** Union *)
(* Plain Attr List *)
Fixpoint atts_union (A A': atts) : atts :=
  let fix merge_aux_atts A' :=
  match A, A' with
  | [], _ => A'
  | _, [] => A
  |  a ::xs,  a' ::xs' =>
      match (string_comp a a') with
          | EQc => a :: (atts_union xs xs')
          | LTc => a :: (atts_union xs A')
          | GTc => a':: merge_aux_atts xs' 
      end
  end
  in merge_aux_atts A'.

(* Variational Attr List *)
Fixpoint vatts_union (A A': vatts) : vatts :=
  let fix merge_aux_vatts A' :=
  match A, A' with
  | [], _ => A'
  | _, [] => A
  | (a, e) ::xs,  (a', e') ::xs' =>
      match (string_comp a a') with
          | EQc => (a, e \/(F) e') :: (vatts_union xs xs')
          | LTc => (a, e) :: (vatts_union xs A')
          | GTc => (a', e') :: merge_aux_vatts xs'
      end
  end
  in merge_aux_vatts A'.

(* Variational Query Type*)
Definition vqtype_union (Q Q': vqtype) : vatts := 
     vatts_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')).
(*------------------------------------------------------------------------------*)

(** Intersection *)
(* Plain Attr List *)
Fixpoint atts_inter (A A': atts) : atts :=
  let fix merge_aux_attsi A' :=
  match A, A' with
  | [], _ => []
  | _, [] => []
  |  a ::xs,  a' ::xs' =>
      match (string_comp a a') with
          | EQc => a :: (atts_inter xs xs')
          | LTc =>      (atts_inter xs A')
          | GTc =>       merge_aux_attsi xs' 
      end
  end
  in merge_aux_attsi A'.

(* Variational Attr List *)
Fixpoint vatts_inter (A A': vatts) : vatts :=
  let fix merge_aux_vattsi A' :=
  match A, A' with
  | [], _ => []
  | _, [] => []
  | (a, e) ::xs,  (a', e') ::xs' =>
      match (string_comp a a') with
          | EQc => (a, e /\(F) e') :: (vatts_inter xs xs')
          | LTc =>                    (vatts_inter xs A')
          | GTc =>                     merge_aux_vattsi xs'
      end
  end
  in merge_aux_vattsi A'.

(* Variational Query Type*)
Definition vqtype_inter (Q Q': vqtype) : vatts := 
     vatts_inter (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')).

(* Check whether sets are disjoint - A intersect A' = {}*)
Definition is_disjoint_bool (A A': atts) : bool :=
  match atts_inter A A' with
  | [] => true
  | _  => false
  end.
(*-------------------------------------------------------------------------------*)

(** lemmas to expand second recursive function used for ackermann *)
(* better name *)
Lemma ackerman_resolve_vatts_inter: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = GTc ->
   vatts_inter (v ::xs)  (v' ::xs') = vatts_inter (v ::xs) xs'.
Proof. intros. simpl. destruct v. destruct v'. simpl in H. 
       rewrite H. reflexivity. 
Qed.

Lemma ackerman_resolve_atts_inter: forall (a a':att) (xs xs':atts),
 (string_comp a a') = GTc ->
   atts_inter (a ::xs)  (a' ::xs') = atts_inter (a ::xs) xs'.
Proof. intros. simpl. rewrite H. reflexivity. Qed.


Lemma ackerman_resolve_vatts_union: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = GTc ->
   vatts_union (v ::xs)  (v' ::xs') = v' :: vatts_union (v ::xs) xs'.
Proof. intros. simpl. destruct v. destruct v'. simpl in H. 
       rewrite H. reflexivity. 
Qed.

Lemma ackerman_resolve_atts_union: forall (a a':att) (xs xs':atts),
 (string_comp a a') = GTc ->
   atts_union (a ::xs)  (a' ::xs') = a' :: atts_union (a ::xs) xs'.
Proof. intros. simpl. rewrite H. reflexivity. Qed.
(*---------------------------------------------------------------*)

(** lemmas for set OP with identity and union commutivity *)

Lemma atts_union_nil_r: forall A, atts_union A [] = A.
Proof. intros. destruct A; reflexivity. Qed.

Lemma atts_union_nil_l: forall A, atts_union [] A = A.
Proof. intros. simpl. destruct A; reflexivity. Qed.

Lemma atts_inter_nil_r: forall A, atts_inter A [] = [].
Proof. intros. destruct A; reflexivity. Qed.

Lemma atts_inter_nil_l: forall A, atts_inter [] A = [].
Proof. intros. simpl. destruct A; reflexivity. Qed.

Lemma vatts_union_nil_r : forall A, vatts_union A [] = A.
Proof. intros. simpl. destruct A. reflexivity. simpl. 
       destruct v. reflexivity. Qed.

Lemma vatts_union_nil_l : forall A, vatts_union [] A = A.
Proof. intros. destruct A. reflexivity. destruct v. reflexivity. Qed.

Lemma vatts_inter_nil_r : forall A, vatts_inter A [] = [].
Proof. intros. simpl. destruct A. reflexivity. simpl. 
       destruct v. reflexivity. Qed.

Lemma vatts_inter_nil_l : forall A, vatts_inter [] A = [].
Proof. intros. destruct A. reflexivity. destruct v. reflexivity. Qed.

Lemma atts_union_comm: forall A A', 
   atts_union A A' = atts_union A' A.
Proof. intros. generalize dependent A'. induction A.
       + destruct A'. 
         ++ reflexivity.
         ++ simpl. reflexivity.
       + induction A'. ++ reflexivity.
         ++  destruct (string_comp a a0) eqn: SC.
             +++ simpl. rewrite SC. apply string_comp_eqc_symm in SC. rewrite SC.
                  rewrite IHA. rewrite string_compEq_eq in SC. rewrite SC. reflexivity.
             +++ unfold atts_union at 1; fold atts_union. rewrite SC.
                 apply string_comp_lt_gt in SC. rewrite ackerman_resolve_atts_union. 
                 rewrite IHA. reflexivity. assumption.
             +++ rewrite ackerman_resolve_atts_union. 
                 apply string_comp_lt_gt in SC as SC_rev. 
                 unfold atts_union at 2; fold atts_union. rewrite SC_rev. 
                 rewrite IHA'. reflexivity. assumption.
Qed.

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
  | Relation_vE_fm : forall e rn A e',
        ~ sat (  e'    /\(F)   (~(F) (e)) ) ->
       vtype e (rel_v (rn, (A, e'))) (A, e') (** variational context is initialized with feature_model which is more general than the overall pc of any relation in vdbms *)
  (*   -- intro MORE specific context --
    empty |- rn : A^e'  ~sat(e /\ (~e'))
    ------------------------------------  RELATION-E 
               e  |- rn : A^e
   *)
  | Relation_vE : forall e rn A e',
       ~ sat (  e    /\(F)   (~(F) (e')) ) ->
       vtype e (rel_v (rn, (A, e'))) (A, e)
  (*   -- PROJECT-E --  *)
  | Project_vE: forall e vq e' A' A,
       vtype e vq (A', e') -> 
       subsump_vqtype (A, e) (A', e') ->
       vtype e (proj_v A vq) (A, e)
  (*  -- CHOICE-E --  *)
  | Choice_vE: forall e e' vq1 vq2 A1 e1 A2 e2,
       (*LocallySortedVAtts A1 /\ LocallySortedVAtts A2 ->*)
       vtype (e /\(F) e') vq1 (A1, e1) ->
       vtype (e /\(F) (~(F) e')) vq2 (A2, e2) ->
       vtype e (chcQ e' vq1 vq2)
        (vqtype_union (A1, e1) (A2, e2) , e1 \/(F) e2)
            (*e1 and e2 can't be simultaneously true.*)
  (*  -- PRODUCT-E --  *)
  | Product_vE: forall e vq1 vq2 A1 e1 A2 e2 ,
       vtype e  vq1 (A1, e1) ->
       vtype e  vq2 (A2, e2) ->
       vqtype_inter (A1, e1) (A2, e2) = nil ->
       vtype e  (prod_v vq1 vq2)
        (vqtype_union (A1, e1) (A2, e2) , e1 \/(F) e2)
  (*  -- SETOP-E --  *)
  | SetOp_vE: forall e vq1 vq2 A1 e1 A2 e2 op,
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

