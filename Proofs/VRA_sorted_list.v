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

Module VRA.
(** Variational Condition Syntax *)

Definition att : Type := string.

Inductive comp : Type := 
  | EQc | LTc | GTc.

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


(** asuumption: list att s are set thus string_comp ( a) ( b) = EQc can't happen*)
Inductive LocallySortedAtts : list att -> Prop :=
  | LSorted_nil : LocallySortedAtts []
  | LSorted_cons1 a : LocallySortedAtts [a]
  | LSorted_consn a b l :
      LocallySortedAtts (b :: l) -> string_comp a b = LTc
       -> LocallySortedAtts (a :: b :: l).

Inductive NoDup {A: Type}: list A -> Prop :=
 | NoDup_nil : NoDup nil
 | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

(** variational to non-variational condiitions configurations *)

Inductive op : Type :=
  | eq | GTE | LTE | GT | LT | neq.

Inductive cond : Type :=
  | litCB  : bool -> cond
  | relOPI : op -> att -> nat -> cond
  | relOP  : op -> att -> att -> cond
  | compT  : cond -> cond 
  | meetT  : cond -> cond -> cond
  | joinT  : cond -> cond -> cond.

Inductive vcond : Type :=
  | litCB_v  : bool -> vcond
  | relOPI_v : op -> att -> nat -> vcond
  | relOP_v  : op -> att -> att -> vcond
  | compT_v  : vcond -> vcond
  | meetT_v  : vcond -> vcond -> vcond
  | joinT_v  : vcond -> vcond -> vcond
  | chcT     : fexp -> vcond -> vcond -> vcond.

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

(** -----------------------conds------------------------ **)

(** variational to non-variational relation-schema, attr, query configurations *)

Definition r : Type := string.
Definition atts : Type := list att.

Definition assumption_atts (a:atts): Prop:= forall (a:atts), LocallySortedAtts a /\ NoDup a.

Definition relS : Type := (r * atts) % type.

Inductive setop : Type := union | inter | diff.


(* @meeting: not sure about rel. should it get r or relS?? in RA is just the relation name,
although for proving purposes consider it relation schema might not be a bad idea.
still I'm not sure. same goes for vquery. this affects the typing relation since now we don't 
need to pass the schema. SHOULD DISCUSS THIS!!*)
Inductive query : Type :=
  | rel   : relS    -> query
  | sel   : cond    -> query -> query 
  | proj  : atts    -> query -> query 
  | join  : cond    -> query -> query -> query 
  | prod  : query   -> query -> query 
  | setU  : setop   -> query -> query -> query.

Definition vatt : Type := (att * fexp)%type. (*assuming always annotated; could've used option*)

(** asuumption: list vatt s are set thus string_comp (fst a) (fst b) = EQc can't happen*)
Inductive LocallySortedVAtts : list vatt -> Prop :=
  | LSorted_nil_v : LocallySortedVAtts []
  | LSorted_cons1_v a : LocallySortedVAtts [a]
  | LSorted_consn_v a b l :
      LocallySortedVAtts (b :: l) ->  string_comp (fst a) (fst b) = LTc
       -> LocallySortedVAtts (a :: b :: l).

Definition vatts : Type := list vatt.

(** variational attribute list from queries are explicitly typed. 
Assuming variational attribute list from schema are also explicitly typed.
Thus not looking up pc(rel(a)) *)

(** A[]_c *)
Fixpoint configVAttSet (vA : vatts) (c : config) : atts :=
  match vA with
  | nil                  => nil
  | cons (a, e) vas => if semE e c 
                             then (cons a (configVAttSet vas c))
                             else (           configVAttSet vas c )
  end.

Definition vrelS : Type := (r * (vatts * fexp) ) %type. (*assuming always annotated; could've used option*)

Definition configVRelS (vr : vrelS) (c : config) : relS := if semE (snd (snd vr)) c
                                                         then  (fst vr, (configVAttSet (fst (snd vr) ) c)) 
                                                           else  (fst vr, nil).
Inductive vquery : Type :=
  | rel_v   : vrelS    -> vquery
  | sel_v   : vcond    -> vquery -> vquery 
  | proj_v  : vatts    -> vquery -> vquery 
  | chcQ    : fexp     -> vquery -> vquery -> vquery
  | join_v  : vcond    -> vquery -> vquery -> vquery 
  | prod_v  : vquery   -> vquery -> vquery 
  | setU_v  : setop    -> vquery -> vquery -> vquery.

(** Q[]_c *)
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

(** ---------------rel-schema, attr, query-------------- **)


(** variational to non-variational schema configurations *)

Definition schema : Type := (list relS)%type. (* relS : (r * atts) *)

Definition vschema : Type := ( (list vrelS) * fexp )%type. (*assuming always annotated; could've used option*)

Fixpoint configVRelSSet (vrelSSet : list vrelS) (c : config) : list relS :=
  match vrelSSet with 
  | nil => nil
  | cons vr vrs => cons (configVRelS vr c) (configVRelSSet vrs c)
  end.

Definition configVSchema (vs : vschema) (c : config) : schema := if semE (snd vs) c 
                                                        then configVRelSSet (fst vs) c
                                                          else nil.
(** --------------------schema--------------------------- **)

(** variational to non-variational Qtype configurations *)

Definition vqtype : Type := (vatts * fexp) %type. (*assuming always annotated; could've used option*)
Definition qtype  : Type := (atts) %type.

Definition configVQtype (vqt : vqtype) (c : config) : qtype := 
      match vqt with 
      |(V, e) => if semE e c then  configVAttSet V c else  nil
      end.
(*if semE (snd vqt) c
                                                         then  configVAttSet (fst vqt) c
                                                           else  nil. *)
(** ---------------------qtype-------------------------- **)

(*Reserved Notation "e S '|-' q ':' T"
                  (at level 71, left associativity).*)

(** not_sat_not_prop *)

Lemma config_det_plain: forall A a c, (exists e, In (a, e) A /\ (E[[ e ]] c) = true) 
                   <-> In a (configVAttSet A c).
Proof.
  intros. split. 
  - intros. destruct H as [e H]. destruct H as [H1 H2]. induction A as [| (a1, e1)].
    + simpl in H1. destruct H1.
    + simpl in H1. simpl. destruct H1.
      ++ inversion H. rewrite H2. simpl. left. reflexivity.
      ++ apply IHA in H.  destruct (E[[ e1]] c). 
         +++ simpl. right. assumption. 
         +++ assumption.
  - intros. induction A as [| (a1, e1)]. 
    ++ simpl in H.  destruct H. 
    ++ simpl in H. destruct (E[[ e1]] c) eqn: E.
       +++  simpl in H. destruct H.
            { rewrite H. exists e1. simpl. split.  left. reflexivity. assumption. }
            { apply IHA in H. simpl. destruct H as [e' H]. exists e'. destruct H. split. 
              right. assumption. assumption. }
       +++ apply IHA in H. destruct H as [e' H]. exists e'. simpl. destruct H. split. 
              right. assumption. assumption. 
Qed. 

Lemma configVAttSet_app_dist: forall A A' c, configVAttSet A c ++ configVAttSet A' c = configVAttSet (A++A') c.
Proof.
  intros. induction A as [|(a, e)]. 
  - destruct A' as [|(a', e')]. 
    + reflexivity.
    + destruct (E[[ e']] c);
        reflexivity.
  - destruct A' as [|(a', e')]. 
    + simpl. destruct (E[[ e]] c); 
        rewrite app_nil_r; rewrite app_nil_r;  reflexivity.
    + simpl. destruct (E[[ e]] c);
        destruct (E[[ e']] c) eqn: E';
          rewrite <- IHA; simpl; rewrite E'; reflexivity.
Qed. 

Fixpoint annot_dist_helper (v : vatts) (e: fexp) : vatts := 
 match v with
 | nil => nil
 | cons (a, e') vas  =>
     cons (a, e' /\(F) e) (annot_dist_helper vas e)
 end.

Definition annot_dist ( X : (vatts * fexp)) : vatts := annot_dist_helper (fst X) (snd X).

Definition avatts_inter (A A': (vatts * fexp)) : vatts := nil.

Fixpoint findx (x : att) (A : atts) : bool :=
    match A with
    | nil => false
    | y :: ys => if eqb_string x y then true else findx x ys
    end.

Fixpoint atts_inter (A A': atts) : atts :=  
  match A with
  | nil => nil
  | x :: xs => if findx x A' then x::(atts_inter xs A') else atts_inter xs A'
  end.

Theorem In_findx_iff: forall a l, In a l <-> findx a l = true.
Proof. intros. split. 
       - intros. induction l. 
         + simpl in H. contradiction.
         + simpl in H. destruct H. 
           ++ simpl. rewrite H. rewrite <- eqb_string_refl. reflexivity.
           ++ apply IHl in H. simpl. destruct (eqb_string a a0). +++ reflexivity. +++ assumption.
       - intros. induction l.
         ++ simpl in H. discriminate H.
         ++ simpl. simpl in H. destruct (eqb_string a a0) eqn:E in H. 
            +++ left. rewrite eqb_string_true_iff in E. symmetry. assumption. +++ apply IHl in H. right. assumption.
Qed.

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

Definition subsump_vatts ( X X': vatts ) : Prop := forall c, 
    sublist (configVAttSet X c) (configVAttSet X' c) = true.

Definition subsump_vqtype ( X X': vqtype ) : Prop := forall c, 
    sublist (configVQtype X c) (configVQtype X' c) = true.

Definition subsump ( X X': qtype ) : Prop := forall a, In a X -> In a X'.

Definition subsump_qtype_bool (A A': qtype) : bool := sublist A A'.

Definition subsump_qtype ( A A': qtype ) : Prop := forall a, In a A -> In a A'.

(*Definition atts_union (A A': atts) : atts := A ++ A'.*)

Definition equiv_vatts ( X X': vatts ) : Prop := forall c, configVAttSet X c = configVAttSet X' c.

Definition equiv_vqtype ( X X': vqtype ) : Prop := equiv_vatts (fst X) (fst X') /\ equivE (snd X) (snd X').

Definition equiv ( X X': qtype ) : Prop := X = X'.

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

Theorem equiv_qtype_bool_refl: forall A, equiv_qtype_bool A A = true.
Proof.
  intros. induction A. 
  + reflexivity. 
  + simpl. rewrite <- eqb_string_refl. simpl. apply IHA.
Qed.

Definition equiv_qtype ( A A': qtype ) : Prop := A = A'.

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

Fixpoint avatts_union (A A': vatts) : vatts :=
  let fix merge_aux_vatts A' :=
  match A, A' with
  | [], _ => A'
  | _, [] => A
  | (a, e) ::xs,  (a', e') ::xs' =>
      match (string_comp a a') with
          | EQc => (a, e \/(F) e') :: (avatts_union xs xs')
          | LTc => (a, e) :: (avatts_union xs A')
          | GTc => (a', e') :: merge_aux_vatts xs'
      end
  end
  in merge_aux_vatts A'.

(** Prove that both unions preserve sorting (by lexical order)*)
(** Define a prop called sorted on vatts and atts*)

(*Definition globally_less_dec_ord : forall v v' xs xs', 
  globally_less -> (string_comp (fst v) (fst v')) = EQc \/ (string_comp (fst v) (fst v')) = LTc -> 
  (forall c, (E[[(snd v)]] c) = true /\ (E[[(snd v')]] c) = false ->
   atts_union (configVAttSet (v :: xs) c)
    (configVAttSet (v' :: xs') c) = (fst v) :: atts_union (configVAttSet xs c)
     (configVAttSet xs' c) ).
Proof. 
  intros. unfold globally_less in H. 
  intros. 
Admitted.*)

Lemma ackerman_resolve_vatts: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = GTc ->
   avatts_union (v ::xs)  (v' ::xs') = v' :: avatts_union (v ::xs) xs'.
Proof. intros. simpl. destruct v. destruct v'. simpl in H. 
       rewrite H. reflexivity. 
Qed.

Lemma ackerman_resolve_atts: forall (a a':att) (xs xs':atts),
 (string_comp a a') = GTc ->
   atts_union (a ::xs)  (a' ::xs') = a' :: atts_union (a ::xs) xs'.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma string_comp_symm : forall a a0, string_comp a a0 = EQc
    -> string_comp a0 a = EQc.
Proof. intros. apply string_compEq_eq in H.  symmetry in H. rewrite string_compEq_eq.
       assumption. 
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
             apply nat_of_ascii_injective in anat. rewrite anat.
             assert (I: forall k, Ascii.nat_of_ascii k ?= Ascii.nat_of_ascii k = Eq). 
             { intros. induction (Ascii.nat_of_ascii k).
               reflexivity.  simpl. assumption. }
             rewrite I. apply IHa0 in H.  assumption.
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
             apply nat_of_ascii_injective in anat. rewrite anat.
             assert (I: forall k, Ascii.nat_of_ascii k ?= Ascii.nat_of_ascii k = Eq). 
             { intros. induction (Ascii.nat_of_ascii k).
               reflexivity.  simpl. assumption. }
             rewrite I. apply IHa0 in H.  assumption.
             
             +++ simpl in H. 
                 rewrite anat in H. discriminate H. 
             +++ apply nat_compare_gt in anat.
                 apply nat_compare_lt in anat.  
                 rewrite anat. 
                 reflexivity.
Qed. 


Lemma avatts_union_trans: forall A A' c, 
   configVAttSet (avatts_union A A') c = configVAttSet (avatts_union A' A) c.
Proof. intros. generalize dependent A'. induction A. 
       - destruct A'.
         + simpl. reflexivity.
         + simpl. destruct v as (v', e'). reflexivity.
       - induction A' as [| v A'].
        + simpl. destruct a. reflexivity.
        + destruct a, v. 
          assert (I: forall a e A, configVAttSet ( (a, e) :: A ) c = 
             if semE e c then a :: (configVAttSet A c) else configVAttSet A c ). { reflexivity. }
          destruct (string_comp a a0) eqn: cmp. 
          ++ unfold avatts_union at 1; fold avatts_union. rewrite cmp.
             apply string_compEq_eq in cmp as cmp_eq.
             apply string_comp_symm in cmp. 
             simpl. rewrite cmp.
             rewrite cmp_eq. rewrite IHA. 
             rewrite I. simpl. rewrite orb_comm. reflexivity.
          ++ unfold avatts_union at 1; fold avatts_union. rewrite cmp.
             apply string_comp_lt_gt in cmp as cmp_rev.
             rewrite ackerman_resolve_vatts. rewrite I. rewrite I. 
             destruct (E[[ f]] c). rewrite IHA.
             reflexivity. apply IHA. simpl. assumption.
          ++ apply string_comp_lt_gt in cmp as cmp_rev.
             unfold avatts_union at 2; fold avatts_union. rewrite cmp_rev.
             rewrite ackerman_resolve_vatts.  rewrite I. rewrite I. 
             destruct (E[[ f0]] c). rewrite IHA'.  reflexivity. 
             apply IHA'. simpl. assumption.
Qed.

Lemma atts_union_trans: forall A A', 
   atts_union A A' = atts_union A' A.
Proof. intros. generalize dependent A'. induction A.
       + destruct A'. 
         ++ reflexivity.
         ++ simpl. reflexivity.
       + induction A'. ++ reflexivity.
         ++  destruct (string_comp a a0) eqn: SC.
             +++ simpl. rewrite SC. apply string_comp_symm in SC. rewrite SC.
                  rewrite IHA. rewrite string_compEq_eq in SC. rewrite SC. reflexivity.
             +++ unfold atts_union at 1; fold atts_union. rewrite SC.
                 apply string_comp_lt_gt in SC. rewrite ackerman_resolve_atts. 
                 rewrite IHA. reflexivity. assumption.
             +++ rewrite ackerman_resolve_atts. 
                 apply string_comp_lt_gt in SC as SC_rev. 
                 unfold atts_union at 2; fold atts_union. rewrite SC_rev. 
                 rewrite IHA'. reflexivity. assumption.
Qed.

Lemma atts_union_nil_r: forall A, atts_union A [] = A.
Proof. intros. destruct A. reflexivity. reflexivity. Qed.

Lemma atts_union_nil_l: forall A, atts_union [] A = A.
Proof. intros. simpl. destruct A. reflexivity. reflexivity. Qed.

Fixpoint recurse_annot (A: vatts) (m: fexp) : (vatts):=
  match A with
  | nil => nil
  | (x, e) :: xs => (x, e /\(F) m) :: recurse_annot xs m
  end.

Definition annoted (A: vqtype) : vatts := 
   match A with 
   | (nil, m) => nil
   | (v , m)  => recurse_annot v m
   end.


Lemma avatts_union_nil_r : forall A, avatts_union A [] = A.
Proof. intros. simpl. destruct A. reflexivity. simpl. 
       destruct v. reflexivity. Qed.

Lemma avatts_union_nil_l : forall A, avatts_union [] A = A.
Proof. intros. destruct A. reflexivity. destruct v. reflexivity. Qed.


(**  Set Printing All. *)


(*Lemma string_comp_trans: forall a a' a'',(string_comp a a') = EQc \/ (string_comp a a') = LTc ->
      (string_comp a' a'') = LTc -> (string_comp a a'') = LTc.
Proof. Admitted.*)

Lemma hack_control_simpl: forall a e A c, configVAttSet ( (a, e) :: A ) c = 
       if semE e c then a :: (configVAttSet A c) else configVAttSet A c .
Proof. intros. simpl. reflexivity. Qed.

Lemma assumption_vatts : forall (v:vatts), (LocallySortedVAtts v)  /\ (NoDup v).
Proof. Admitted.

(** forall (a, e) ((a', e')::l), if a <= a', then a is less than (first element of) all components in l as 
l is a unique list of paired elements ordered on the first element of each pair *)
Definition globally_less : Prop :=
   forall (a: vatt) (vs:vatts), (string_comp (fst a) (fst (hd a vs)) = EQc 
                              \/ string_comp (fst a) (fst (hd a vs)) = LTc ->
     (forall (x:att), (exists e, In (x, e) (tail vs)) -> 
       string_comp (fst a) x = LTc)).

Lemma globally_less_is_true: globally_less = True.
Proof. Admitted.

Lemma config_filters_subset: forall vs c x xs, configVAttSet vs c = x :: xs 
 -> exists e, In (x, e) vs.
Proof. intros. induction vs as [| v vs]. 
       - simpl in H.  discriminate H. 
       - destruct v. simpl in H. destruct (E[[ f]] c) eqn: F.
         + inversion H. exists f. simpl. left. reflexivity.
         + simpl. apply IHvs in H. destruct H as [e H].
           exists e. right. assumption.
Qed. 

Lemma case1_req_global_lt_prop: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = EQc \/ (string_comp (fst v) (fst v')) = LTc -> 
  (forall c, (E[[(snd v)]] c) = true  /\ (E[[(snd v')]] c) = false ->
   atts_union (configVAttSet (v :: xs) c) (configVAttSet (v' :: xs') c) 
     = (fst v) :: atts_union (configVAttSet xs c) (configVAttSet xs' c) ).
Proof. 
      intros v v' xs xs' H0 c H1.
      assert (I: (LocallySortedVAtts (v'::xs')) /\ (NoDup (v'::xs'))). 
      { apply assumption_vatts. }
      destruct v as (a, e). destruct v' as (a',e'). 
      simpl in H0. simpl in H1. simpl. 
      destruct H1 as [H1 H2]. 
      rewrite H1. rewrite H2. destruct (configVAttSet xs' c) eqn: Imp. 
        + simpl. rewrite atts_union_nil_r. reflexivity.
        + assert (H: globally_less). { rewrite globally_less_is_true. auto. }
          unfold globally_less in H. specialize H with (vs:=((a',e')::xs')). 
          simpl in H.
          specialize H with (a:=(a,e)). 
          simpl in H. 
          simpl. specialize H with a0. 
          simpl in H. rewrite H. reflexivity. assumption. 
          apply config_filters_subset in Imp. assumption.   
Qed.

Lemma case2_req_global_lt_prop: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = EQc \/ (string_comp (fst v) (fst v')) = GTc -> 
  (forall c, (E[[(snd v)]] c) = false /\ (E[[(snd v')]] c) = true  ->
   atts_union (configVAttSet (v :: xs) c) (configVAttSet (v' :: xs') c) 
     = (fst v') :: atts_union (configVAttSet xs c) (configVAttSet xs' c) ).
Proof. 
      intros. rewrite atts_union_trans. assert (rev: atts_union (configVAttSet xs c)
     (configVAttSet xs' c) = atts_union (configVAttSet xs' c)
     (configVAttSet xs c)). { rewrite atts_union_trans. reflexivity. }
      rewrite rev. apply case1_req_global_lt_prop.
      - destruct H. 
      + left. apply string_comp_symm. assumption. 
      + right. rewrite string_comp_lt_gt. assumption.
      - rewrite and_comm. assumption.
Qed.

Lemma configVAttSet_dist_avatts_union : forall A  A' c, configVAttSet (avatts_union A A') c =
      atts_union (configVAttSet A c) (configVAttSet A' c) .
Proof. 
   intros A A' c. generalize dependent A'. induction A as [ | (a1, e1) ].
   - intro A'. rewrite avatts_union_nil_l. simpl. destruct (configVAttSet A' c).
     reflexivity. reflexivity.
   - intros. induction A' as [| (a2, e2)]. 
     + rewrite avatts_union_nil_r. rewrite atts_union_nil_r. 
       reflexivity. 
     + assert (I: forall a e A, configVAttSet ( (a, e) :: A ) c = 
       if semE e c then a :: (configVAttSet A c) else configVAttSet A c ).
       { intros. simpl. reflexivity. } (* rewrite I. rewrite I. *)
       destruct (E[[ e1]] c) eqn: E1. 
       ++ destruct (E[[ e2]] c) eqn: E2. 
          { rewrite I. rewrite I. rewrite E1. rewrite E2.
            destruct (string_comp a1 a2) eqn:SC.
            + simpl. rewrite SC. rewrite I. simpl. rewrite E1. simpl. 
              rewrite IHA. reflexivity.
            + simpl. rewrite SC. rewrite I. rewrite E1. 
              rewrite IHA. rewrite I. rewrite E2. reflexivity.
            + rewrite ackerman_resolve_vatts. 
                   rewrite ackerman_resolve_atts.
                   rewrite I. rewrite E2. rewrite IHA'.
                   rewrite I. rewrite E1. reflexivity.
                   assumption. simpl. assumption.
          }
          { destruct (string_comp a1 a2) eqn:SC.
            + rewrite case1_req_global_lt_prop. unfold avatts_union; fold avatts_union. 
              rewrite SC.  rewrite I. rewrite or_any_true. rewrite IHA.
              simpl. reflexivity.
              rewrite E1. reflexivity.
              simpl. left. assumption.
              simpl. split. assumption. assumption.
            + rewrite case1_req_global_lt_prop. simpl. rewrite SC. rewrite I. rewrite E1.
                rewrite IHA. rewrite I. rewrite E2. reflexivity.
                simpl. right. assumption.
                simpl. split. assumption. assumption.
            + rewrite ackerman_resolve_vatts. 
              rewrite I. rewrite E2. rewrite IHA'.
              rewrite I. rewrite E1.  rewrite I. rewrite E2. reflexivity.
              simpl. assumption.
          }
     ++ destruct (E[[ e2]] c) eqn: E2. 
          { destruct (string_comp a1 a2) eqn:SC.
            + rewrite case2_req_global_lt_prop. unfold avatts_union; fold avatts_union. 
              rewrite SC.  rewrite I. rewrite or_any_true. rewrite IHA.
              simpl. apply string_compEq_eq in SC. rewrite SC. reflexivity.
              rewrite E2. rewrite orb_comm. reflexivity.
              simpl. left. assumption.
              simpl. split. assumption. assumption.
            + simpl. rewrite SC. 
              rewrite E1. rewrite E2. rewrite I. rewrite E1. rewrite IHA. 
              rewrite I. rewrite E2. reflexivity.
            + rewrite case2_req_global_lt_prop. 
              rewrite ackerman_resolve_vatts. 
              rewrite I. rewrite E2.
              rewrite IHA'. rewrite I. rewrite E1. reflexivity.
              simpl. assumption.
              simpl. right. assumption. 
              simpl. split. assumption. assumption.
          }
          { rewrite I. rewrite I. rewrite E1. rewrite E2.
            destruct (string_comp a1 a2) eqn:SC.
            + simpl. rewrite SC. rewrite I. simpl. rewrite E1. rewrite E2. 
              simpl. apply IHA.
            + simpl. rewrite SC. rewrite I. rewrite E1. rewrite IHA. 
              rewrite I. rewrite E2. reflexivity.
            + rewrite ackerman_resolve_vatts. 
              rewrite I. rewrite E2. rewrite IHA'.
              rewrite I. rewrite E1. reflexivity.
             simpl. assumption.
          }
Qed.

Lemma configVQType_dist_avatts_union : forall A A' e c, configVQtype (avatts_union A A', e) c
= atts_union (configVQtype (A, e) c) (configVQtype (A', e) c).
Proof. 
 intros A A' e c. generalize dependent A'. induction A as [ | (a1, e1) ]. 
 - intro A'. destruct A' as [| (a2, e2)]. simpl. 
   + unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E.
     ++ reflexivity.
     ++ reflexivity. 
   + unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E.
     ++ rewrite atts_union_nil_l. reflexivity.
     ++ reflexivity. 
 - intro A'. destruct A' as [| (a2, e2)]. 
   + rewrite avatts_union_nil_r. 
     unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E. 
     rewrite atts_union_nil_r. reflexivity. reflexivity.
   + unfold configVQtype. unfold configVQtype in IHA. 
     destruct (E[[ e]] c) eqn: E. 
     ++ apply configVAttSet_dist_avatts_union. 
     ++ reflexivity.
Qed.


Lemma configVQType_recurse_anott : forall A e1 e2 c, 
configVQtype (recurse_annot A e1, e2) c
= configVQtype (A, e1 /\(F) e2) c.
Proof. intros. induction A. 
       - simpl. destruct (E[[ e2]] c); 
          destruct (E[[ e1]] c); simpl; repeat (reflexivity).
       - destruct a as (x, e). unfold recurse_annot; fold recurse_annot. 
         simpl. 
         simpl in IHA.
         destruct (E[[ e2]] c) eqn: E2.
          + destruct (E[[ e1]] c) eqn: E1; 
            destruct (E[[ e]] c) eqn: E; simpl; simpl in IHA;
              rewrite IHA; reflexivity. 
          + rewrite andb_false_r. reflexivity.
Qed.


Inductive vtype :fexp -> vquery -> vqtype -> Prop :=
  | Relation_vE_fm : forall e rn A e',
        ~ sat (  e'    /\(F)   (~(F) (e)) ) ->
       vtype e (rel_v (rn, (A, e'))) (A, e') (** variational context is initialized with feature_model which is more general than the overall pc of any relation in vdbms *)
  | Relation_vE : forall e rn A e',
       ~ sat (  e    /\(F)   (~(F) (e')) ) ->
       vtype e (rel_v (rn, (A, e'))) (A, e)
  | Project_vE: forall e vq e' A' A,
       vtype e vq (A', e') -> 
       subsump_vqtype (A, e) (A', e') ->
       vtype e (proj_v A vq) (A, e)
  (*| Select_vE: forall e S vq A e',
       vtype e S vq (A, e') ->
       vtype e S (sel_v c vq) (A, e'). *) 
  | SetOp_vE: forall e vq1 vq2 A1 e1 A2 e2 op,
       vtype e vq1 (A1, e1) ->
       vtype e vq2 (A2, e2) ->
       equiv_vqtype (A1, e1) (A2, e2) ->
       vtype e (setU_v op vq1 vq2) (A1, e1)
  | Choice_vE: forall e e' vq1 vq2 A1 e1 A2 e2,
       vtype (e /\(F) e') vq1 (A1, e1) ->
       vtype (e /\(F) (~(F) e')) vq2 (A2, e2) ->
       vtype e (chcQ e' vq1 vq2) 
        (avatts_union (recurse_annot A1 e1) (recurse_annot A2 e2) , e1 \/(F) e2).
            (*e1 and e2 can't be simultaneously true.*)
  (*| Product_vE: forall e vq1 vq2 A1 e1 A2 e2 ,
       vtype e  vq1 (A1, e1) ->
       vtype e  vq2 (A2, e2) ->
       avatts_inter (A1, e1) (A2, e2) = nil ->
       vtype e  (prod_v vq1 vq2) 
   (avatts_union (recurse_annot A1 (litB true)) (recurse_annot A2 (litB true)), (e1 /\(F) e2) ).
  *)

Fixpoint type1 (q:query) : qtype :=
 match q with
 | (rel (rn, A)) => A
 | (proj A q)    => let A' := type1 q in
                      if subsump_qtype_bool A A' then A else nil 
 | (setU op q1 q2) => if equiv_qtype_bool (type1 q1) (type1 q2) then type1 q1 else nil
 | _ => nil
 end.
 (*| (setU op q1 q2) => let A1 := type q1 in
                          let A2 := type q2 in
                              if equiv_atts A1 A2 && *)

(** Variation Preservation *)

Theorem context_type_rel : forall e vq A' e',
       vtype e vq (A', e') -> 
           ~ sat (  e' /\(F) (~(F) (e)) ).
Proof. intros e vq. generalize dependent e. induction vq. (* subst. *)
       - intros. inversion H; subst. assumption. rewrite not_sat_not_prop. 
          rewrite <- sat_taut_comp.
          intros. assumption.
       - intros. inversion H; subst.
       - intros. inversion H; subst.
         rewrite not_sat_not_prop. rewrite <- sat_taut_comp.
         intros. assumption.
       - intros. inversion H; subst. rewrite not_sat_not_prop. 
         unfold not_sat. intros.
         destruct (E[[ e1]] c) eqn:E1.
         + rewrite <- sat_taut_comp_inv_c. intros. simpl. 
         rewrite E1. simpl. 
         apply IHvq1 in H3.  rewrite not_sat_not_prop in H3. 
         rewrite <- sat_taut_comp in H3. specialize H3 with c.
         apply H3 in E1. simpl in E1. apply andb_prop in E1. 
         destruct E1. rewrite <- H1, H0. reflexivity.
         + rewrite <- sat_taut_comp_inv_c. intros. simpl.
         rewrite E1. simpl.
         apply IHvq2 in H7.  rewrite not_sat_not_prop in H7. 
         rewrite <- sat_taut_comp_inv in H7. specialize H7 with c.
         apply H7. simpl. rewrite H0. simpl. reflexivity.
Admitted.
 (** (E[[ e']] c) = true -> (E[[ e]] c) = true.*)


(* @Fariba: I didn't go over this, I cannot even compile it yet and I don't have time to get into it this week.
you need to prove variationa preserving for typing relation of conditions to be able to prove variation 
preserving for the selection case. *)
(* @Fariba: the empty context must be schema's presence condition. that's another reason why you 
need to pass the schema to the typing relation. *)
Theorem variation_preservation : forall e vq T, 
       vtype e vq T ->
       forall c, (E[[e]] c) = true ->
           type1 (configVQuery vq c) = configVQtype T c.
Proof. 
  intros. induction H.
  (* Relation - E *) (*get rid of this*)
  - unfold configVQuery. unfold configVRelS. simpl. 
    rewrite not_sat_not_prop in H. rewrite <- sat_taut_comp in H. 
    unfold configVQtype. simpl. destruct (E[[e']] c) eqn: HsemE.
    + reflexivity.
    + reflexivity. 
  (* Relation - E *)
  - unfold configVQuery. unfold configVRelS. unfold configVQtype. simpl. 
    rewrite not_sat_not_prop in H. rewrite <- sat_taut_comp in H. 
    rewrite H0. apply H in H0. rewrite H0. reflexivity.
 (* Project - E *)
 - unfold subsump_vqtype, configVQtype in H1. simpl in H1.
   unfold configVQtype in IHvtype. simpl in IHvtype. 
   unfold configVQtype. simpl. 
   destruct (E[[ e']] c) eqn: He'.
     ++ rewrite IHvtype. simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. rewrite H1. rewrite H0. 
        reflexivity. assumption.
     ++ rewrite IHvtype. simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (configVAttSet A c). rewrite H0.
        reflexivity. simpl in H1. discriminate H1. assumption.
 (* SetOp - E *)
 - simpl in IHvtype1. simpl in IHvtype2. simpl. 
   + simpl. rewrite IHvtype1. rewrite IHvtype2.
     unfold configVQtype. simpl. 
     destruct H2. simpl in H2. simpl in H3. unfold equiv_vatts in H2.
     unfold equivE in H3. rewrite H2. rewrite H3. destruct (E[[ e2]] c) eqn: E'.
     ++ rewrite (equiv_qtype_bool_refl (configVAttSet A2 c)). reflexivity.
     ++ simpl. reflexivity. 
     ++ assumption. ++ assumption.
 (* Choice - E *)
 - simpl in IHvtype1. simpl in IHvtype2. rewrite H0 in IHvtype1, IHvtype2.
   rewrite configVQType_dist_avatts_union.
   rewrite configVQType_recurse_anott. rewrite configVQType_recurse_anott. 
   destruct (E[[ e']] c) eqn: E'.
   + simpl. rewrite E'. apply context_type_rel in H1.
     rewrite not_sat_not_prop in H1. 
     rewrite <- sat_taut_comp_inv in H1.
     specialize H1 with c. 
     simpl in H1. rewrite H0, E' in H1. simpl in H1. 
     rewrite H1.
     simpl. rewrite atts_union_nil_r. 
     simpl. rewrite orb_false_r. rewrite andb_diag.
     apply IHvtype1. reflexivity. reflexivity.
   + apply context_type_rel in H.
     rewrite not_sat_not_prop in H. 
     rewrite <- sat_taut_comp_inv in H.
     specialize H with c. 
     simpl in H. rewrite H0, E' in H. simpl in H. 
     unfold configVQtype at 1. 
     assert(Ihack2: forall e1 e2, (E[[  e1 /\(F) (e1 \/(F) e2)]] c) = (E[[ e1]] c)).
     { simpl. Search andb. intros. apply absorption_andb. }
     rewrite Ihack2. rewrite H. rewrite atts_union_nil_l.  
     unfold configVQuery. rewrite E'. fold configVQuery.
     destruct (configVQtype (A2, e2 /\(F) (e1 \/(F) e2)) c) eqn: D;
     unfold configVQtype in D; simpl in D; rewrite H in D;
     try (simpl in D); try (rewrite andb_diag in D);
     try (unfold configVQtype in IHvtype2); try (simpl in IHvtype2);
     try (rewrite D in IHvtype2);
     try (apply IHvtype2); repeat (reflexivity). reflexivity.
  (* Product - E *)
  (* Select - E *)
Qed.



(*Lemma configVAttSet_dist_avatts_union_v1 : forall A c, (forall A' , configVAttSet (avatts_union A A') c =
      atts_union (configVAttSet A c)
        (configVAttSet A' c) )  -> forall a1 e1 A', configVAttSet
        (avatts_union ((a1, e1) :: A) ( A')) c =
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

(*Fixpoint avatts_union (A A': vatts) : vatts := 
  match A, A' with
  | nil, _ => A'
  | _, nil => A
  | cons (a, e) xs, cons (a', e') xs' =>
          match (string_comp a a') with
          | 0 => cons (a, e \/(F) e') (avatts_union xs xs')
          | S 0 => cons (a', e') (avatts_union (cons (a, e) xs) xs')
          | S (S 0) => cons (a, e) (avatts_union xs (cons (a', e') xs'))
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
          rewrite configVQType_dist_avatts_union.
          rewrite configVQType_recurse_anott. rewrite configVQType_recurse_anott.
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
              
