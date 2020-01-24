(** Variational relational algebra *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
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

(** variational to non-variational condiitions configurations *)

Inductive op : Type :=
  | eq | GTE | LTE | GT | LT | neq.

(*assumption: attributes' domain is nat. *)
(* meet is and. join is or. *)
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
  | setU  : setop   -> query   -> query -> query.

Definition vatt : Type := (att * fexp)%type. (*assuming always annotated; could've used option*)
                                              (*| AnnotAtt : att -> option fexp -> vatt.*)

(* @Fariba: what is this lemma saying? *)
Lemma vatt_dec : forall s1 s2 : vatt, {s1 = s2} + {s1 <> s2}.
Proof. Admitted.

Definition vatts : Type := list vatt.

(** variational attribute list from queries are explicitly typed. 
Assuming variational attribute list from schema are also explicitly typed.
Thus not looking up pc(rel(a)) *)

(** A[[.]]_c *)
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
  | setU_v  : setop    -> vquery   -> vquery -> vquery.

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

Definition configVQtype (vqt : vqtype) (c : config) : qtype := if semE (snd vqt) c
                                                         then  configVAttSet (fst vqt) c
                                                           else  nil.
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

(* vatts^fexp *)
Fixpoint annot_dist_helper (v : vatts) (e: fexp) : vatts := 
 match v with
 | nil => nil
 | cons (a, e') vas  =>
     cons (a, e' /\(F) e) (annot_dist_helper vas e)
 end.

Definition annot_dist ( X : (vatts * fexp)) : vatts := annot_dist_helper (fst X) (snd X).

(* @Fariba: I'm assuming that this isn't completed yet. *)
Definition avatts_union (A A': (vatts * fexp)) : vatts := nil.

(* @Fariba: I'm assuming that this isn't completed yet. *)
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

Definition subsump_vatts ( X X': vatts ) : Prop := forall a e1, In (a, e1) X -> 
exists e1', (In (a, e1') X' /\ ~ sat ( (e1 /\(F) (~(F) e1') ) ) ).

Definition subsump_vqtype ( X X': vqtype ) : Prop := subsump_vatts (fst X) (fst X')
/\ ~ sat ( (snd X) /\(F) (~(F) (snd X')) ).

Definition subsump ( X X': qtype ) : Prop := forall a, In a X -> In a X'.

Fixpoint subsump_qtype_bool (A A': qtype) : bool :=
   match A with
   | nil       => true
   | cons x xs => if findx x A' then subsump_qtype_bool xs A' 
                                 else false
   end.

Definition subsump_qtype ( A A': qtype ) : Prop := forall a, In a A -> In a A'.

Lemma subsump_prop_bool: forall A A', subsump_qtype A A' -> subsump_qtype_bool A A' = true.
Proof.
  intros. unfold subsump_qtype in H. unfold subsump_qtype_bool. 
  (*unfold equiv_qtype_union. destruct (A++A').
  + reflexivity. 
  + specialize H with a. rewrite (In_findx_iff) in H. *)
    
Admitted.

(* @Fariba: shouldn't forall c be moved to the right hand side of -> ? *)
Lemma subsump_vq_to_q : forall X X' c, subsump_vqtype X X' -> 
                   (*~( exists c, ((E[[snd X]] c) &&  (negb (E[[snd X']] c)) ) = true )*)
                   ( (E[[snd X]] c) = true -> (E[[snd X']] c) = true )
                   /\ subsump_qtype_bool (configVQtype X c) (configVQtype X' c) = true.
Proof.
  intros. unfold subsump_vqtype in H. destruct H as [H1 H2]. 
  rewrite not_sat_not_prop in H2. rewrite <- sat_taut_comp in H2. 
  split. 
  - apply H2.
  - apply subsump_prop_bool. unfold subsump_qtype. unfold subsump_vatts in H1. 
    unfold configVQtype. destruct (E[[ snd X]] c) eqn: H.
    + apply H2 in H. rewrite H. intros. 
      rewrite <- config_det_plain in H0. 
      destruct H0 as [e He]. destruct He as [He1 He2]. 
      apply H1 in He1. destruct He1 as [e1 He1]. 
      destruct He1 as [He11 He12].
      rewrite not_sat_not_prop in He12. rewrite <- sat_taut_comp in He12.
      apply He12 in He2. 
      assert (He112: exists e, In (a, e) (fst X') /\ (E[[ e]] c) = true). 
         { exists e1. split. apply He11. apply He2. }
      rewrite (config_det_plain (fst X') a c) in He112. assumption.
    + intros. simpl in H0. destruct H0.
Qed.

Definition atts_union (A A': atts) : atts := A ++ A'.

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

(* qtype1 = qtype1 *)
Theorem equiv_qtype_bool_refl: forall A, equiv_qtype_bool A A = true.
Proof.
  intros. induction A. 
  + reflexivity. 
  + simpl. rewrite <- eqb_string_refl. simpl. apply IHA.
Qed.

Definition equiv_qtype ( A A': qtype ) : Prop := A = A'.

Lemma or_dist_implies: forall (X: Type) (P Q R: X -> Prop), 
       (forall a, ( P a \/ Q a -> R a)) <-> (forall a, (P a-> R a)/\(Q a-> R a) ).
Proof.
Admitted.

(* @Fariba: shouldn't this be two sided, i.e., instead of -> shouldn't it be <_> ? *)
Theorem equiv_prop_bool: forall A A', equiv_qtype A A' -> equiv_qtype_bool A A' = true.
Proof.
 (*intros. unfold equiv_qtype in H. unfold equiv_qtype_bool. 

 (* induction A.
  + destruct A'. 
    ++ reflexivity. 
    ++ specialize H with a. simpl in H. 
       apply ex_falso_quodlibet. *)
  induction (A++A').
  + reflexivity. 
  + simpl. 
    ++ destruct (findx a A) eqn: Ha.
       +++ destruct (findx a A') eqn: Ha'.
           ++++ simpl. apply IHl. *)
Admitted.
(*
    simpl in H. 
    rewrite or_dist_implies in H. destruct H. 
    assert (I: a=a). { reflexivity. } apply H in I.
    destruct I as [I1 I2]. rewrite (In_findx_iff) in I1.
    rewrite (In_findx_iff) in I2. rewrite I1, I2. simpl.
    apply IHl.
  
Admitted.*)
Search Set.
Inductive Empty_set : Set := .

(* @Fariba: shouldn't forall c be on the right hand side of implication? *)
(* @Fariba: also shouldn't be <-> instead of _> ? *)
Theorem equiv_vq_to_q : forall X X' c, equiv_vqtype X X' -> 
                   (E[[ snd X ]] c) = (E[[ snd X']] c)
                   /\ equiv_qtype_bool (configVQtype X c) (configVQtype X' c) = true.
Proof.
  (*intros. unfold equiv_vqtype in H. destruct H as [H1 H2]. 
  unfold equivE in H2. split. apply H2.
  apply equiv_prop_bool. unfold equiv_qtype. unfold equiv_vatts in H1. unfold configVQtype.
  destruct (E[[ snd X]] c) eqn: H.
  + rewrite <- H2. rewrite H. intros. 
    rewrite configVAttSet_app_dist in H0.  rewrite <- config_det_plain in H0. 
    destruct H0 as [e He]. destruct He.
    apply H1 in H0. unfold equivE in H0. destruct H0 as [e1 H0]. destruct H0 as [e2 H0].
    destruct H0. destruct H4. destruct H5.
    destruct (E[[ e1]] c) eqn: E. 
    ++ assert (H0E: exists e, In (a, e) (fst X) /\ (E[[ e]] c) = true). 
       { exists e1. split. apply H0. apply E. }
       rewrite (config_det_plain (fst X) a c) in H0E.
       assert (H4E: exists e, In (a, e) (fst X') /\ (E[[ e]] c) = true). 
       { exists e2. split. apply H4. rewrite <- H5. apply E. }
       rewrite (config_det_plain (fst X') a c) in H4E. 
       split. assumption. assumption. 
    ++ specialize H6 with c. rewrite H3 in H6. rewrite E in H6. discriminate H6.
  + rewrite H2 in H. rewrite H. simpl. intros. destruct H0.*)
Admitted.

Inductive vtype :fexp -> vquery -> vqtype -> Prop :=
  | Relation_vE_empty : forall rn A e',
       vtype (litB true) (rel_v (rn, (A, e'))) (A, e')
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
       vtype e (chcQ e' vq1 vq2) (avatts_union (A1, e1) (A2, e2) , (e1 \/(F) e2) )
  | Product_vE: forall e vq1 vq2 A1 e1 A2 e2 ,
       vtype e  vq1 (A1, e1) ->
       vtype e  vq2 (A2, e2) ->
       avatts_inter (A1, e1) (A2, e2) = nil ->
       vtype e  (prod_v vq1 vq2) (avatts_union (A1, litB true) (A2, litB true) , (e1 /\(F) e2) ).

(* @Fariba: this must take schema as input. I understand that you can write the typing rule
withou passing the schema and that's because instead of referring to a relation name in the query
language that you've defined you're referring to the relation name and its schema. I'm not sure how 
I feel about this since it's getting further away from our written draft. *)
(* @Fariba: you need to have a typing relation for conditions to be able to write the select_E rule. *)
Inductive type : query -> qtype -> Prop :=
  | Relation_E : forall rn A,
       type (rel (rn, A)) A
  | Project_E: forall q A' A,
       type q A'  -> 
       subsump A A' ->
       type (proj A q) A
  (*| Select_E: forall e S vq A e',
       vtype e S vq (A, e') ->
       vtype e S (sel_v c vq) (A, e'). *) 
  | SetOp_E: forall q1 q2 A1 A2 op,
       type q1 A1 ->
       type q2 A2 ->
       equiv A1 A2  ->
       type (setU op q1 q2) A1
  | Product_E: forall q1 q2 A1 A2,
       type q1 A1 ->
       type q2 A2 ->
       atts_inter A1 A2 = nil ->
       type (prod q1 q2) (atts_union A1 A2).

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

(* @Fariba: just as a reminder. the initial context will be the schema presence condition. *)
Definition empty_context := litB true.
(** Variation Preservation*)

(* @Fariba: I didn't go over this, I cannot even compile it yet and I don't have time to get into it this week.
you need to prove variationa preserving for typing relation of conditions to be able to prove variation 
preserving for the selection case. *)
Theorem variation_preservation : forall vq T, 
       vtype (empty_context) vq T ->
       forall c, type1 (configVQuery vq c) = configVQtype T c.
Proof. intros. remember (empty_context) as e. induction H. 
  - unfold configVQuery. unfold configVRelS. simpl. 
    destruct (E[[e']] c) eqn: HsemE;
      unfold configVQtype; simpl; rewrite HsemE;
      reflexivity.
  - unfold configVQuery. unfold configVRelS. simpl.  
    destruct (E[[e']] c) eqn: HsemE'.
    + unfold configVQtype. rewrite Heqe. simpl. reflexivity.
    + unfold sat in H. simpl in H. unfold not in H. apply ex_falso_quodlibet. 
      apply H. exists c. rewrite HsemE'. rewrite Heqe. simpl. reflexivity.
   (* destruct (E[[e']] c) eqn: HsemE. admit.
    + unfold configVQtype. simpl. 
      reflexivity.
    + unfold configVQtype. simpl. unfold sat in H0.
      simpl in H0. unfold not in  H0. apply ex_falso_quodlibet. 
      apply H0. exists c. rewrite HsemE. simpl. reflexivity. *)
 - simpl. apply ( subsump_vq_to_q _ _ c) in H0. unfold configVQtype in H0.
   simpl in H0. destruct H0. assert (He: (E[[ e]] c) = true). { rewrite Heqe. reflexivity. }
   apply H0 in He as He'. rewrite He, He' in H1. rewrite IHvtype. unfold configVQtype.
   simpl. rewrite He, He'. rewrite H1. reflexivity. apply Heqe.
 - simpl. rewrite IHvtype1. rewrite IHvtype2. unfold configVQtype. simpl. 
   destruct H1. simpl in H1. simpl in H2. unfold equiv_vatts in H1.
   unfold equivE in H2. rewrite H1. rewrite H2. destruct (E[[ e2]] c) eqn: E.
   + rewrite (equiv_qtype_bool_refl (configVAttSet A2 c)). reflexivity.
   + simpl. reflexivity.
Admitted.
