(** Variational relational algebra *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
(*Require Import Maps.*)
Require Export List.
(*Require Export Arith.
Require Export String.*)
Require Export Logic.
Require Import Coq.Strings.String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Sorting.Sorted.

Import Coq.Lists.List.ListNotations.

Load Feature.
Import Feature.

Module VRA_RA_encoding.

Module SSet := FSetAVL.Make String_as_OT.

Definition v : Type := SSet.t.

Check LocallySorted.

Check String_as_OT.compare.

Locate string_dec.

Definition s1 : list string := nil. 

(** -------------------------------------------------------------
  Attribute: Type and Comparison Function, Lemmas
-----------------------------------------------------------------*)
(* Plain Attribute *)
Definition att : Type := string.

Inductive comp : Type := 
  | EQc | LTc | GTc.

(* Variational Attribute *)
Definition vatt : Type := (att * fexp)%type. (*assuming always annotated; could've used option*)

(*Inductive vatt' : Type :=
   | P: string -> fexp -> vatt'. *)

Definition vfeqb (v v' : vatt) := String.eqb (fst v) (fst v').

Definition veqb (v v' : vatt) := String.eqb (fst v) (fst v') && eqb (snd v) (snd v').

(*Scheme Equality for vatt'. Print vatt'_beq. Print fexp_beq. Print string_beq. *)



Lemma veqb_refl: forall (a:vatt), veqb a a = true.
Proof. destruct a. unfold veqb. simpl. rewrite String.eqb_refl.
rewrite eqb_refl. reflexivity. Qed.

(*Definition s : string := "ba".
Definition s' : string := "ab". 
Compute (veqb (s, e) (s, e)).*)

Locate eqb_string.

(** Attribute (string-)comparison function and associated lemmas *)

(* String_as_OT.compare *)

(** -----------------------att vatt-------------------------- **)


(** ------------------------------------------------------------
  Attribute List
---------------------------------------------------------------*)

(* Plain Attribute List *)
Definition atts : Type := list att.

(*------------------------------------------------------------------------*)

(* Variational Attribute List *)
Definition vatts : Type := list vatt.

Fixpoint findIfExists (a : att) (v:vatts) : option fexp := 
   match v with
   | []           => None
   | (x, e) :: xs => 
       match (String.eqb a x) with
       | true  => Some e
       | false => findIfExists a xs
       end
   end.
(*-------------------------------------------------------------------------------*)

(*-------------------------------------------------------------------------------*)
(** Remove replace with List.remove *)

(* it's bag remove but once *)
Fixpoint remove {X:Type} (f:X->X->bool) (a : X) (A : list X) : list X :=
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

Admitted.
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
Proof. intros e c. simpl. destruct (E[[ e]] c); reflexivity. Qed.
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
                   | cons x' xs' => if String.eqb x x' then sublist xs xs'
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
                   | cons x' xs' => String.eqb x x' && equiv_qtype_bool xs xs'
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
  + simpl. rewrite String.eqb_refl. simpl. apply IHA.
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
(** Union *)
(* Plain Attr List *)
Fixpoint atts_union_c (A A': atts) : atts :=
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
     vatts_union (push_annot (fst Q) (snd Q)) (push_annot (fst Q') (snd Q')).
(*------------------------------------------------------------------------------*)
(** Intersection *)
(* Plain Attr List *)
Fixpoint atts_inter (A A': atts) : atts :=
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

Lemma atts_union_nil_r: forall A, atts_union A [] = A.
Proof. intro A. induction A as [|a A IHA]. auto. 
simpl. rewrite IHA. reflexivity. Qed.

Lemma atts_union_nil_l: forall A, atts_union [] A = A.
Proof. auto. Qed.

Lemma atts_inter_nil_r: forall A, atts_inter A [] = [].
Proof. intro A. induction A. auto. simpl. assumption. Qed.

Lemma atts_inter_nil_l: forall A, atts_inter [] A = [].
Proof. auto. Qed.

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

Lemma vatts_union_nil_r : forall A, vatts_union A [] = A.
Proof. intro A. induction A as [|a A IHA]. auto. 
destruct a as (a,e). simpl. rewrite IHA. reflexivity. Qed.

Lemma vatts_union_nil_l : forall A, vatts_union [] A = A.
Proof. auto. Qed.

Lemma vatts_inter_nil_r : forall A, vatts_inter A [] = [].
Proof. intro A. induction A as [|(a, e)]. reflexivity. simpl. 
       assumption. Qed.

Lemma vatts_inter_nil_l : forall A, vatts_inter [] A = [].
Proof. auto. Qed.


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

