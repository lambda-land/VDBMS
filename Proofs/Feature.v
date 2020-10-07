(* Feature *)
Set Warnings "-notation-overridden,-parsing".
Require Import Bool.
Require Import String.
Require Import Coq.Strings.String.
Require Import Relations.Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Setoids.Setoid.
Require Import Logic.Classical_Pred_Type.

Module Feature.

(** Feature Exression Generic Object *)

Definition fname := string.

(** Feature Exression Syntax. *)
(* comp is negation. meet is conjunction. join is disjunction.*)
Inductive fexp : Type :=
  | litB : bool -> fexp
  | litF : fname -> fexp
  | comp : fexp -> fexp
  | meet : fexp -> fexp -> fexp
  | join : fexp -> fexp -> fexp.

Notation "~(F) f" := (comp f) (at level 75, right associativity).
Infix "/\(F)" := meet (at level 80, right associativity).
Infix "\/(F)" := join (at level 85, right associativity).


(** Configurations. *)
Definition config := fname -> bool.

(** Feature Exression Semantics. *)

Fixpoint semE (e : fexp) (c : config) : bool :=
  match e with
  | litB b   => b
  | litF f   => c f
  | ~(F) e      => negb (semE e c)
  | e1 \/(F) e2 => (semE e1 c) || (semE e2 c)
  | e1 /\(F) e2 => (semE e1 c) && (semE e2 c)
  end.

Notation "E[[ e ]] c" := (semE e c) (at level 90, left associativity).

(** Feature Expression Equality - see above *)
(*Fixpoint eqb (e1 e2: fexp) : bool :=
  match e1, e2 with
  | litB b, litB c => Bool.eqb b c 
  | litF f, litF g => String.eqb f g
  | ~(F) e1', ~(F) e2' => eqb e1' e2'
  | e1' \/(F) e1'', e2' \/(F) e2'' => eqb e1' e2' && eqb e1'' e2''
  | e1' /\(F) e1'', e2' /\(F) e2'' => eqb e1' e2' && eqb e1'' e2''
  | _, _ => false
  end.

Notation "=?" := eqb (at level 95) : type_scope.

Lemma eqb_refl: forall e, eqb e e = true.
Proof. intro e. induction e. 
       - simpl. destruct b; reflexivity.
       - simpl. induction f as [| a f IHf]. reflexivity. simpl.
         rewrite Ascii.eqb_refl. apply IHf.
       - simpl. assumption.
       - simpl. rewrite IHe1, IHe2. reflexivity.
       - simpl. rewrite IHe1, IHe2. reflexivity.
Qed.*)

(** Feature Expression Equivalemce *)
Definition equivE : relation fexp :=
  fun e e' => forall c, (semE e c) = (semE e' c).

Infix "=e=" := equivE (at level 70) : type_scope.

(** Feature Equivalence is an Equivalence *)

(** Feature equivalence is reflexive. *)
(* e \equiv e *)
Remark equivE_refl : Reflexive equivE.
Proof.
  intros x c.
  reflexivity.
Qed.

(** Feature equivalence is symmetric. *)
(* e \equiv e' --> e' \equiv e *)
Remark equivE_sym : Symmetric equivE.
Proof.
  intros x y H c.
  symmetry.
  apply H.
Qed.

(** Feature equivalence is transitive. *)
(* e \equiv e' and e' \equiv e'' --> e \equiv e'' *)
Remark equivE_trans : Transitive equivE.
Proof.
  intros x y z H1 H2 c.
  transitivity (semE y c).
    apply H1.
    apply H2.
Qed.

(** Feature equivalence is an equivalence relation. *)
Instance eqE : Equivalence equivE.
Proof.
  split.
    apply equivE_refl.
    apply equivE_sym.
    apply equivE_trans.
Qed.

(** Function over feature expression *)

Definition sat (e:fexp): Prop :=
  exists c, semE e c = true.

Definition taut (e:fexp): Prop :=
  forall c, semE e c = true.

(* lemma not_sat_not_prop relates sat and not_sat with each other.*)
Definition not_sat (e:fexp): Prop :=
  forall c, semE e c = false.

(* @Fariba: not sure what you mean by implies and if you're defining it correctly. *)
(* @Parisa: never used it anywhre; not sure why I wrote this in the first place!! *)
Definition implies (e1 e2:fexp) (c:config): Prop :=
  semE e1 c = true -> semE e2 c = true.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.
 
Theorem dist_not_exists : forall (X:Type) (Q : X -> Prop),
  (forall x, ~Q x) <-> ~(exists x, Q x).
Proof. 
  intros. split. 
  - apply all_not_not_ex.
  - apply not_ex_all_not.
Qed.

Lemma not_sat_not_prop : forall e, (~ sat e) <-> not_sat e.
Proof. 
 split. 
 - unfold sat, not_sat. intros. 
   rewrite <- dist_not_exists in H. 
   specialize H with c. rewrite not_true_iff_false in H. 
   assumption. 
 - unfold sat, not_sat. intros. rewrite <- dist_not_exists. intros. 
   rewrite not_true_iff_false. apply H.
Qed.

(* not_sat (e1 /\(F) ~(F)e2) is saying that e2 is a subset of e1, i.e., e2 is more specific than e1. *)
Theorem sat_taut_comp : forall e1 e2, 
           (forall c, semE e1 c = true -> semE e2 c = true) 
                  <-> not_sat (e1 /\(F) ~(F)e2).
Proof. 
  split.
  + intros. unfold not_sat. intros. 
    simpl. destruct (E[[ e1]] c) eqn: E.
    ++ apply H in E. rewrite E. simpl. reflexivity.
    ++ reflexivity.
  + intros. unfold not_sat in H. simpl in H. 
    specialize H with c.  rewrite H0 in H. simpl in H. 
    symmetry in H. apply negb_sym in H. simpl in H. 
    assumption.
Qed.

Theorem sat_taut_comp_inv : forall e1 e2, 
           (forall c, semE e2 c = false -> semE e1 c = false) 
                  <-> not_sat (e1 /\(F) ~(F)e2).
Proof.
 split.
  + intros. unfold not_sat. intros. 
    simpl. destruct (E[[ e2]] c) eqn: E.
    ++ simpl. apply andb_false_r.
    ++ apply H in E. rewrite E. simpl. reflexivity.
  + intros. unfold not_sat in H. simpl in H. 
    specialize H with c.  rewrite H0 in H. simpl in H. 
    apply andb_false_iff in H. destruct H.  
    assumption. discriminate H.
  Qed.

Lemma sat_taut_comp_inv_c : forall e1 e2 c, 
           (semE e2 c = false -> semE e1 c = false)
                  <-> (E[[ e1 /\(F) ~(F) e2]] c) = false.
Proof.
 split.
  + intros. 
    simpl. destruct (E[[ e2]] c) eqn: E.
    ++ simpl. apply andb_false_r.
    ++ simpl. rewrite andb_true_r. apply H. reflexivity.
  + intros. simpl in H. 
   rewrite H0 in H. simpl in H. 
    rewrite andb_true_r in H. 
    assumption.
  Qed.


Lemma or_any_true : forall e1 e2 c, 
         ((E[[ e1]] c) || (E[[ e2]] c)) = true
            -> (E[[ e1 \/(F) e2]] c) = true.
Proof. intros. simpl. assumption. Qed.

Lemma or_both_false : forall e1 e2 c, 
         ((E[[ e1]] c) && (E[[ e2]] c)) = false
            -> (E[[ e1 /\(F) e2]] c) = false.
Proof. intros. simpl. assumption. Qed.
    
Example sat_or: sat (litB true \/(F) litB false).
Proof. intros. unfold sat. exists (fun _ => true). 
simpl. reflexivity. Qed.

Example taut_or: taut (litB true \/(F) litB false).
Proof. intros. unfold taut. 
intros. simpl. reflexivity. Qed.

End Feature.
