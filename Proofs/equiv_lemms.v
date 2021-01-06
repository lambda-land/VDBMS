(** Equivalence lemmas *)
Set Warnings "-notation-overridden,-parsing".

Load VRA_RA_encoding.
Import VRA_RA_encoding.



Lemma eq_equiv_atts: forall A A', A = A' -> A =a= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma eq_equiv_vatts: forall A A', A = A' -> A =va= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma eq_equiv_vqtype: forall A A', A = A' -> A =T= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma cons_equiv_atts: forall a l1 l2, l1 =a= l2 -> (a::l1) =a= (a::l2).
Proof. 
intros. 
unfold equiv_atts in H.

unfold equiv_atts. 
intros. split;
specialize H with (a:=a0);
destruct H.

+ simpl. split; intro H1;
   destruct H1;
   eauto; right; 
   try (rewrite <- H); auto; try (rewrite H); auto.
+ simpl. destruct (string_eq_dec a a0);
  rewrite H0; auto.

Qed.

Lemma cons_equiv_vatts: forall a l1 l2, l1 =va= l2 -> (a::l1) =va= (a::l2).
Proof. 
intros. 
unfold equiv_vatts in H. 
unfold equiv_atts in H.
unfold equiv_vatts.
intro c. 
unfold equiv_atts. 
intros. split;
specialize H with (c:=c) (a:=a0);
destruct H; destruct a as (a, e);
simpl; destruct (E[[ e]] c).

+ simpl. split; intro H1;
   destruct H1;
   eauto; right; 
   try (rewrite <- H); auto; try (rewrite H); auto.
+ auto.

+ simpl. destruct (string_eq_dec a a0);
  rewrite H0; auto.
+ rewrite H0; auto.
Qed.

Lemma equiv_irres_order x y l: (x::y::l) =a= (y::x::l).
Proof. unfold equiv_atts. intro. split. split;
try (intro H; simpl in H; simpl;
destruct H; eauto; try (destruct H); eauto).
simpl. destruct (string_eq_dec x a);
destruct (string_eq_dec y a); reflexivity.
Qed.



Lemma NoDup_equiv_atts l l': l =a= l' -> 
    (NoDup l <-> NoDup l').
Proof. intro H. split;
intro H1; unfold equiv_atts in H;
apply forall_dist_and in H; destruct H as [H H0];
rewrite (NoDup_count_occ string_eq_dec) in H1;
rewrite (NoDup_count_occ string_eq_dec); intro x;
specialize H0 with x; try (rewrite <- H0; apply H1); 
try (rewrite H0; apply H1). Qed.



(*Lemma removeAtt_equiv a A A':
A =va= A' -> removeAtt a A =va= removeAtt a A'.
Proof. 
unfold equiv_vatts.
simpl. unfold equiv_atts. intros.
specialize H with c a0. destruct H as [H H0].
split. 
+ split; intro H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e0 H1]; destruct H1 as [H1 H2];
  destruct (string_eq_dec a0 a) as [Heqdec | Heqdec];
  (* a0 = a *)
  try (rewrite Heqdec in H1; apply notIn_removeAtt in H1; destruct H1);
  (* a0 <> a *)
  try (apply In_removeAtt in H1; apply In_config_true with (c:=c) in H1;
  auto; apply H in H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e1 H1]; destruct H1 as [H1 H1e1];
  rewrite <- In_config_exists_true; exists e1;
  split; try (apply In_removeAtt; eauto); try(eauto)).
  
+ destruct (string_eq_dec a a0) as [eq | neq].
  rewrite eq. rewrite count_occ_config_removeAtt_eq.
  reflexivity.
  repeat (rewrite (count_occ_config_removeAtt_neq _ _ neq)).
  assumption.
Qed.*)

Lemma equiv_sublist: forall A B B' , 
     B =a= B' -> sublist A B <-> sublist A B'.
Proof. 
intros. unfold equiv_atts in H. unfold sublist.
split; intro H1;
intro x; specialize H with x;
destruct H;  
[rewrite <- H  | rewrite H]; 
[rewrite <- H0 | rewrite H0];
apply H1.
Qed.


Lemma nil_equiv_eq: forall A, A =a= [] -> 
A = []. intros. unfold equiv_atts in H. 
simpl in H.
apply (count_occ_inv_nil string_eq_dec).
intro x. specialize H with x. destruct H.
exact H0. Qed.

Lemma cons_equiv_neq: forall x l A, A =a= (x::l) -> 
A <> []. 
Proof. intros. unfold equiv_atts in H. 
assert (H1: exists a, count_occ string_eq_dec (x :: l) a <> 0).
exists x. simpl. 
destruct (string_eq_dec x x) as [Heq|Heq]; subst.
+ apply Nat.neq_succ_0. 
+ destruct Heq. reflexivity. 
+ destruct H1 as [a H1].
  unfold not in H1. unfold not. intro H2.
  apply H1. specialize H with a. rewrite H2 
  in H. destruct H. simpl in H0. rewrite H0.
  reflexivity. 
Qed.

Lemma configVQtype_equiv: forall Q Q' c, Q =T= Q' ->
(QT[[ Q]] c) =a= (QT[[ Q']] c).
Proof. intros. unfold "=T=" in H. apply H.
(* unfold configVQtype, configaVatts. unfold equiv_vqtype in H.
destruct H. destruct Q as (A, e). destruct Q' as (A', e').
simpl in *. rewrite H0. destruct (E[[ e']] c).
apply H. reflexivity.*)
Qed.

Lemma configaVatts_equivE_configVQtype: forall Q Q', (fst Q) =va= (fst Q') ->
(snd Q) =e= (snd Q') -> Q =T= Q'. 
Proof. intros. 
unfold "=va=" in H. 
destruct Q as (A, e). destruct Q' as (A', e').
simpl in *. unfold "=T=". intro c. simpl.
rewrite H0. 
destruct (E[[ e']] c).
apply H. reflexivity.
Qed.

Lemma configVAttSet_push_annot A e c:
configVAttSet (push_annot A e) c = configVQtype (A, e) c.
Proof. induction A. 
simpl. destruct ( E[[ e]] c); reflexivity.
unfold push_annot; fold push_annot.
destruct a. simpl configVQtype. 
simpl configVQtype in IHA.
simpl configVAttSet.
destruct (E[[ e]] c); destruct (E[[ f]] c); simpl;
try(eauto).
rewrite IHA. reflexivity.
Qed.

Lemma push_annot_equiv A B e: A =va= B -> (A < e) =va= (B < e).
Proof. intro H. unfold "=va=". intro c.
repeat(rewrite configVAttSet_push_annot).
simpl. destruct (E[[ e]] c). apply H. reflexivity.
(*apply configVQtype_equiv. unfold "=T=". simpl. 
split; [assumption | reflexivity].*) Qed.


(*Lemma equiv_push_annot: forall A A' e e' , 
     A =va= A' -> e =e= e' -> 
     push_annot A e =va= push_annot A' e'.
Proof. 
intros. unfold equiv_vatts in H. 
unfold equiv_vatts. 
intro c; specialize H with c.
induction A; destruct A'.
- intro a.
split. simpl. reflexivity.
simpl. reflexivity.
- unfold equiv_atts in H.
intro a; specialize H with a.
destruct H. simpl in H1.
destruct v as (a_,e_).
simpl in H. destruct (E[[ e_]] c) eqn:He_.
+ simpl in H1.
destruct (string_eq_dec a_ a); subst.
Search (0 = S _). apply O_S in H1.
destruct H1.
symmetry in H1. rewrite <- count_occ_not_In in H1.
split. split; intro HIn.
simpl in HIn. destruct HIn.
simpl. rewrite H.
simpl. right.
simpl in HIn. rewrite He_ in HIn.
destruct (E[[ e']] c) eqn:He'.
simpl in HIn. destruct HIn. contradiction.
 


destruct H;  
[rewrite <- H  | rewrite H]; 
[rewrite <- H0 | rewrite H0];
apply H1.
Qed.*)


(*---------------------------equiv-----------------------------*)