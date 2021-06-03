(** Equivalence lemmas *)
Set Warnings "-notation-overridden,-parsing".

Load VDBMS_Encoding.
Import VDBMS_Encoding.



Lemma eq_equiv_elems: forall A A', A = A' -> A =set= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma eq_equiv_velems: forall A A', A = A' -> A =vset= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma eq_equiv_vqtype: forall A A', A = A' -> A =vqtype= A'.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma cons_equiv_elems: forall a l1 l2, l1 =set= l2 -> (a::l1) =set= (a::l2).
Proof. 
intros. 
unfold equiv_elems in H.

unfold equiv_elems. 
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

Lemma cons_equiv_velems: forall a l1 l2, l1 =vset= l2 -> (a::l1) =vset= (a::l2).
Proof. 
intros. 
unfold equiv_velems in H. 
unfold equiv_elems in H.
unfold equiv_velems.
intro c. 
unfold equiv_elems. 
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

Lemma In_equiv_elems A A' x: A =set= A' ->
In x A <-> In x A'. Proof. intro H. unfold "=set=" in H.
specialize H with x. destruct H. auto. Qed.


Lemma equiv_irres_order x y l: (x::y::l) =set= (y::x::l).
Proof. unfold equiv_elems. intro. split. split;
try (intro H; simpl in H; simpl;
destruct H; eauto; try (destruct H); eauto).
simpl. destruct (string_eq_dec x a);
destruct (string_eq_dec y a); reflexivity.
Qed.



Lemma NoDup_equiv_elems l l': l =set= l' -> 
    (NoDup l <-> NoDup l').
Proof. intro H. split;
intro H1; unfold equiv_elems in H;
apply forall_dist_and in H; destruct H as [H H0];
rewrite (NoDup_count_occ string_eq_dec) in H1;
rewrite (NoDup_count_occ string_eq_dec); intro x;
specialize H0 with x; try (rewrite <- H0; apply H1); 
try (rewrite H0; apply H1). Qed.



(*Lemma removeElem_equiv a A A':
A =vset= A' -> removeElem a A =vset= removeElem a A'.
Proof. 
unfold equiv_velems.
simpl. unfold equiv_elems. intros.
specialize H with c a0. destruct H as [H H0].
split. 
+ split; intro H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e0 H1]; destruct H1 as [H1 H2];
  destruct (string_eq_dec a0 a) as [Heqdec | Heqdec];
  (* a0 = a *)
  try (rewrite Heqdec in H1; apply notIn_removeElem in H1; destruct H1);
  (* a0 <> a *)
  try (apply In_removeElem in H1; apply In_config_true with (c:=c) in H1;
  auto; apply H in H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e1 H1]; destruct H1 as [H1 H1e1];
  rewrite <- In_config_exists_true; exists e1;
  split; try (apply In_removeElem; eauto); try(eauto)).
  
+ destruct (string_eq_dec a a0) as [eq | neq].
  rewrite eq. rewrite count_occ_config_removeElem_eq.
  reflexivity.
  repeat (rewrite (count_occ_config_removeElem_neq _ _ neq)).
  assumption.
Qed.*)

Lemma equiv_subset: forall A B B' , 
     B =set= B' -> subset A B <-> subset A B'.
Proof. 
intros. unfold equiv_elems in H. unfold subset.
split; intro H1;
intro x; specialize H with x;
destruct H;  
[rewrite <- H  | rewrite H]; 
[rewrite <- H0 | rewrite H0];
apply H1.
Qed.


Lemma nil_equiv_eq: forall A, A =set= [] -> 
A = []. intros. unfold equiv_elems in H. 
simpl in H.
apply (count_occ_inv_nil string_eq_dec).
intro x. specialize H with x. destruct H.
exact H0. Qed.

Lemma cons_equiv_neq: forall x l A, A =set= (x::l) -> 
A <> []. 
Proof. intros. unfold equiv_elems in H. 
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

Lemma configVQtype_equiv: forall Q Q' c, Q =vqtype= Q' ->
(QT[[ Q]] c) =set= (QT[[ Q']] c).
Proof. intros. unfold "=vqtype=" in H. apply H.
(* unfold configVQtype, configaVelems. unfold equiv_vqtype in H.
destruct H. destruct Q as (A, e). destruct Q' as (A', e').
simpl in *. rewrite H0. destruct (E[[ e']] c).
apply H. reflexivity.*)
Qed.

Lemma configaVelems_equivE_configVQtype: forall Q Q', (fst Q) =vset= (fst Q') ->
(snd Q) =e= (snd Q') -> Q =vqtype= Q'. 
Proof. intros. 
unfold "=vset=" in H. 
destruct Q as (A, e). destruct Q' as (A', e').
simpl in *. unfold "=vqtype=". intro c. simpl.
rewrite H0. 
destruct (E[[ e']] c).
apply H. reflexivity.
Qed.

Lemma push_annot_correctness A e c: 
    AX[[ (A, e)]] c = X[[ A < e]] c.
Proof. induction A. 
simpl. destruct ( E[[ e]] c); reflexivity.
unfold push_annot; fold push_annot.
destruct a. simpl configVQtype. 
simpl (AX[[_]]c) in IHA.
simpl (X[[_]]c). simpl (AX[[_]]c).
destruct (E[[ e]] c); destruct (E[[ f]] c); simpl;
try(eauto).
rewrite IHA. reflexivity.
Qed.

Lemma configVElemSet_push_annot A e c:
configVElemSet (push_annot A e) c = configVQtype (A, e) c.
Proof. symmetry. apply push_annot_correctness. Qed.

Lemma push_annot_equiv A B e: A =vset= B -> (A < e) =vset= (B < e).
Proof. intro H. unfold "=vset=". intro c.
repeat(rewrite configVElemSet_push_annot).
simpl. destruct (E[[ e]] c). apply H. reflexivity.
(*apply configVQtype_equiv. unfold "=vqtype=". simpl. 
split; [assumption | reflexivity].*) Qed.

Lemma existsb_elem_equiv: forall A A', A =set= A' ->
(forall a, (existsb (string_beq a) A) = (existsb (string_beq a) A')).
Proof. intros A A' H. intro a.
unfold "=set=" in H.
specialize H with a. destruct H as [HIn Hcount].
destruct (existsb (string_beq a) A) eqn: HexA.
rewrite existsb_In_elem in HexA. rewrite HIn in HexA.
rewrite <- existsb_In_elem in HexA. symmetry. assumption.
rewrite not_existsb_In_elem in HexA. rewrite HIn in HexA.
rewrite <- not_existsb_In_elem in HexA. symmetry. assumption.
Qed.

Lemma condtype_equiv: forall A A' c, A =set= A' ->
(A ||- c) = (A' ||- c).
Proof. induction c; intros H; simpl condtype.
- reflexivity.
- (* apply existsb_elem_equiv with (a:=e) in H.
  rewrite H.*) reflexivity.
- (*apply existsb_elem_equiv with (a:=e) in H as He. 
  apply existsb_elem_equiv with (a:=e0) in H as He0.
  rewrite He, He0. *)
  reflexivity.
- apply IHc in H. rewrite H. reflexivity.
- apply IHc1 in H as Hc1.
  apply IHc2 in H as Hc2.
rewrite Hc1, Hc2. reflexivity.
- apply IHc1 in H as Hc1.
  apply IHc2 in H as Hc2.
rewrite Hc1, Hc2. reflexivity.
Qed.

(* might be useful to have E[[ e]] c = true to prove implies *)

Lemma equiv_vqtype_In Q Q' a : Q =vqtype= Q' -> (exists e : fexp, In (ae a e) (fst Q < snd Q) /\ sat e)
-> exists e0 : fexp, In (ae a e0) (fst Q' < snd Q') /\ sat e0.
Proof. intros H H0. unfold sat in H0. destruct H0 as [e0 [HIne0 He0c] ].
destruct He0c as [c He0]. 
assert (Hex: exists e, In (ae a e) (fst Q < snd Q) /\ (E[[ e]] c) = true).
exists e0. eauto. 
rewrite In_config_exists_true in Hex. rewrite configVElemSet_push_annot in Hex.
destruct Q as (Aq, eq). simpl fst in Hex. simpl snd in Hex.
rewrite In_equiv_elems with (A':=(QT[[ Q']] c)) in Hex; try eauto.
destruct Q' as (Aq', eq'). rewrite <- configVElemSet_push_annot in Hex.
rewrite <- In_config_exists_true in Hex. 
destruct Hex as [e1 [HIn He1] ]. exists e1. split. auto.
unfold sat. exists c. auto. Qed.

Lemma vcondtype_equiv: forall e Q Q' vc, Q =vqtype= Q' ->
{ e , Q |- vc } -> { e , Q' |- vc }.
Proof. intros. intros.
induction H0. 
- apply litCB_vC.
- apply elemOpV_vC. apply equiv_vqtype_In with (a:=a)in H;
auto.
- apply elemOpA_vC. apply equiv_vqtype_In with (a:=a1)in H;
auto. apply equiv_vqtype_In with (a:=a2)in H;
auto.
- apply NegC_vC. eauto.
- apply ConjC_vC; eauto.
- apply DisjC_vC; eauto.
- apply ChcC_vC; eauto.
Qed.

(*
Lemma condtype_equiv: forall A A' c, A =set= A' ->
(A ||- c) = (A' ||- c).
Proof. induction c; intros H; simpl condtype.
- reflexivity.
- apply existsb_elem_equiv with (a:=a) in H.
rewrite H. reflexivity.
- apply existsb_elem_equiv with (a:=a) in H as Ha.
apply existsb_elem_equiv with (a:=a0) in H as Ha0.
rewrite Ha, Ha0. reflexivity.
- apply IHc in H. rewrite H. reflexivity.
- apply IHc1 in H as Hc1.
  apply IHc2 in H as Hc2.
rewrite Hc1, Hc2. reflexivity.
- apply IHc1 in H as Hc1.
  apply IHc2 in H as Hc2.
rewrite Hc1, Hc2. reflexivity.
Qed.


*)

(*Lemma equiv_push_annot: forall A A' e e' , 
     A =vset= A' -> e =e= e' -> 
     push_annot A e =vset= push_annot A' e'.
Proof. 
intros. unfold equiv_velems in H. 
unfold equiv_velems. 
intro c; specialize H with c.
induction A; destruct A'.
- intro a.
split. simpl. reflexivity.
simpl. reflexivity.
- unfold equiv_elems in H.
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