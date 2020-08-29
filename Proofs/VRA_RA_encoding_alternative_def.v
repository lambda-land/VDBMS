Definition lengthOrder (ls1 ls2 : list vatt) :=
    List.length ls1 < List.length ls2.

Hint Constructors Acc.

Lemma lengthOrder_wf' : forall len, forall ls, List.length ls <= len -> Acc lengthOrder ls.
  unfold lengthOrder; induction len; crush.
Defined.

Theorem lengthOrder_wf : well_founded lengthOrder.
  red; intro; eapply lengthOrder_wf'; eauto.
Defined.

Lemma remove_reduce (a:att) (l:vatts) : List.length (removeAtt a l) < S(List.length l).
Proof. intros. induction l. 
       - unfold removeAtt.  unfold List.length. 
         apply PeanoNat.Nat.lt_0_succ. 
       - simpl. destruct a0. destruct (string_beq a a0). auto. 
         simpl. apply Lt.lt_n_S. auto. 
Qed.

(** REGULAR DEFINITION *)

Definition default : vatt := (ae ""%string (litB false)).

Lemma removeAtt_wf : forall len ls, 1 <= List.length ls <= len
 -> lengthOrder (removeAtt (fstVatt (hd default ls)) ls) ls.
intros. simpl. destruct ls. simpl in H. inversion H. inversion H0.
destruct v. simpl. rewrite stringBEF.eqb_refl. unfold lengthOrder. simpl. 
apply remove_reduce.
Defined.

Hint Resolve removeAtt_wf.

Lemma removeAtt_wf1 : forall ls, 1 <= List.length ls 
 -> lengthOrder (removeAtt (fstVatt (hd default ls)) ls) ls.
intros. eauto. 
Defined.

Lemma removeAtt_wf2 : forall ls, 1 <= List.length ls 
 -> lengthOrder (tl ls) ls.
intros. destruct ls. 
            ++ simpl in H. inversion H. 
            ++ simpl. unfold lengthOrder. simpl. omega.
Defined.

Hint Resolve removeAtt_wf1 removeAtt_wf2.

(*Ltac removeAtt_wf := intros ls ?; intros; generalize (@removeAtt_wf (List.length ls) ls);
destruct (split ls); destruct 1; crush.*)

Lemma cons_injective: forall (A : Type)(a a' : A)(l l' : list A),
   (a = a') /\ (l = l') -> (a :: l) = (a' :: l').
Proof. intros. destruct H. rewrite H, H0. reflexivity. Qed.

Definition nodupatt : list vatt -> list vatt.
    refine (Fix lengthOrder_wf (fun _ => list vatt)
      (fun (ls : list vatt)
           (nodupatt : forall ls' : list vatt, lengthOrder ls' ls -> list vatt) =>
        if le_lt_dec 1 (List.length ls)
        then   
                   let lss := removeAtt (fstVatt (hd default ls)) ls in 
                      match findAtt (fstVatt (hd default ls)) (tl ls) with
                      | false => (hd default ls) :: nodupatt (tl ls) _
                      | true  => let e' := extract_e (fstVatt (hd default ls)) (tl ls) in
                         (ae (fstVatt (hd default ls)) ((sndVatt (hd default ls)) /\(F) e')) :: nodupatt lss _
                      end
        else ls
       )); intros; subst lss; eauto.
  Defined.

Theorem nodupatt_eq : forall ls,
  nodupatt ls = if le_lt_dec 1 (List.length ls)
        then   
                   let lss := removeAtt (fstVatt (hd default ls)) ls in 
                      match findAtt (fstVatt (hd default ls)) (tl ls) with
                      | false => (hd default ls) :: nodupatt (tl ls) 
                      | true  => let e' := extract_e (fstVatt (hd default ls)) (tl ls) in
                         (ae (fstVatt (hd default ls)) ((sndVatt (hd default ls)) /\(F) e')) :: nodupatt lss
                      end
        else ls.
  intros.

Check Fix_eq.
 apply (Fix_eq (lengthOrder_wf) (fun _ => list vatt)); intros. 
  match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end. simpl. destruct(findAtt (fstVatt (hd default x)) (tl x)). 
apply cons_injective. split. reflexivity.
apply H. 
apply cons_injective. split. reflexivity.
apply H. reflexivity.
Qed.

Lemma removeAtt_hd: forall a l, removeAtt (fstVatt (hd default (a :: l))) (a :: l) =
 removeAtt (fstVatt a) l.
intros. destruct a. simpl. rewrite stringBEF.eqb_refl. 
auto. Qed.

Ltac simpl_nondupatt := rewrite nodupatt_eq, removeAtt_hd.

(** FUNCTION WITH wf*)

Lemma removeAtt_wf : forall ls a e, lengthOrder (removeAtt a ls) (ae a e :: ls).
intros. simpl. 
unfold lengthOrder. simpl. 
apply remove_reduce.
Defined.

Lemma tl_wf : forall ls a e, lengthOrder ls (ae a e :: ls).
intros. unfold lengthOrder. simpl. omega.
Defined.

Hint Resolve removeAtt_wf tl_wf.

(*Ltac removeAtt_wf := intros ls ?; intros; generalize (@removeAtt_wf (List.length ls) ls);
destruct (split ls); destruct 1; crush.*)

Lemma cons_injective: forall (A : Type)(a a' : A)(l l' : list A),
   (a = a') /\ (l = l') -> (a :: l) = (a' :: l').
Proof. intros. destruct H. rewrite H, H0. reflexivity. Qed.

Require Import Recdef.

Function nodupatt (v : list vatt) {wf lengthOrder v} : list vatt :=
   match v with 
   | nil          => nil
   | ae a e :: vs =>  match findAtt a vs with
                      | false => ae a e :: nodupatt vs
                      | true  => let e' := extract_e a vs in
                         (ae a (e /\(F) e') ) :: nodupatt (removeAtt a vs)
                      end
   end.
all: intros; eauto. 
Defined.

(** USING FUNCTION WITH measure*)

Hint Resolve remove_reduce.

Lemma cons_injective: forall (A : Type)(a a' : A)(l l' : list A),
   (a = a') /\ (l = l') -> (a :: l) = (a' :: l').
Proof. intros. destruct H. rewrite H, H0. reflexivity. Qed.

Require Import Recdef.

Function nodupatt_ (v : list vatt) {measure List.length v} : list vatt :=
   match v with 
   | nil          => nil
   | ae a e :: vs =>  match findAtt a vs with
                      | false => ae a e :: nodupatt_ vs
                      | true  => let e' := extract_e a vs in
                         (ae a (e /\(F) e') ) :: nodupatt_ (removeAtt a vs)
                      end
   end.
all:intros; simpl; eauto.
Defined.