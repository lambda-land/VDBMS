(** lemmas for set OP *)
Set Warnings "-notation-overridden,-parsing".


Load AttOPVatt.

(* Push_annot vatts_inter *)

(*Lemma dist_push_annot_vatts_inter A B e:
vatts_inter (push_annot A e) (push_annot B e)
= push_annot (vatts_inter A B) e.
Proof. Admitted.*)

(* -- In set_remove  -- *)
(*Lemma notIn_set_remove_eq a l :
   ~ In a l -> set_remove string_eq_dec a l = l.
Proof.
induction l. 
- intro H. simpl. reflexivity.
- intro H. simpl in H.
  apply Classical_Prop.not_or_and in H.
  destruct H.
  simpl. destruct (string_eq_dec a a0) eqn:Haa0.
  + destruct H. eauto.
  + rewrite (IHl H0). reflexivity.
Qed.*)

Lemma set_remove_config: forall a A c (H: NoDupAtt A), 
      set_remove string_eq_dec a (configVAttSet A c) 
      = configVAttSet (removeAtt a A) c.
Proof. intros a A c.
induction A; intro H.
 simpl. reflexivity.
- inversion H; subst. simpl.
  destruct (E[[ e]] c) eqn:He.
  + simpl. destruct (string_eq_dec a a1).
    ++ rewrite e0. rewrite stringBEF.eqb_refl.
       rewrite (notInAtt_removeAtt_eq _ _ H2). reflexivity.
    ++ rewrite <- stringBEF.eqb_neq in n. 
       rewrite n. simpl. rewrite He. rewrite (IHA H3).
       reflexivity.
  + destruct (string_beq a a1). 
    ++ eauto.
    ++ simpl. rewrite He. eauto.
Qed.


(* -- In config set_add -- *)
Lemma config_set_add_equiv_atts_true a f c A: ~ In (ae a f) A -> (E[[ f]]c) = true ->
configVAttSet (set_add vatt_eq_dec (ae a f) A) c =a=  (a :: (configVAttSet A c)).
Proof. induction A.
- intros. simpl. rewrite H0. reflexivity.
- intros. simpl in H. apply Classical_Prop.not_or_and in H.
destruct H. simpl set_add. 
destruct (vatt_eq_dec (ae a f) a0) eqn: Heq.
++ destruct H. eauto.
++ destruct a0 as (a0, e0).
   simpl configVAttSet. apply (IHA H1) in H0.
   destruct (E[[ e0]] c) eqn: He0.
   +++ rewrite (cons_equiv_atts a0 H0).
       apply equiv_irres_order.
   +++ assumption.
Qed.


Lemma config_set_add_equiv_atts_false a f c A: ~ In (ae a f) A -> (E[[ f]]c) = false ->
configVAttSet (set_add vatt_eq_dec (ae a f) A) c =a=  (configVAttSet A c).
Proof. induction A.
- intros. simpl. rewrite H0. reflexivity.
- intros. simpl in H. apply Classical_Prop.not_or_and in H.
destruct H. simpl set_add. 
destruct (vatt_eq_dec (ae a f) a0) eqn: Heq.
++ reflexivity.
++ destruct a0 as (a0, e0).
   simpl configVAttSet. apply (IHA H1) in H0.
   destruct (E[[ e0]] c) eqn: He0.
   +++ rewrite (cons_equiv_atts a0 H0).
       reflexivity.
   +++ assumption.
Qed.


(* -- count_occ set_add -- *)
Lemma count_occ_set_add_eq {A:Type} eq_dec (l:list A) (x:A):
    ~(In x l) -> (count_occ eq_dec (set_add eq_dec x l) x 
                           = S (count_occ eq_dec l x)).
Proof. intros. induction l as [ |a l IHal]. 
       - simpl. destruct (eq_dec x x). 
         reflexivity. destruct n. reflexivity. 
       - simpl. 
         rewrite not_in_cons in H. destruct H.
         destruct (eq_dec a x); subst.
         + destruct H. reflexivity. 
         + destruct (eq_dec x a); subst. 
           ++ destruct n. reflexivity.
           ++ simpl. destruct (eq_dec a x); subst. 
              +++ destruct n. reflexivity.
              +++ apply IHal. auto.
Qed.

Lemma count_occ_set_add_eq_In {A:Type} eq_dec (l:list A) (x:A):
    (In x l) -> (count_occ eq_dec (set_add eq_dec x l) x 
                           = (count_occ eq_dec l x)).
Proof. intros. induction l as [ |a l IHal]. 
       - simpl in H. destruct H. 
       - simpl. 
         simpl in H. destruct H. rewrite H. 
         destruct (eq_dec x x); subst.
         + simpl. destruct (eq_dec x x); subst. reflexivity.
           contradiction.
         + destruct n. reflexivity. 
         + destruct (eq_dec x a); subst. 
              ++ destruct (eq_dec a a); subst.
                 simpl. destruct (eq_dec a a); subst.
                 reflexivity. contradiction. 
                 rewrite (count_occ_cons_neq _ l n). reflexivity. 
              ++  rewrite count_occ_cons_neq. 
                  destruct (eq_dec a x); subst. destruct n.
                  reflexivity. apply IHal. apply H. eauto.
Qed.

Lemma count_occ_set_add_neq {A:Type} eq_dec (l:list A) (x y:A):
    x <> y -> count_occ eq_dec (set_add eq_dec x l) y = 
                          count_occ eq_dec l y.
Proof. 
   intros Hxy. induction l as [ |a l IHal]. 
   - simpl. destruct (eq_dec x y); subst.  
      + destruct Hxy. reflexivity.
      + reflexivity.
   - simpl. destruct (eq_dec x a). 
      + destruct (eq_dec a y); subst. destruct Hxy. reflexivity.
           simpl. destruct (eq_dec a y); subst. destruct n. 
           destruct Hxy. reflexivity. reflexivity.
      + destruct (eq_dec a y); subst. simpl. 
        ++ destruct (eq_dec y y); subst.
            +++ auto.
            +++ destruct n0. reflexivity. 
        ++ simpl. destruct (eq_dec a y); subst. 
            destruct n0. reflexivity. auto. 
Qed.

Lemma count_occ_set_add_cons {A:Type} eq_dec (l:list A) (x y:A):
         ~(In x l) -> (count_occ eq_dec (set_add eq_dec x l) y =
                count_occ eq_dec (x::l) y).
Proof. intros H0. destruct (eq_dec x y) as [H | H]. 
       + rewrite <- H. rewrite (count_occ_set_add_eq eq_dec l).
         symmetry. apply count_occ_cons_eq. auto. auto.
       + apply (count_occ_set_add_neq eq_dec l) in H as H1. rewrite H1.
         symmetry. apply count_occ_cons_neq. auto. 
Qed.

(* -- count_occ set_remove -- *)

Lemma count_occ_set_remove_neq {A:Type} eq_dec (l:list A) (x y:A):
    x <> y -> count_occ eq_dec (set_remove eq_dec x l) y = 
                          count_occ eq_dec l y.
Proof. 
   intros Hxy. induction l as [ |a l IHal]. 
   - simpl. reflexivity.
   - simpl.  destruct (eq_dec x a); subst.  
      + destruct (eq_dec a y); subst. destruct Hxy.
        reflexivity. reflexivity.
      + simpl. destruct (eq_dec a y); subst. 
        rewrite IHal. reflexivity. assumption.
Qed.

Lemma count_occ_set_remove_In {T:Type} eq_dec (A :list T) (x:T):
    In x A -> S (count_occ eq_dec (set_remove eq_dec x A) x)
         = count_occ eq_dec A x.
Proof. intro H. induction A. 
- simpl in H. destruct H.
- simpl in H. destruct H; subst.
  + simpl. destruct (eq_dec x x).
    reflexivity. contradiction.
  + simpl. destruct (eq_dec x a);
    destruct (eq_dec a x);
    try (reflexivity);
    try (symmetry in e; contradiction).
    ++ simpl. destruct (eq_dec a x). 
       contradiction. eauto.
Qed.

Lemma count_occ_set_remove_notIn (T:Type) eq_dec (A :list T) (x:T):
    ~In x A -> count_occ eq_dec (set_remove eq_dec x A) x
         = count_occ eq_dec A x.
Proof. intro H.
apply (contrapositive _ _ (set_remove_1 eq_dec x x A)) in H as H1.
rewrite (count_occ_not_In eq_dec A x) in H.
rewrite (count_occ_not_In eq_dec _ x) in H1.
rewrite H, H1. reflexivity.
Qed.

(* -- count_occ set_union -- *)

Lemma count_occ_set_union_In {A:Type} eq_dec (l l':list A) (x:A):
    NoDup l -> NoDup l' -> 
    (In x l \/ In x l') -> 
      count_occ eq_dec (set_union eq_dec l l') x = 1.
Proof. intros.
pose (set_union_nodup eq_dec H H0) as HNdpll'.
apply (set_union_intro eq_dec) in H1.
rewrite (NoDup_count_occ' eq_dec) in HNdpll'.
apply HNdpll'. apply H1.
Qed.

Lemma count_occ_set_union_not_In {A:Type} eq_dec (l l':list A) (x:A):
    NoDup l -> NoDup l' -> 
    ~(In x l \/ In x l') -> 
      count_occ eq_dec (set_union eq_dec l l') x = 0.
Proof. intros.
rewrite <- (set_union_iff eq_dec x l l') in H1.
rewrite (count_occ_not_In eq_dec) in H1.
exact H1.
Qed.

(* -- count_occ set_inter -- *)

Lemma count_occ_set_inter_In {A:Type} eq_dec (l l':list A) (x:A):
    NoDup l -> NoDup l' -> 
    (In x l /\ In x l') -> 
      count_occ eq_dec (set_inter eq_dec l l') x = 1.
Proof. intros.
pose (set_inter_nodup eq_dec H H0) as HNdpll'.
rewrite <- (set_inter_iff eq_dec) in H1.
rewrite (NoDup_count_occ' eq_dec) in HNdpll'.
apply HNdpll'. apply H1.
Qed.

Lemma count_occ_set_inter_not_In {A:Type} eq_dec (l l':list A) (x:A):
    NoDup l -> NoDup l' -> 
    ~(In x l /\ In x l') -> 
      count_occ eq_dec (set_inter eq_dec l l') x = 0.
Proof. intros.
rewrite <- (set_inter_iff eq_dec x l l') in H1.
rewrite (count_occ_not_In eq_dec) in H1.
exact H1.
Qed.


(* -- In set_remove -- *)

Lemma notIn_set_remove {T:Type} eq_dec (a:T) (A:list T): NoDup A -> 
    ~ In a (set_remove eq_dec a A).
Proof. intros. unfold not. intro HIn.
apply (set_remove_2 _ H) in HIn. destruct HIn.
reflexivity. Qed.

Lemma notIn_set_remove_eq {T:Type} eq_dec (a:T) (A:list T): 
    ~ In a A -> set_remove eq_dec a A = A.
Proof.  intros. induction A. 
- simpl. reflexivity.
- simpl in H. apply Classical_Prop.not_or_and in H.
destruct H as [H1 H2]. simpl.
destruct (eq_dec a a0) eqn:Heqdec.
destruct H1. eauto. apply IHA in H2.
rewrite H2. reflexivity.
Qed.

(* -- In set_add -- *)

Lemma In_set_add {T:Type} eq_dec (a:T) (A:list T): In a A -> 
      (set_add eq_dec a A) = A.
Proof. intros. induction A. 
- simpl in H. destruct H.
- simpl in H. 
destruct H as [H1 | H2]; simpl;
destruct (eq_dec a a0) eqn:Heqdec.
reflexivity. symmetry in H1. contradiction.
reflexivity. rewrite IHA. reflexivity.
assumption. Qed.

Lemma notIn_set_add_equiv_atts a A:
         ~ In a A -> (set_add string_eq_dec a A) =a= (a::A) .
Proof. unfold equiv_atts. intros Ha a0. split.
       - split.
         + intro H. simpl. rewrite set_add_iff in H. 
           destruct H. ++ left. auto.
                       ++ right. auto.
         + intro H. rewrite set_add_iff. simpl in H. 
           destruct H. ++ left. auto.
                       ++ right. auto. 
      - apply (count_occ_set_add_cons string_eq_dec A a a0).
        auto.
Qed.


Lemma notIn_set_add_equiv_vatts a A: ~ In a A -> 
      (set_add vatt_eq_dec a A) =va= (a::A) .
Proof. unfold equiv_vatts. destruct a as (a, e).
intros H c. simpl configVAttSet. destruct (E[[ e]]c) eqn: He.
+ apply (config_set_add_equiv_atts_true _ _ _ _ H He). 
+ apply (config_set_add_equiv_atts_false _ _ _ _ H He). 
Qed.

(* -- In set_add remove  -- *)
Lemma In_set_add_remove: forall a A (HA: NoDup A), 
       In a A ->  
       set_add string_eq_dec a (set_remove string_eq_dec a A) =a= A.
Proof. intros. unfold equiv_atts. intro.
destruct (string_beq a0 a) eqn:Haa0.
+ rewrite stringDecF.eqb_eq in Haa0.
rewrite Haa0.
split. split. 
++ intro. assumption.
++ intro. apply set_add_intro2. reflexivity.
++ apply (notIn_set_remove string_eq_dec a) in HA as HA'.
rewrite (count_occ_set_add_eq _ _ _ HA').
rewrite count_occ_not_In  in HA'. rewrite HA'.
rewrite NoDup_count_occ' in HA. apply HA in H.
rewrite H. reflexivity.
+ rewrite stringBEF.eqb_neq in Haa0.
split. split. 
++ intro Hset. 
apply (set_add_elim2 _ _ Hset) in Haa0 as Hsetr.
apply set_remove_1 in Hsetr. assumption.
++ intro Ha0. apply set_add_intro1. 
apply set_remove_3. assumption. assumption.
++ rewrite count_occ_set_add_neq. 
rewrite count_occ_set_remove_neq.
reflexivity. eauto. eauto.
Qed.

(* -- set_add set_remove -- *)
Lemma set_add_remove: forall a A (HA: NoDup A),
       set_add string_eq_dec a A =a= 
       set_add string_eq_dec a (set_remove string_eq_dec a A).
Proof. intros. destruct (in_dec string_eq_dec a A) eqn:HInA.
rewrite In_set_add. symmetry.
apply In_set_add_remove. assumption.
assumption. assumption.
rewrite notIn_set_remove_eq. reflexivity.
assumption. Qed.


(* -- In set_union -- *)
(* contrapositive of set_union_iff *) 
Lemma notIn_set_union: forall {T:Type} eq_dec (a:T) (A A':list T) ,
 (~ In a A /\ ~ In a A') <-> ~ In a (set_union eq_dec A A').
Proof. 
intros T eq_dec a A A'. 
pose (contrapositive_iff _ _(set_union_iff eq_dec a A A')) as H.
rewrite not_or_and_not in H.
exact H.
Qed.

(* -- InAtt set_union -- *)

Lemma InAtt_set_union: forall a A A', 
    InAtt a (set_union vatt_eq_dec A A') <-> InAtt a A \/ InAtt a A'.
Proof. intros. split.
- intro H. rewrite InAtt_In_exfexp in H.
  destruct H as [e H]. apply set_union_iff in H.
  destruct H.
  + left. rewrite InAtt_In_exfexp. 
    exists e. auto.
  + right. rewrite InAtt_In_exfexp. 
    exists e. auto.
- intro H. destruct H; 
  rewrite InAtt_In_exfexp in H;
  destruct H as [e H]; 
  rewrite InAtt_In_exfexp; 
  exists e; apply set_union_iff;
  eauto.
Qed.
  
  
Lemma notInAtt_set_union: forall a A A',
 (~ InAtt a A /\ ~ InAtt a A') <-> ~ InAtt a (set_union vatt_eq_dec A A').
Proof. intros a A A'.
pose (contrapositive_iff _ _(InAtt_set_union a A A')) as H.
rewrite not_or_and_not in H.
exact H.
Qed.


Lemma notInAtt_vatts_inter a A B: 
~ InAtt a A -> ~ InAtt a (vatts_inter A B).
Proof. apply vatts_inter_ind. 
- intros. auto.
-  intros. apply H. simpl in H0.
rewrite not_or_and_not in H0. destruct H0. auto.
- intros. simpl. simpl in H0.
rewrite not_or_and_not in H0. 
rewrite not_or_and_not. destruct H0. split.
all: auto. Qed.


Lemma notInAttB_vatts_inter a A B: 
~ InAtt a B -> ~ InAtt a (vatts_inter A B).
Proof. apply vatts_inter_ind. 
- intros. auto.
-  intros. apply H. simpl in H0.
auto.
- intros. simpl. simpl in H0.
rewrite not_or_and_not. split.
rewrite <- existsbAtt_InAtt in H0.
unfold not; intro. rewrite <- H1 in H0.
rewrite e1 in H0. contradiction.
apply H in H0. assumption. Qed.


Lemma InAtt_vatts_inter a A B: 
InAtt a (vatts_inter A B) -> InAtt a A /\ InAtt a B.
Proof. intro H. split;
[ pose (contrapositive _ _ (notInAtt_vatts_inter a A B))  as HInA 
| pose (contrapositive _ _ (notInAttB_vatts_inter a A B)) as HInA ];
apply Classical_Prop.NNPP; eauto. 
Qed.

Lemma InAtt_vatts_inter_2 a A B: 
 (InAtt a A /\ InAtt a B) -> InAtt a (vatts_inter A B).
Proof. apply vatts_inter_ind. 
- intros. destruct H. auto.
- intros. apply H. simpl in H0.
 destruct H0. destruct H0. rewrite H0 in *. 
rewrite <- existsbAtt_InAtt in H1. rewrite e1 in H1. discriminate H1. auto.
- intros. simpl. simpl in H0.
destruct H0. destruct H0. left. auto. right. apply H. auto.
Qed.

Lemma InAtt_vatts_inter_rewrite a A B: 
InAtt a (vatts_inter A B) <-> InAtt a A /\ InAtt a B.
Proof. split. apply InAtt_vatts_inter.
apply InAtt_vatts_inter_2. Qed.

Lemma In_vatts_inter a e c A B: 
In (ae a e) (vatts_inter A B) /\ (E[[ e]]c) = true -> 
exists e', In (ae a e') B /\ (E[[ e']]c) = true.
Proof. apply vatts_inter_ind; intros.
- destruct H. destruct H. 
- apply H. eauto.
- (* extract_e a A' -> In a A[[A]]c -> goal *) destruct H0.
destruct H0 as [Heq | HIn]. inversion Heq; subst.
simpl in H1. rewrite andb_true_iff in H1.
destruct H1 as [He0 He']. apply extract_true_In in He' as HInAtt.
rewrite <- In_config_exists_true in HInAtt. auto.
apply H. eauto.

(*induction A; intros. destruct H. simpl in H.
destruct H.
destruct H. rewrite vatts_inter_equation in H.
destruct a0. destruct (existsbAtt a0 B) eqn:Hex.
simpl in H. destruct H.  inversion H; subst.
simpl in H0. rewrite andb_true_iff in H0.
destruct H0. apply extract_true_In in H1 as HInAtt. 
rewrite <- In_config_exists_true in HInAtt. auto.
apply IHA. eauto. 
apply IHA. eauto.*)
Qed.


Lemma set_add_equiv: forall a A A',
A=a=A' -> set_add string_eq_dec a A =a= set_add string_eq_dec a A'.
Proof. intros a A A'.
intro H. unfold equiv_atts in H.
unfold equiv_atts. intro a0.
specialize H with a0. destruct H as [H H0].
split. 
-  repeat (rewrite set_add_iff).
rewrite <- H. reflexivity.
- destruct (string_eq_dec a a0).
  + rewrite e. destruct (in_dec string_eq_dec a0 A).
    ++ repeat(rewrite count_occ_set_add_eq_In).
       all: try(assumption). rewrite <- H. assumption.
    ++ repeat(rewrite count_occ_set_add_eq). apply eq_S.
       all: try(assumption). rewrite <- H. assumption.
  + repeat(rewrite count_occ_set_add_neq). 
    all: assumption.
Qed.

Lemma set_remove_equiv: forall a A A' (HA: NoDup A) (HA': NoDup A'),
A=a=A' -> set_remove string_eq_dec a A =a= set_remove string_eq_dec a A'.
Proof. intros a A A' HA HA'.
intro H. unfold equiv_atts in H.
unfold equiv_atts. intro a0.
specialize H with a0. destruct H as [H H0].
split. 
-  repeat (rewrite set_remove_iff).
rewrite <- H. reflexivity. all:assumption.
- destruct (string_eq_dec a a0).
  + rewrite e. pose (notIn_set_remove string_eq_dec) as HnInA.
    apply HnInA with (a:=a0) in HA.
    pose (notIn_set_remove string_eq_dec) as HnInA'.
    apply HnInA' with (a:=a0) in HA'.
    rewrite count_occ_not_In in HA. rewrite HA.
    rewrite count_occ_not_In in HA'. rewrite HA'.
    reflexivity.
  + repeat(rewrite count_occ_set_remove_neq). 
    all: assumption.
Qed.

(* merge next two *)

Lemma set_union_equiv A A' B B' (HA: NoDup A) (HA': NoDup A')
(HB: NoDup B) (HB': NoDup B'):
A=a=B -> A'=a=B' -> set_union string_eq_dec A A' =a= set_union string_eq_dec B B'.
Proof.
intros H1 H2. unfold equiv_atts in H1, H2.
unfold equiv_atts. intro a0.
specialize H1 with a0. destruct H1 as [H1 H1'].
specialize H2 with a0. destruct H2 as [H2 H2'].
split. 
- repeat (rewrite set_union_iff). rewrite <- H1, H2. reflexivity. 
- destruct (in_dec string_eq_dec a0 (set_union string_eq_dec A A')) as [i|i];
rewrite (set_union_iff string_eq_dec a0 A A') in i;
pose i as j;
try(apply (count_occ_set_union_In string_eq_dec _ HA HA') in j);
try(apply (count_occ_set_union_not_In string_eq_dec _ HA HA') in j);
rewrite H1, H2 in i;
try(apply (count_occ_set_union_In string_eq_dec _ HB HB') in i);
try(apply (count_occ_set_union_not_In string_eq_dec _ HB HB') in i);
rewrite i, j; reflexivity.
Qed.


Lemma set_inter_equiv A A' B B' (HA: NoDup A) (HA': NoDup A')
(HB: NoDup B) (HB': NoDup B'):
A=a=B -> A'=a=B' -> set_inter string_eq_dec A A' =a= set_inter string_eq_dec B B'.
Proof.
intros H1 H2. unfold equiv_atts in H1, H2.
unfold equiv_atts. intro a0.
specialize H1 with a0. destruct H1 as [H1 H1'].
specialize H2 with a0. destruct H2 as [H2 H2'].
split. 
- repeat (rewrite set_inter_iff). rewrite <- H1, H2. reflexivity. 
- destruct (in_dec string_eq_dec a0 (set_inter string_eq_dec A A')) as [i|i];
rewrite (set_inter_iff string_eq_dec a0 A A') in i;
pose i as j;
try(apply (count_occ_set_inter_In string_eq_dec _ HA HA') in j);
try(apply (count_occ_set_inter_not_In string_eq_dec _ HA HA') in j);
rewrite H1, H2 in i;
try(apply (count_occ_set_inter_In string_eq_dec _ HB HB') in i);
try(apply (count_occ_set_inter_not_In string_eq_dec _ HB HB') in i);
rewrite i, j; reflexivity.
Qed.


Lemma is_disjoint_bool_equiv A A' B B' (HA: NoDup A) (HA': NoDup A')
(HB: NoDup B) (HB': NoDup B'):
A=a=B -> A'=a=B' -> is_disjoint_bool A A' = is_disjoint_bool B B'.
Proof. intros. unfold is_disjoint_bool.
pose (set_inter_equiv HA HA' HB HB' H H0) as Hinter.
destruct (atts_inter A A') eqn: HAA'; unfold atts_inter;
unfold atts_inter in HAA'; rewrite HAA' in Hinter;
symmetry in Hinter.
+ apply nil_equiv_eq in Hinter.
  rewrite Hinter. reflexivity.
+ apply cons_equiv_neq in Hinter.
  destruct (set_inter string_eq_dec B B').
  contradiction. reflexivity.
Qed.

Lemma count_occ_set_remove {A: Type} eq_dec (l:list A) (x: A) : 
   count_occ eq_dec l x > 1 <-> 
      count_occ eq_dec (set_remove eq_dec x l) x > 0.
Proof. split; intro H; induction l;
simpl in H. 
- inversion H.
- simpl. destruct (eq_dec x a) as [Hxa | Hxa];
subst. simpl in H. destruct (eq_dec a a). omega.
contradiction. simpl. 
simpl in H. destruct (eq_dec a x). symmetry in e. contradiction.
apply IHl. assumption.
- inversion H.
- simpl. destruct (eq_dec x a) as [Hxa | Hxa];
subst. simpl in H. destruct (eq_dec a a).
omega. contradiction. simpl. 
simpl in H. destruct (eq_dec a x). symmetry in e. contradiction.
apply IHl. assumption.
Qed. 

Lemma equiv_qtype_set_remove_cons A a A':
     In a A'-> A =t= set_remove string_eq_dec a A' <->
               (a :: A) =t= A'.
Proof. intros H1. split; intro H;
unfold equiv_qtype; unfold equiv_qtype in H;
unfold equiv_atts;  unfold equiv_atts in H;
intro x; specialize H with x; destruct H as [H H0];
split.
- split; intro. simpl in H2.
destruct H2; subst. assumption. apply H in H2.
apply (set_remove_1 string_eq_dec) with (b:=a).
assumption.
simpl. destruct (string_eq_dec a x) as [Hxa | Hxa].
left. assumption. right. 
apply H. apply (set_remove_3 string_eq_dec). 
all: eauto.
- simpl. destruct (string_eq_dec a x) as [Hxa | Hxa]
; subst.
rewrite H0. rewrite count_occ_set_remove_In.
reflexivity.  assumption. 
rewrite count_occ_set_remove_neq in H0.
all: assumption.

- split; intro H2.
+ simpl in H0. destruct (string_eq_dec a x) as [Hxa | Hxa];
subst. 
  ++ rewrite (count_occ_In string_eq_dec) in H2.
apply gt_n_S in H2. rewrite H0 in H2.
apply count_occ_set_remove in H2.
rewrite <- (count_occ_In string_eq_dec) in H2.
assumption. 
  ++ rewrite (count_occ_In string_eq_dec) in H2.
rewrite H0 in H2.
rewrite <- (count_occ_In string_eq_dec) in H2.
apply (set_remove_3 string_eq_dec). all: eauto.
+ simpl in H0. destruct (string_eq_dec a x) as [Hxa | Hxa];
subst.
 ++ rewrite (count_occ_In string_eq_dec) in H2.
rewrite <- count_occ_set_remove in H2.
rewrite (count_occ_In string_eq_dec).
rewrite <- H0 in H2. omega.
 ++ rewrite (count_occ_In string_eq_dec) in H2.
rewrite (count_occ_set_remove_neq _ _ Hxa) in H2.
rewrite <- H0 in H2. rewrite (count_occ_In string_eq_dec).
omega.

- simpl in H0. destruct (string_eq_dec a x) as [Hxa | Hxa];
subst. 
  ++ apply eq_add_S. rewrite H0. rewrite count_occ_set_remove_In.
     reflexivity. assumption.
  ++ rewrite (count_occ_set_remove_neq _ _ Hxa). assumption. 
Qed.



Lemma set_union_vatts_nil_l: forall A (H: NoDup A), 
          set_union vatt_eq_dec [] A =va= A.
Proof. induction A. simpl. 
reflexivity. simpl.  
intro H.
unfold vatts_union.
simpl. destruct a as (a, e).
(* get ~ In a set_union from context and rewrite set_add *)
inversion H; subst.
apply (contrapositive _ _ (set_union_emptyL vatt_eq_dec (ae a e) A)) in H2.
unfold set_In in H2. 
pose (notIn_set_add_equiv_vatts (ae a e) (set_union vatt_eq_dec [] A)) as Hset_add.
rewrite Hset_add. 
apply cons_equiv_vatts. apply IHA.
all:assumption.
Qed.

Lemma  extract_set_union: forall a A A' c (HA: NoDupAtt A) (HA': NoDupAtt A'),
      (E[[ extract_e a (set_union vatt_eq_dec A A')]]c) 
         = (E[[ (extract_e a A \/(F) extract_e a A')]]c).
Proof. (*intros a A A'. generalize dependent a.*)
 induction A' as [|a' A' IHA']; intros.
- simpl. rewrite orb_false_r. reflexivity.
- destruct a' as (a', e').
  inversion HA' as [|a'' e'' A'' HnInAttA' HNdpAttA'] ; subst.
  (* destruct (string_eq_dec a' a); subst.
  + simpl. rewrite simpl_extract_eq. *)
    specialize IHA' with c. pose  (IHA' HA HNdpAttA') as IH.
    destruct (InAtt_dec a' A) as [HInAttA | HnInAttA].
    ++ (* InAtt a A *) 
       rewrite InAtt_In_exfexp in HInAttA.
       destruct HInAttA as [e HInA].
       destruct (fexp_eq_dec e e'); subst.
       +++ (* e = e' -> In (ae a e') A *)
           simpl. 
           (* rewrite set_add *)
           apply (set_union_intro1 vatt_eq_dec) with (y:=A') 
           in HInA as HInAUA'. 
           apply (In_set_add vatt_eq_dec ) in HInAUA' as Hsetadd.
           rewrite Hsetadd. 
           simpl in IHA'. 
           (* rewrite IH *)
           rewrite IH. 
           destruct (string_eq_dec a a') as [Heq|Heq]; subst.
           { simpl. rewrite simpl_extract_eq.
             rewrite (notInAtt_extract _ _ HnInAttA').
             rewrite (In_extract _ _ HA HInA).  simpl.
             repeat( rewrite orb_false_r). 
             rewrite orb_diag. reflexivity.
           }
           { simpl. rewrite (simpl_extract_neq _ _ Heq).
             reflexivity.
           }
       
       +++ (* e <> e' -> In (ae a e) A *)
           (* rewrite set_add *)
           assert (HnInAe': ~ In (ae a' e') A). 
           { apply NoDupAtt_In_notIn with (e:=e). all:assumption. }
           (* ~InAtt a A' -> forall e, ~ In (ae a e) A' *)
           assert (HnInA'e': ~ In (ae a' e') A'). 
           { rewrite InAtt_In_exfexp in HnInAttA'. 
             apply not_ex_all_not with (n:=e') in HnInAttA'. auto. }
           (* ~ In a A /\ ~ In a A' -> ~ In a (A U A') *)
           pose (conj HnInAe' HnInA'e') as HnInAUA'.
           rewrite (notIn_set_union vatt_eq_dec) in HnInAUA'.
           (* ~ In a A -> set_add a A =va= (a::A) *)
           apply (notIn_set_add_equiv_vatts) in HnInAUA' as Hsetadd.
           apply extract_equiv with (a:=a) in Hsetadd. rewrite Hsetadd.
           
           (* rewrite IHA' *)
           
           destruct (string_eq_dec a a') as [Heq|Heq]; subst.
           { simpl. repeat(rewrite simpl_extract_eq). 
             simpl. rewrite IH.
             rewrite (notInAtt_extract _ _ HnInAttA').
             rewrite (In_extract _ _ HA HInA).  simpl.
             repeat( rewrite orb_false_r). apply orb_comm.
           }
           { simpl. repeat(rewrite (simpl_extract_neq _ _ Heq)).
             apply IH. 
           }
           

    ++ (* ~InAtt a A *)
       (* rewrite set_add *)

       (* ~InAtt a A -> forall e, ~ In (ae a e) A *)
       assert (HnInAe': ~ In (ae a' e') A). 
       { rewrite InAtt_In_exfexp in HnInAttA. 
         apply not_ex_all_not with (n:=e') in HnInAttA. auto. }
       (* ~InAtt a A' -> forall e, ~ In (ae a e) A' *)
       assert (HnInA'e': ~ In (ae a' e') A'). 
       { rewrite InAtt_In_exfexp in HnInAttA'. 
         apply not_ex_all_not with (n:=e') in HnInAttA'. auto. }
       (* ~ In a A /\ ~ In a A' -> ~ In a (A U A') *)
       pose (conj HnInAe' HnInA'e') as HnInAUA'.
       rewrite (notIn_set_union vatt_eq_dec) in HnInAUA'.
       (* ~ In a A -> set_add a A =va= (a::A) *)
       apply (notIn_set_add_equiv_vatts) in HnInAUA' as Hsetadd.
       apply extract_equiv with (a:=a) in Hsetadd. rewrite Hsetadd.
       

       (* rewrite IHA' *)
        
        destruct (string_eq_dec a a') as [Heq|Heq]; subst.
       { simpl. repeat(rewrite simpl_extract_eq). 
         simpl. rewrite IH.
         rewrite (notInAtt_extract _ _ HnInAttA).
         rewrite (notInAtt_extract _ _ HnInAttA').
         simpl.
         repeat( rewrite orb_false_r). reflexivity.
       }
       { simpl. repeat(rewrite (simpl_extract_neq _ _ Heq)).
         apply IH.
       }
Qed.


(* -- set_union set_intersection nil_l nil_r -- *)

(* nil lemmas should hold for equality,
   but proving equiv is easier and should be enough for us. *)

Lemma atts_union_nil_r: forall A, atts_union A [] =a= A.
Proof. intros. simpl. reflexivity. Qed.

(* atts_union use set_add; thus bag(Dup) A will become set A on LHS*)
Lemma atts_union_nil_l: forall A (H: NoDup A), atts_union [] A =a= A.
Proof. intros. unfold atts_union. unfold equiv_atts.
 intro a. split. split.
 - rewrite set_union_iff. simpl. intro.
   destruct H0. destruct H0. auto.
 - intro H0. rewrite set_union_iff. eauto.
 - pose (NoDup_nil att) as Hnil. 
   pose (set_union_nodup string_eq_dec Hnil H) as Hndp.
   destruct (in_dec string_eq_dec a A).
   + apply (set_union_intro2 string_eq_dec) with (x:=[]) in i as HsetU.
     rewrite NoDup_count_occ' in Hndp, H.
     rewrite Hndp, H. 
     reflexivity. exact i. exact HsetU. 
   + assert (n':~ In a []). simpl. unfold not. eauto.
     pose (conj n' n) as Hnn'.
     rewrite notIn_set_union in Hnn'. 
     rewrite count_occ_not_In in n, Hnn'.
     rewrite n, Hnn'. reflexivity.
Qed.



Lemma atts_inter_nil_r: forall A, atts_inter A [] = [].
Proof. intro A. induction A. simpl. reflexivity. simpl.
       assumption.
Qed.

Lemma atts_inter_nil_l: forall A, atts_inter [] A = [].
Proof. intros. simpl. reflexivity. Qed.


Lemma vatts_union_nil_r : forall A (H: NoDupAtt A), vatts_union A [] = A.
Proof. intro A. 
intro H. unfold vatts_union. simpl. 
apply nodupatt_fixed_point. auto.
Qed.


Lemma vatts_union_nil_l : forall A (H: NoDupAtt A), vatts_union [] A =va= A.
Proof. 
induction A. simpl. 
reflexivity. simpl.  
intro H.
unfold vatts_union.
simpl. destruct a as (a, e).
(* get ~ In a set_union from context and rewrite set_add *)
pose (NoDupAtt_NoDup H) as Hnodup.
inversion Hnodup; subst.
apply (contrapositive _ _ (set_union_emptyL vatt_eq_dec (ae a e) A)) in H2.
unfold set_In in H2. 
pose (notIn_set_add_equiv_vatts (ae a e) (set_union vatt_eq_dec [] A)) as Hset_add.
rewrite (nodupatt_equiv (Hset_add (H2))).
clear Hnodup.
(* get ~ InAtt a set_union from context and rewrite nodupatt *)
inversion H; subst.
assert(HInnil: ~ InAtt a []). simpl. eauto.
pose (conj HInnil H4) as H4'. 
apply (notInAtt_set_union a [] A) in H4'.
pose nodupatt_not_in_cons as Hcons.
apply (Hcons a e ((set_union vatt_eq_dec [] A))) in H4'.
rewrite H4'.
apply IHA in H6.
unfold vatts_union in H6.
apply cons_equiv_vatts. assumption.
Qed.

Lemma vatts_inter_nil_r : forall A, vatts_inter A [] = [].
Proof. intro A. induction A as [|(a, e)]. reflexivity.
       rewrite vatts_inter_equation. simpl.  
       assumption. Qed. 

Lemma vatts_inter_nil_l : forall A, vatts_inter [] A = [].
Proof. intros. rewrite vatts_inter_equation. simpl. reflexivity. Qed.

Lemma atts_inter_nil_l_equiv A B (HA: NoDup A) (HB: NoDup B): A =a= [] ->
atts_inter A B =a= []. 
Proof. intro H. rewrite set_inter_equiv with (B:=[]) (B':=B).
rewrite atts_inter_nil_l. try reflexivity.
all: try (assumption); try (apply (NoDup_nil)). reflexivity.
Qed.

Lemma atts_inter_nil_r_equiv A B (HA: NoDup A) (HB: NoDup B): B =a= [] ->
atts_inter A B =a= []. 
Proof. intro H. rewrite set_inter_equiv with (B:=A) (B':=[]).
rewrite atts_inter_nil_r. try reflexivity.
all: try (assumption); try (apply (NoDup_nil)). reflexivity.
Qed.

Lemma vatts_inter_notIn A B x ex: ~InAtt x A -> 
 vatts_inter A (ae x ex::B) = vatts_inter A B.
Proof. induction A as [|(a, e)].
- intros. rewrite vatts_inter_nil_l. reflexivity.
- intros. simpl. 
rewrite vatts_inter_equation. symmetry.
rewrite vatts_inter_equation. symmetry. simpl. 
unfold eqbAtt. simpl. simpl in H.
rewrite not_or_and_not in H.
destruct H.
simpl. destruct (string_beq a x) eqn:Hxa.
 rewrite stringDecF.eqb_eq in Hxa.
contradiction. simpl. destruct (existsbAtt a B).
rewrite IHA. Search extract_e.
rewrite simpl_extract_neq. reflexivity.
all: (try eauto). Qed. 

Lemma vatts_inter_pres : forall A (H: NoDupAtt A), vatts_inter A A =va= A.
Proof. intro A. induction A as [|(a, e)]. reflexivity.
intro H.
inversion H; subst. 
rewrite vatts_inter_equation. 
 simpl. unfold eqbAtt. simpl.
rewrite stringBEF.eqb_refl. simpl.
rewrite simpl_extract_eq. apply notInAtt_extract in H2 as H2e.
rewrite H2e.  eapply vatts_inter_notIn in H2.
rewrite H2. unfold equiv_vatts. intro c.
unfold configVAttSet; fold configVAttSet.
simpl. 
rewrite orb_false_r.
destruct (E[[ e]]c); simpl. 
apply cons_equiv_atts. unfold equiv_vatts in IHA.
all: apply (IHA H4).
Qed.

(* if not NoDupAtt B then replace In (ae a e') B with e' := extract_e a B *)
Lemma vatts_inter_elemchc_more_specific: forall x e e' A B (HndpB: NoDupAtt B),
In (ae x e) (vatts_inter A B) -> In (ae x e') B -> forall c,
((E[[ e]]c) = true  -> (E[[ e']]c) = true).
Proof. induction A as [|(a, ea) A].
- simpl. intros. destruct H.
- intros B HndpB HInAB HInB c He.
+ rewrite vatts_inter_equation in *.
unfold eqbAtt in *. simpl in *.
destruct (existsbAtt a B) eqn: HInAttaB.
++ simpl in HInAB. destruct HInAB as [Heq | HInAB].
{ inversion Heq; subst. apply (In_extract _ _ HndpB) in HInB.
simpl in He. rewrite andb_true_iff in He.
destruct He as [He1 He2].
rewrite HInB in He2. simpl in He2. 
rewrite orb_false_r in He2. assumption. }
{ apply (IHA B HndpB HInAB HInB) with (c:= c) in He. assumption. } 
++ apply (IHA B HndpB HInAB HInB) with (c:= c) in He. assumption.
Qed.

Lemma vatts_inter_simpl A B:
vatts_inter (vatts_inter A B) B =va= vatts_inter A B. 
Proof. induction A.
- repeat (rewrite vatts_inter_nil_l).
reflexivity.
- destruct B.
simpl. repeat (rewrite vatts_inter_nil_r).
reflexivity. destruct a as (a', e').
destruct (existsbAtt a' (v :: B)) eqn:Ha'.
rewrite vatts_inter_equation. 
destruct (vatts_inter (ae a' e' :: A) (v :: B)) eqn:Ha'AvB.
reflexivity.
destruct v0 as (a0, e0).
rewrite vatts_inter_equation in Ha'AvB. 
rewrite Ha' in Ha'AvB. 
inversion Ha'AvB; subst.
rewrite Ha'. simpl. unfold equiv_vatts.
intro c. simpl. 
destruct ((E[[ e']] c) && (E[[ extract_e a0 (v :: B)]] c) &&
  (E[[ extract_e a0 (v :: B)]] c)) eqn:Hes;
rewrite <- andb_assoc in Hes; rewrite andb_diag in Hes;
rewrite Hes; try( apply cons_equiv_atts);
unfold equiv_vatts in IHA; auto.

assert (Hsimp: vatts_inter (ae a' e' :: A) (v :: B) = vatts_inter A (v :: B)).
{ rewrite vatts_inter_equation. rewrite Ha'. reflexivity. }

rewrite Hsimp. apply IHA.
Qed.

Lemma atts_inter_simpl A B:
atts_inter (atts_inter A B) B =a= atts_inter A B. 
Proof. induction A.
- repeat (rewrite atts_inter_nil_l). reflexivity.
- simpl. destruct (set_mem string_eq_dec a B) eqn:H. 
+ simpl. rewrite H. apply cons_equiv_atts. auto.
+ auto.
Qed.





