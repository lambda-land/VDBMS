(** lemmas for set OP *)
Set Warnings "-notation-overridden,-parsing".


Load ElemOPVelem.

(* Push_annot velems_inter *)

(*Lemma dist_push_annot_velems_inter A B e:
velems_inter (push_annot A e) (push_annot B e)
= push_annot (velems_inter A B) e.
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

Lemma set_remove_config: forall a A c (H: NoDupElem A), 
      set_remove string_eq_dec a (configVElemSet A c) 
      = configVElemSet (removeElem a A) c.
Proof. intros a A c.
induction A; intro H.
 simpl. reflexivity.
- inversion H; subst. simpl.
  destruct (E[[ e]] c) eqn:He.
  + simpl. destruct (string_eq_dec a a1).
    ++ rewrite e0. rewrite stringBEF.eqb_refl.
       rewrite (notInElem_removeElem_eq _ _ H2). reflexivity.
    ++ rewrite <- stringBEF.eqb_neq in n. 
       rewrite n. simpl. rewrite He. rewrite (IHA H3).
       reflexivity.
  + destruct (string_beq a a1). 
    ++ eauto.
    ++ simpl. rewrite He. eauto.
Qed.


(* -- In config set_add -- *)
Lemma config_set_add_equiv_elems_true a f c A: ~ In (ae a f) A -> (E[[ f]]c) = true ->
configVElemSet (set_add velem_eq_dec (ae a f) A) c =set=  (a :: (configVElemSet A c)).
Proof. induction A.
- intros. simpl. rewrite H0. reflexivity.
- intros. simpl in H. apply Classical_Prop.not_or_and in H.
destruct H. simpl set_add. 
destruct (velem_eq_dec (ae a f) a0) eqn: Heq.
++ destruct H. eauto.
++ destruct a0 as (a0, e0).
   simpl configVElemSet. apply (IHA H1) in H0.
   destruct (E[[ e0]] c) eqn: He0.
   +++ rewrite (cons_equiv_elems a0 H0).
       apply equiv_irres_order.
   +++ assumption.
Qed.


Lemma config_set_add_equiv_elems_false a f c A: ~ In (ae a f) A -> (E[[ f]]c) = false ->
configVElemSet (set_add velem_eq_dec (ae a f) A) c =set=  (configVElemSet A c).
Proof. induction A.
- intros. simpl. rewrite H0. reflexivity.
- intros. simpl in H. apply Classical_Prop.not_or_and in H.
destruct H. simpl set_add. 
destruct (velem_eq_dec (ae a f) a0) eqn: Heq.
++ reflexivity.
++ destruct a0 as (a0, e0).
   simpl configVElemSet. apply (IHA H1) in H0.
   destruct (E[[ e0]] c) eqn: He0.
   +++ rewrite (cons_equiv_elems a0 H0).
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

Lemma notIn_set_add_equiv_elems a A:
         ~ In a A -> (set_add string_eq_dec a A) =set= (a::A) .
Proof. unfold equiv_elems. intros Ha a0. split.
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


Lemma notIn_set_add_equiv_velems a A: ~ In a A -> 
      (set_add velem_eq_dec a A) =vset= (a::A) .
Proof. unfold equiv_velems. destruct a as (a, e).
intros H c. simpl configVElemSet. destruct (E[[ e]]c) eqn: He.
+ apply (config_set_add_equiv_elems_true _ _ _ _ H He). 
+ apply (config_set_add_equiv_elems_false _ _ _ _ H He). 
Qed.

(* -- In set_add remove  -- *)
Lemma In_set_add_remove: forall a A (HA: NoDup A), 
       In a A ->  
       set_add string_eq_dec a (set_remove string_eq_dec a A) =set= A.
Proof. intros. unfold equiv_elems. intro.
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
       set_add string_eq_dec a A =set= 
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

(* -- InElem set_union -- *)

Lemma InElem_set_union: forall a A A', 
    InElem a (set_union velem_eq_dec A A') <-> InElem a A \/ InElem a A'.
Proof. intros. split.
- intro H. rewrite InElem_In_exfexp in H.
  destruct H as [e H]. apply set_union_iff in H.
  destruct H.
  + left. rewrite InElem_In_exfexp. 
    exists e. auto.
  + right. rewrite InElem_In_exfexp. 
    exists e. auto.
- intro H. destruct H; 
  rewrite InElem_In_exfexp in H;
  destruct H as [e H]; 
  rewrite InElem_In_exfexp; 
  exists e; apply set_union_iff;
  eauto.
Qed.
  
  
Lemma notInElem_set_union: forall a A A',
 (~ InElem a A /\ ~ InElem a A') <-> ~ InElem a (set_union velem_eq_dec A A').
Proof. intros a A A'.
pose (contrapositive_iff _ _(InElem_set_union a A A')) as H.
rewrite not_or_and_not in H.
exact H.
Qed.


Lemma notInElem_velems_inter a A B: 
~ InElem a A -> ~ InElem a (velems_inter A B).
Proof. apply velems_inter_ind. 
- intros. auto.
-  intros. apply H. simpl in H0.
rewrite not_or_and_not in H0. destruct H0. auto.
- intros. simpl. simpl in H0.
rewrite not_or_and_not in H0. 
rewrite not_or_and_not. destruct H0. split.
all: auto. Qed.


Lemma notInElemB_velems_inter a A B: 
~ InElem a B -> ~ InElem a (velems_inter A B).
Proof. apply velems_inter_ind. 
- intros. auto.
-  intros. apply H. simpl in H0.
auto.
- intros. simpl. simpl in H0.
rewrite not_or_and_not. split.
rewrite <- existsbElem_InElem in H0.
unfold not; intro. rewrite <- H1 in H0.
rewrite e1 in H0. contradiction.
apply H in H0. assumption. Qed.


Lemma InElem_velems_inter a A B: 
InElem a (velems_inter A B) -> InElem a A /\ InElem a B.
Proof. intro H. split;
[ pose (contrapositive _ _ (notInElem_velems_inter a A B))  as HInA 
| pose (contrapositive _ _ (notInElemB_velems_inter a A B)) as HInA ];
apply Classical_Prop.NNPP; eauto. 
Qed.

Lemma InElem_velems_inter_2 a A B: 
 (InElem a A /\ InElem a B) -> InElem a (velems_inter A B).
Proof. apply velems_inter_ind. 
- intros. destruct H. auto.
- intros. apply H. simpl in H0.
 destruct H0. destruct H0. rewrite H0 in *. 
rewrite <- existsbElem_InElem in H1. rewrite e1 in H1. discriminate H1. auto.
- intros. simpl. simpl in H0.
destruct H0. destruct H0. left. auto. right. apply H. auto.
Qed.

Lemma InElem_velems_inter_rewrite a A B: 
InElem a (velems_inter A B) <-> InElem a A /\ InElem a B.
Proof. split. apply InElem_velems_inter.
apply InElem_velems_inter_2. Qed.

Lemma In_velems_inter_existsAB a e A B: 
In (ae a e) (velems_inter A B) -> 
(exists e', In (ae a e') A ) /\
(exists e', In (ae a e') B ).
Proof. intro H.
apply In_InElem_fstVelem in H.
simpl in H.
rewrite InElem_velems_inter_rewrite in H.
destruct H as [HA HB].
split;
[ rewrite InElem_In_exfexp in HA |
rewrite InElem_In_exfexp in HB ]; auto.
Qed.


Lemma In_velems_inter a e c A B: 
In (ae a e) (velems_inter A B) /\ (E[[ e]]c) = true -> 
exists e', In (ae a e') B /\ (E[[ e']]c) = true.
Proof. apply velems_inter_ind; intros.
- destruct H. destruct H. 
- apply H. eauto.
- (* get_annot a A' -> In a X[[A]]c -> goal *) destruct H0.
destruct H0 as [Heq | HIn]. inversion Heq; subst.
simpl in H1. rewrite andb_true_iff in H1.
destruct H1 as [He0 He']. apply get_annot_true_In in He' as HInElem.
rewrite <- In_config_exists_true in HInElem. auto.
apply H. eauto.

(*induction A; intros. destruct H. simpl in H.
destruct H.
destruct H. rewrite velems_inter_equation in H.
destruct a0. destruct (existsbElem a0 B) eqn:Hex.
simpl in H. destruct H.  inversion H; subst.
simpl in H0. rewrite andb_true_iff in H0.
destruct H0. apply get_annot_true_In in H1 as HInElem. 
rewrite <- In_config_exists_true in HInElem. auto.
apply IHA. eauto. 
apply IHA. eauto.*)
Qed.

Lemma In_velems_inter_A a e c A B: 
In (ae a e) (velems_inter A B) /\ (E[[ e]]c) = true -> 
exists e', In (ae a e') A /\ (E[[ e']]c) = true.
Proof. apply velems_inter_ind; intros.
- destruct H. destruct H. 
- apply H in H0. destruct H0 as [e' [ HIne' He' ] ].
exists e'. split; try eauto. apply in_cons. auto.
- (* get_annot a A' -> In a X[[A]]c -> goal *) destruct H0.
destruct H0 as [Heq | HIn]. inversion Heq; subst.
exists e0. split. simpl. left. auto.
simpl in H1. rewrite andb_true_iff in H1.
destruct H1 as [He0 He']. auto.
assert(H0: In (ae a e) (velems_inter As A') /\ E[[ e]] c = true).
eauto. apply H in H0. destruct H0 as [e'' [ HIne' He'' ] ].
exists e''. split; try eauto. apply in_cons. auto.
Qed.

Lemma In_velems_inter_AB a e c A B: 
In (ae a e) (velems_inter A B) /\ (E[[ e]]c) = true -> 
(exists e', In (ae a e') A /\ (E[[ e']]c) = true) /\
(exists e', In (ae a e') B /\ (E[[ e']]c) = true).
Proof.
intros. split.
eapply In_velems_inter_A. eauto.
eapply In_velems_inter. eauto.
Qed.

Lemma set_add_equiv: forall a A A',
A=set=A' -> set_add string_eq_dec a A =set= set_add string_eq_dec a A'.
Proof. intros a A A'.
intro H. unfold equiv_elems in H.
unfold equiv_elems. intro a0.
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
A=set=A' -> set_remove string_eq_dec a A =set= set_remove string_eq_dec a A'.
Proof. intros a A A' HA HA'.
intro H. unfold equiv_elems in H.
unfold equiv_elems. intro a0.
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
A=set=B -> A'=set=B' -> set_union string_eq_dec A A' =set= set_union string_eq_dec B B'.
Proof.
intros H1 H2. unfold equiv_elems in H1, H2.
unfold equiv_elems. intro a0.
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
A=set=B -> A'=set=B' -> set_inter string_eq_dec A A' =set= set_inter string_eq_dec B B'.
Proof.
intros H1 H2. unfold equiv_elems in H1, H2.
unfold equiv_elems. intro a0.
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
A=set=B -> A'=set=B' -> is_disjoint_bool A A' = is_disjoint_bool B B'.
Proof. intros. unfold is_disjoint_bool.
pose (set_inter_equiv HA HA' HB HB' H H0) as Hinter.
destruct (elems_inter A A') eqn: HAA'; unfold elems_inter;
unfold elems_inter in HAA'; rewrite HAA' in Hinter;
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
     In a A'-> A =qtype= set_remove string_eq_dec a A' <->
               (a :: A) =qtype= A'.
Proof. intros H1. split; intro H;
unfold equiv_qtype; unfold equiv_qtype in H;
unfold equiv_elems;  unfold equiv_elems in H;
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



Lemma set_union_velems_nil_l: forall A (H: NoDup A), 
          set_union velem_eq_dec [] A =vset= A.
Proof. induction A. simpl. 
reflexivity. simpl.  
intro H.
unfold velems_union.
simpl. destruct a as (a, e).
(* get ~ In a set_union from context and rewrite set_add *)
inversion H; subst.
apply (contrapositive _ _ (set_union_emptyL velem_eq_dec (ae a e) A)) in H2.
unfold set_In in H2. 
pose (notIn_set_add_equiv_velems (ae a e) (set_union velem_eq_dec [] A)) as Hset_add.
rewrite Hset_add. 
apply cons_equiv_velems. apply IHA.
all:assumption.
Qed.

Lemma  get_annot_set_union: forall a A A' c (HA: NoDupElem A) (HA': NoDupElem A'),
      (E[[ get_annot a (set_union velem_eq_dec A A')]]c) 
         = (E[[ (get_annot a A \/(F) get_annot a A')]]c).
Proof. (*intros a A A'. generalize dependent a.*)
 induction A' as [|a' A' IHA']; intros.
- simpl. rewrite orb_false_r. reflexivity.
- destruct a' as (a', e').
  inversion HA' as [|a'' e'' A'' HnInElemA' HNdpElemA'] ; subst.
  (* destruct (string_eq_dec a' a); subst.
  + simpl. rewrite simpl_get_annot_eq. *)
    specialize IHA' with c. pose  (IHA' HA HNdpElemA') as IH.
    destruct (InElem_dec a' A) as [HInElemA | HnInElemA].
    ++ (* InElem a A *) 
       rewrite InElem_In_exfexp in HInElemA.
       destruct HInElemA as [e HInA].
       destruct (fexp_eq_dec e e'); subst.
       +++ (* e = e' -> In (ae a e') A *)
           simpl. 
           (* rewrite set_add *)
           apply (set_union_intro1 velem_eq_dec) with (y:=A') 
           in HInA as HInAUA'. 
           apply (In_set_add velem_eq_dec ) in HInAUA' as Hsetadd.
           rewrite Hsetadd. 
           simpl in IHA'. 
           (* rewrite IH *)
           rewrite IH. 
           destruct (string_eq_dec a a') as [Heq|Heq]; subst.
           { simpl. rewrite simpl_get_annot_eq.
             rewrite (notInElem_get_annot _ _ HnInElemA').
             rewrite (In_get_annot _ _ HA HInA).  simpl.
             repeat( rewrite orb_false_r). 
             rewrite orb_diag. reflexivity.
           }
           { simpl. rewrite (simpl_get_annot_neq _ _ Heq).
             reflexivity.
           }
       
       +++ (* e <> e' -> In (ae a e) A *)
           (* rewrite set_add *)
           assert (HnInAe': ~ In (ae a' e') A). 
           { apply NoDupElem_In_notIn with (e:=e). all:assumption. }
           (* ~InElem a A' -> forall e, ~ In (ae a e) A' *)
           assert (HnInA'e': ~ In (ae a' e') A'). 
           { rewrite InElem_In_exfexp in HnInElemA'. 
             apply not_ex_all_not with (n:=e') in HnInElemA'. auto. }
           (* ~ In a A /\ ~ In a A' -> ~ In a (A U A') *)
           pose (conj HnInAe' HnInA'e') as HnInAUA'.
           rewrite (notIn_set_union velem_eq_dec) in HnInAUA'.
           (* ~ In a A -> set_add a A =vset= (a::A) *)
           apply (notIn_set_add_equiv_velems) in HnInAUA' as Hsetadd.
           apply get_annot_equiv with (a:=a) in Hsetadd. rewrite Hsetadd.
           
           (* rewrite IHA' *)
           
           destruct (string_eq_dec a a') as [Heq|Heq]; subst.
           { simpl. repeat(rewrite simpl_get_annot_eq). 
             simpl. rewrite IH.
             rewrite (notInElem_get_annot _ _ HnInElemA').
             rewrite (In_get_annot _ _ HA HInA).  simpl.
             repeat( rewrite orb_false_r). apply orb_comm.
           }
           { simpl. repeat(rewrite (simpl_get_annot_neq _ _ Heq)).
             apply IH. 
           }
           

    ++ (* ~InElem a A *)
       (* rewrite set_add *)

       (* ~InElem a A -> forall e, ~ In (ae a e) A *)
       assert (HnInAe': ~ In (ae a' e') A). 
       { rewrite InElem_In_exfexp in HnInElemA. 
         apply not_ex_all_not with (n:=e') in HnInElemA. auto. }
       (* ~InElem a A' -> forall e, ~ In (ae a e) A' *)
       assert (HnInA'e': ~ In (ae a' e') A'). 
       { rewrite InElem_In_exfexp in HnInElemA'. 
         apply not_ex_all_not with (n:=e') in HnInElemA'. auto. }
       (* ~ In a A /\ ~ In a A' -> ~ In a (A U A') *)
       pose (conj HnInAe' HnInA'e') as HnInAUA'.
       rewrite (notIn_set_union velem_eq_dec) in HnInAUA'.
       (* ~ In a A -> set_add a A =vset= (a::A) *)
       apply (notIn_set_add_equiv_velems) in HnInAUA' as Hsetadd.
       apply get_annot_equiv with (a:=a) in Hsetadd. rewrite Hsetadd.
       

       (* rewrite IHA' *)
        
        destruct (string_eq_dec a a') as [Heq|Heq]; subst.
       { simpl. repeat(rewrite simpl_get_annot_eq). 
         simpl. rewrite IH.
         rewrite (notInElem_get_annot _ _ HnInElemA).
         rewrite (notInElem_get_annot _ _ HnInElemA').
         simpl.
         repeat( rewrite orb_false_r). reflexivity.
       }
       { simpl. repeat(rewrite (simpl_get_annot_neq _ _ Heq)).
         apply IH.
       }
Qed.


(* -- set_union set_intersection nil_l nil_r -- *)

(* nil lemmas should hold for equality,
   but proving equiv is easier and should be enough for us. *)

Lemma elems_union_nil_r: forall A, elems_union A [] =set= A.
Proof. intros. simpl. reflexivity. Qed.

(* elems_union use set_add; thus bag(Dup) A will become set A on LHS*)
Lemma elems_union_nil_l: forall A (H: NoDup A), elems_union [] A =set= A.
Proof. intros. unfold elems_union. unfold equiv_elems.
 intro a. split. split.
 - rewrite set_union_iff. simpl. intro.
   destruct H0. destruct H0. auto.
 - intro H0. rewrite set_union_iff. eauto.
 - pose (NoDup_nil elem) as Hnil. 
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



Lemma elems_inter_nil_r: forall A, elems_inter A [] = [].
Proof. intro A. induction A; eauto. Qed.

Lemma elems_inter_nil_l: forall A, elems_inter [] A = [].
Proof. eauto. Qed.


Lemma velems_union_nil_r : forall A (H: NoDupElem A), velems_union A [] = A.
Proof. intro A. 
intro H. unfold velems_union. simpl. 
apply nodupelem_fixed_point. auto.
Qed.


Lemma velems_union_nil_l : forall A (H: NoDupElem A), velems_union [] A =vset= A.
Proof. 
induction A. simpl. 
reflexivity. simpl.  
intro H.
unfold velems_union.
simpl. destruct a as (a, e).
(* get ~ In a set_union from context and rewrite set_add *)
pose (NoDupElem_NoDup H) as Hnodup.
inversion Hnodup; subst.
apply (contrapositive _ _ (set_union_emptyL velem_eq_dec (ae a e) A)) in H2.
unfold set_In in H2. 
pose (notIn_set_add_equiv_velems (ae a e) (set_union velem_eq_dec [] A)) as Hset_add.
rewrite (nodupelem_equiv (Hset_add (H2))).
clear Hnodup.
(* get ~ InElem a set_union from context and rewrite nodupelem *)
inversion H; subst.
assert(HInnil: ~ InElem a []). simpl. eauto.
pose (conj HInnil H4) as H4'. 
apply (notInElem_set_union a [] A) in H4'.
pose nodupelem_not_in_cons as Hcons.
apply (Hcons a e ((set_union velem_eq_dec [] A))) in H4'.
rewrite H4'.
apply IHA in H6.
unfold velems_union in H6.
apply cons_equiv_velems. assumption.
Qed.

Lemma velems_inter_nil_r : forall A, velems_inter A [] = [].
Proof. intro A. induction A as [|(a, e)]. reflexivity.
       rewrite velems_inter_equation. simpl.  
       assumption. Qed. 

Lemma velems_inter_nil_l : forall A, velems_inter [] A = [].
Proof. intros. rewrite velems_inter_equation. simpl. reflexivity. Qed.

Lemma elems_inter_nil_l_equiv A B (HA: NoDup A) (HB: NoDup B): A =set= [] ->
elems_inter A B =set= []. 
Proof. intro H. rewrite set_inter_equiv with (B:=[]) (B':=B).
rewrite elems_inter_nil_l. try reflexivity.
all: try (assumption); try (apply (NoDup_nil)). reflexivity.
Qed.

Lemma elems_inter_nil_r_equiv A B (HA: NoDup A) (HB: NoDup B): B =set= [] ->
elems_inter A B =set= []. 
Proof. intro H. rewrite set_inter_equiv with (B:=A) (B':=[]).
rewrite elems_inter_nil_r. try reflexivity.
all: try (assumption); try (apply (NoDup_nil)). reflexivity.
Qed.

Lemma velems_inter_notIn A B x ex: ~InElem x A -> 
 velems_inter A (ae x ex::B) = velems_inter A B.
Proof. induction A as [|(a, e)].
- intros. rewrite velems_inter_nil_l. reflexivity.
- intros. simpl. 
rewrite velems_inter_equation. symmetry.
rewrite velems_inter_equation. symmetry. simpl. 
unfold eqbElem. simpl. simpl in H.
rewrite not_or_and_not in H.
destruct H.
simpl. destruct (string_beq a x) eqn:Hxa.
 rewrite stringDecF.eqb_eq in Hxa.
contradiction. simpl. destruct (existsbElem a B).
rewrite IHA. Search get_annot.
rewrite simpl_get_annot_neq. reflexivity.
all: (try eauto). Qed. 

Lemma velems_inter_pres : forall A (H: NoDupElem A), velems_inter A A =vset= A.
Proof. intro A. induction A as [|(a, e)]. reflexivity.
intro H.
inversion H; subst. 
rewrite velems_inter_equation. 
 simpl. unfold eqbElem. simpl.
rewrite stringBEF.eqb_refl. simpl.
rewrite simpl_get_annot_eq. apply notInElem_get_annot in H2 as H2e.
rewrite H2e.  eapply velems_inter_notIn in H2.
rewrite H2. unfold equiv_velems. intro c.
unfold configVElemSet; fold configVElemSet.
simpl. 
rewrite orb_false_r.
destruct (E[[ e]]c); simpl. 
apply cons_equiv_elems. unfold equiv_velems in IHA.
all: apply (IHA H4).
Qed.

(* if not NoDupElem B then replace In (ae a e') B with e' := get_annot a B *)
Lemma velems_inter_elemchc_more_specific: forall x e e' A B (HndpB: NoDupElem B),
In (ae x e) (velems_inter A B) -> In (ae x e') B -> (forall c,
((E[[ e]]c) = true  -> (E[[ e']]c) = true)).
Proof. induction A as [|(a, ea) A].
- simpl. intros. destruct H.
- intros B HndpB HInAB HInB c He.
+ rewrite velems_inter_equation in *.
unfold eqbElem in *. simpl in *.
destruct (existsbElem a B) eqn: HInElemaB.
++ simpl in HInAB. destruct HInAB as [Heq | HInAB].
{ inversion Heq; subst. apply (In_get_annot _ _ HndpB) in HInB.
simpl in He. rewrite andb_true_iff in He.
destruct He as [He1 He2].
rewrite HInB in He2. simpl in He2. 
rewrite orb_false_r in He2. assumption. }
{ apply (IHA B HndpB HInAB HInB) with (c:= c) in He. assumption. } 
++ apply (IHA B HndpB HInAB HInB) with (c:= c) in He. assumption.
Qed.

Lemma velems_inter_elemchc_more_specific_A: forall x e e' A B (HndpB: NoDupElem A),
In (ae x e) (velems_inter A B) -> In (ae x e') A -> (forall c,
((E[[ e]]c) = true  -> (E[[ e']]c) = true)).
Proof. induction A as [|(a, ea) A].
- simpl. intros. destruct H.
- intros B HndpB HInAB HInB c He.
rewrite velems_inter_equation in *.
unfold eqbElem in *. simpl in *.
inversion HndpB; subst. 
destruct (existsbElem a B) eqn: HInElemaB.
+ simpl in HInAB. destruct HInAB as [Heq | HInAB];
[ inversion Heq; subst |  ];
destruct HInB as [Heq' | HInB];
[ inversion Heq'; subst | |
  inversion Heq'; subst |  ].
{ simpl in He. apply andb_true_iff in He. 
destruct He as [He1 He2]. auto. }
{ 
apply In_InElem_fstVelem in HInB.
simpl in HInB. contradiction.
}

{ 
apply In_InElem_fstVelem in HInAB.
simpl in HInAB. rewrite InElem_velems_inter_rewrite in HInAB.
destruct HInAB as [HInA HInB]. contradiction. 
}

{ apply IHA with (B:=B); eauto. }

+ apply not_existsbElem_InElem in HInElemaB.

destruct HInB as [Heq | HInB]. 
inversion Heq; subst. 
apply In_InElem_fstVelem in HInAB.
simpl in HInAB. 
rewrite InElem_velems_inter_rewrite in HInAB.
destruct HInAB as [HInA HInB']. contradiction.
apply IHA with (B:=B); eauto. 

Qed.

Lemma In_velems_inter_equivE x e ea eb A 
(HndpA: NoDupElem A) B (HndpB: NoDupElem B):
In (ae x e) (velems_inter A B) -> In (ae x ea) A ->
In (ae x eb) B ->  e =e= (ea /\(F) eb).
Proof. intros HInAB HInA HInB.
induction A as [|(x', ex') A].
- simpl. intros. destruct HInA.
- 
rewrite velems_inter_equation in HInAB.
inversion HndpA; subst. 
destruct (existsbElem x' B) eqn: HInElemaB.
+ simpl in HInAB. destruct HInAB as [Heq | HInAB];
[ inversion Heq; subst |  ];
destruct HInA as [Heq' | HInA];
[ inversion Heq'; subst | |
  inversion Heq'; subst |  ].
{ apply (In_get_annot _ _ HndpB) in HInB.
rewrite HInB. unfold equivE.
intro c.
simpl. rewrite orb_false_r. reflexivity.
}

{ 
apply In_InElem_fstVelem in HInA.
simpl in HInA. contradiction.
}

{ 
apply In_InElem_fstVelem in HInAB.
simpl in HInAB. rewrite InElem_velems_inter_rewrite in HInAB.
destruct HInAB as [HInA HInB']. contradiction. 
}

{
apply IHA; eauto.
}

+ apply not_existsbElem_InElem in HInElemaB.

destruct HInA as [Heq | HInA]. 
inversion Heq; subst. 
apply In_InElem_fstVelem in HInAB.
simpl in HInAB. 
rewrite InElem_velems_inter_rewrite in HInAB.
destruct HInAB as [HInA' HInB']. contradiction.
apply IHA ; eauto. 

Qed.

Lemma velems_inter_simpl A B:
velems_inter (velems_inter A B) B =vset= velems_inter A B. 
Proof. induction A.
- repeat (rewrite velems_inter_nil_l).
reflexivity.
- destruct B.
simpl. repeat (rewrite velems_inter_nil_r).
reflexivity. destruct a as (a', e').
destruct (existsbElem a' (v :: B)) eqn:Ha'.
rewrite velems_inter_equation. 
destruct (velems_inter (ae a' e' :: A) (v :: B)) eqn:Ha'AvB.
reflexivity.
destruct v0 as (a0, e0).
rewrite velems_inter_equation in Ha'AvB. 
rewrite Ha' in Ha'AvB. 
inversion Ha'AvB; subst.
rewrite Ha'. simpl. unfold equiv_velems.
intro c. simpl. 
destruct ((E[[ e']] c) && (E[[ get_annot a0 (v :: B)]] c) &&
  (E[[ get_annot a0 (v :: B)]] c)) eqn:Hes;
rewrite <- andb_assoc in Hes; rewrite andb_diag in Hes;
rewrite Hes; try( apply cons_equiv_elems);
unfold equiv_velems in IHA; auto.

assert (Hsimp: velems_inter (ae a' e' :: A) (v :: B) = velems_inter A (v :: B)).
{ rewrite velems_inter_equation. rewrite Ha'. reflexivity. }

rewrite Hsimp. apply IHA.
Qed.

Lemma elems_inter_simpl A B:
elems_inter (elems_inter A B) B =set= elems_inter A B. 
Proof. induction A.
- repeat (rewrite elems_inter_nil_l). reflexivity.
- simpl. destruct (set_mem string_eq_dec a B) eqn:H. 
+ simpl. rewrite H. apply cons_equiv_elems. auto.
+ auto.
Qed.





