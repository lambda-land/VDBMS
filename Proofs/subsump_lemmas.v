Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Export List.
Require Export Logic.
Import Coq.Lists.List.ListNotations.

Load AttOPVatt.


Module subsump_lemmas. 

Lemma count_occ_NoDup_0_or_1 {A:Type} eq_dec (l:list A):
  NoDup l <-> forall x, count_occ eq_dec l x = 0 \/ count_occ eq_dec l x = 1.
Proof. split; intros H;
[ intro x; rewrite (NoDup_count_occ eq_dec) in H | 
  rewrite (NoDup_count_occ eq_dec); intro x ];
specialize H with x; Lia.lia. Qed.

Lemma count_occ_ge_0 {A:Type} eq_dec (l:list A) (x:A):
  count_occ eq_dec l x >= 0.
Proof. destruct (in_dec eq_dec x l) as [HInl|HnInl]; 
[rewrite (count_occ_In eq_dec) in HInl |  
 rewrite (count_occ_not_In eq_dec) in HnInl]; Lia.lia. 
Qed.

Lemma nil_subsump_nil: subsump_vatts_exp [] [].
Proof. unfold subsump_vatts_exp. intros x e c [H1 H2].
eauto. Qed.

Lemma forall_cons x e l: (forall c : config, (A[[ ae x e :: l]] c) = []) ->
(forall c : config,  (E[[ e]]c) = false) /\ (forall c : config, (A[[ l]] c) = []).
Proof. intros H. split; intro c; specialize H with c; simpl in H; 
try(destruct (E[[ e]] c); [pose (nil_cons) as Hnil_cons;
specialize Hnil_cons with string x (A[[ l]] c); symmetry in H; contradiction |
auto] ). Qed.

Lemma nilconfig_subsump_nil l: (forall c, A[[ l]]c = []) -> subsump_vatts_exp l [].
Proof. intro H. induction l as [|(x , e)]. apply nil_subsump_nil.
unfold subsump_vatts_exp. apply forall_cons in H. 
destruct H as [He Hl]. apply IHl in Hl. intros x' e' c HIn.
destruct HIn as [HIne Hsat]. simpl in HIne. destruct HIne as [Heq | HIn].
inversion Heq; subst. unfold sat in Hsat. apply PNNP in Hsat. 
rewrite not_true_iff_false in Hsat. specialize He with c. contradiction.
unfold subsump_vatts_exp in Hl.
assert (Hlp: In (ae x' e') l /\ (E[[ e']] c) = true). eauto. apply Hl in Hlp. eauto.
Qed.


(*Lemma not_cons_subsump_nil l: (exists c, A[[ l]]c <> [])
-> ~ subsump_vatts_exp l []. *)
(*Proof. unfold not. intros x l H. destruct H
unfold subsump_vatts_exp in H.
destruct x as (x, e). specialize H with x e. simpl in H. Lia.lia.
reflexivity. Qed. *)

Lemma nil_sublist_nil: sublist [] [].
Proof. unfold sublist. intros x. split; 
[ intro H | simpl ]; eauto. Qed.

Lemma not_cons_sublist_nil: forall x l, ~ sublist (x::l) [].
Proof. unfold not. intros x l H. unfold sublist in H.
specialize H with x. destruct H as [H1 H2]. 
rewrite count_occ_cons_eq in H2. simpl in H2. Lia.lia.
reflexivity. Qed.

Lemma subsump_vatts_correctness A A' {HndpA: NoDupAtt A} {HndpA': NoDupAtt A'}: 
       subsump_vatts_exp A A' <-> (forall c, sublist (configVAttSet A c) (configVAttSet A' c)). 
Proof. split; 
generalize dependent A'; generalize dependent A; 
induction A' as [|(a', ea') A' IHA'];  
intros HndpA' H. 

(*Goals -> :  1: A' := [] , 2: A' := [ae a ' ea':A']*)
1, 2: unfold subsump_vatts_exp in H; unfold sublist; intros c x; 

try (split; (* 1: sublist A []     to 1-1: In A []       1-2: count A [] *)
            (* 2: sublist A [_:A'] to 2-1: In A [_:A'][] 2-2: count A [_:A'][] *)

[ (* 1-1 2-1 In: intro In x A[[A]]c  *) 
  intro HInxA |

  (* 1-2 2-2 count: destruct (count_occ A x) *)
  destruct (count_occ string_eq_dec (A[[ A]] c) x) eqn:Hcount;
  [(* Case 0: count_occ string_eq_dec (A[[ A]] c) x = 0 *)
   (* trivial 0 <= any *) simpl; auto; apply (count_occ_ge_0) |
   
   (* Case Sn: count_occ l x = S n -> HInxA: In x A[[A]]c *) 
   pose (gt_Sn_O n) as HInxA; rewrite <- Hcount in HInxA;  
   rewrite <- count_occ_In in HInxA ]
]); (* 1-1 ->1 , 2-1 -> 2, 2-1 -> 3, 2-2 -> 4*)

(* In x A[[A]]c -> exists e, In (x, e) A /\ E[[e]]c = true *)
rewrite <- In_config_exists_true in HInxA;
destruct HInxA as [e HInxeA];
specialize H with x e c;
(* cereate subsump premise H': In (x,e) A /\ sat e*)
assert (H': In (ae x e) A /\ (E[[ e]] c) = true);
try(auto);
(* get subsump conclusion with H' -> HIne': In (x, e') A' /\ Hsat: e -> e' *)
apply H in H'; destruct H' as [e' He'];
destruct He' as [HIne' Hsat]; simpl in HIne'. 

(* 1, 2: In x [] , count x []
         destruct (In (x, e') []) *)
1, 2: try (destruct HIne'). (* proving 1,2 changes goals# 3->1, 4->2 *)

(* 1, 2: In x [_:A'] , count [_:A'] x *)
1, 2: destruct HInxeA as [HInxeA Hetrue];
(* (E[[ e]] c) = true -> (E[[ e']] c) = true*)
(*rewrite not_sat_not_prop in Hsat;
rewrite <- sat_taut_comp in Hsat; 
specialize  Hsat with c; apply Hsat in Hetrue;*)

(* 1: In x (A[[ ae a' ea' :: A']] c) ->  (x = a' /\ ea' = true) \/ In x A[[A']]c *)
(* 2: count_occ (A[[ ae a' ea' :: A']] c) x ->  
                    [case (x = a' /\ ea' = true): S (count_occ A[[A']]c x) 
                     case  _                    :    count_occ A[[A']]c x *)

(* destruct HIne': (ae a' ea' = ae x e' \/ In (ae x e') A') *) 
try (destruct HIne' as [Heq | Hin]; 

[(* Case Heq: ae a' ea' = ae x e' *) 
 inversion Heq; subst;
 simpl; rewrite Hsat; simpl 
 |
 (* Case HIn: In (ae x e') A'*) (* proves Goal 1 right *)
 
]). (** 1-> 1(Heq), 2(HIn)  2-> 3(Heq), 4(HIn)*)

3, 4: apply NoDupAtt_NoDup_config with (c:=c) in HndpA as Hcount';
rewrite (NoDup_count_occ string_eq_dec) in Hcount'; specialize Hcount' with x; 
assert (Hn: n = 0); try (Lia.lia); rewrite Hn; 

inversion HndpA'; subst; apply notInAtt_notIn_config with (c:=c) in H2;
rewrite (count_occ_not_In string_eq_dec) in H2.

{ (* 1: 1- Case Heq *)left. reflexivity. }
{ (* 2: 1- Case HIn *)simpl. destruct (E[[ ea']] c); try simpl;
                      try right; rewrite <- In_config_exists_true; exists e'; eauto. }

{ (* 3: 2- Case Heq *)case (string_eq_dec x x); intro Hx; [|contradiction]. 
                      Lia.lia. }
{ (* 4: 2- Case HIn *)simpl. destruct (E[[ ea']] c); try simpl; 
                      [ case (string_eq_dec a' x); intro; [ Lia.lia | ] |]; 

                       assert (HInxA': In x (A[[ A']]c));
                       try(rewrite <- In_config_exists_true; exists e'; eauto);
                       rewrite (count_occ_In string_eq_dec) in HInxA'; 
                       apply NoDupAtt_NoDup_config with (c:=c) in H4 as HcountA';
                       rewrite (NoDup_count_occ string_eq_dec) in HcountA'; 
                       specialize HcountA' with x; Lia.lia. }

(* <- *)

(* case []: *)

(** Prove with two facts: sublist (A[[A]]c) [] -> subsump_vatts_exp A [] 
1. forall c, (A[[A]]c)  = [] -> subsump_vatts_exp A []
2. exists c, (A[[A]]c) <> [] -> ~ sublist (A[[A]]c) [] *)

(* introduce (forall c, (A[[A]]c) = []) \/ (exists c, (A[[A]]c) <> []) *)
pose Classical_Prop.classic as Hclassic.
specialize Hclassic with (forall c, (A[[ A]] c) = []).

destruct Hclassic as [Hall | Hexists].

{ (* case 1: forall c, (A[[A]]c) = [] *)
  apply nilconfig_subsump_nil. assumption. }

{ (* case 2: exists c, (A[[A]]c) <> [] *)
  apply not_all_ex_not in Hexists. destruct Hexists as [c Hexists].
  specialize H with c.
  destruct ((A[[ A]] c)) eqn: HAc. contradiction. simpl in H. 
  apply not_cons_sublist_nil in H. destruct H. }

(* case (ae a' ea': A'):  *)
unfold subsump_vatts_exp. intros x e c HInxeA.
destruct HInxeA as[ HInxeA Hsat].
unfold sublist in H. 

specialize H with c x. 
destruct H as [HInxAA' Hcount].
assert (HInxA: In x (A[[A]]c)).
rewrite <- In_config_exists_true. exists e. eauto.
apply HInxAA' in HInxA as HInxA'. simpl in HInxA'.
destruct (E[[ ea']] c) eqn: Hea; 

[ simpl in HInxA';
  destruct HInxA' as [Heq | HInxA'];
  [ exists ea';  inversion Heq; subst; split;
    [simpl; left; reflexivity | auto] | ] | ].

1, 2: rewrite <- In_config_exists_true in HInxA';
destruct HInxA' as [e' HInxA'];
destruct HInxA' as [HInxe'A' He'];
exists e'; split; 
[simpl; right; auto | auto].

Qed.
 

(*================================================*)
   
(*
unfold subsump_vatts_exp in H;  
unfold sublist; intro x;
split;
[ intro HInxA | 
  destruct (count_occ string_eq_dec (A[[ A]] c) x) eqn:Hcount;
  [(* Case 0: count_occ string_eq_dec (A[[ A]] c) x = 0 *)
   simpl; auto |
   (* count_occ l x > 0 -> In x l *) 
   pose (gt_Sn_O n) as HInxA; rewrite <- Hcount in HInxA;  
   rewrite <- count_occ_In in HInxA ]
]; try (apply (count_occ_ge_0)); 
  
rewrite <- In_config_exists_true in HInxA;
destruct HInxA as [e HInxeA];
specialize H with x e;
assert (H': In (ae x e) A /\ sat e);
try(destruct HInxeA; split; auto; exists c; auto);

apply H in H'; destruct H' as [e' He'];
destruct He' as [HIne' Hsat]; simpl in HIne'.*)

(*
rewrite <- In_config_exists_true in HInxA.
destruct HInxA as [e HInxeA].
specialize H with x e. unfold sat at 1 in H.
assert (H': In (ae x e) A /\ (exists c : config, (E[[ e]] c) = true)).
destruct HInxeA. split. auto. exists c. auto.

apply H in H'. destruct H' as [e' He'].
destruct He' as [HIne' Hsat]. simpl in HIne'.
*)


(*
destruct (existsb (stringDecF.eqb x) (A[[ A]] c)) eqn: HIn;
[rewrite existsb_exists in HIn | apply not_true_iff_false in HIn;
rewrite <- (contrapositive_iff _ _ (existsb_exists _ _)) in HIn ].

{ destruct HIn as [x' HIn]; destruct HIn as [HIn Heq].
  rewrite stringDecF.eqb_eq in Heq; rewrite <- Heq in *.
  rewrite <- In_config_exists_true in HIn.
  destruct HIn as [e HIne]. destruct HIne as [HIn He].
  assert (H': In (ae x e) A /\ (exists c : config, (E[[ e]] c) = true)).
     split. auto. exists c. auto.
  apply H in H'. destruct H' as [e' He']. 
  destruct He' as [HIne' Hsat]. simpl in HIne'.
  destruct HIne'.
}
{ apply Classical_Pred_Type.not_ex_all_not with (n:=x) in HIn.
apply Classical_Prop.not_and_or in HIn.
destruct HIn as [HnIn | Hneq].
rewrite (count_occ_not_In string_eq_dec) in HnIn.
rewrite HnIn. simpl. auto. 
rewrite stringBEF.eqb_refl in *. destruct Hneq.
reflexivity.
}

*)




(*Lemma def_equiv (A A': vatts): subsump_vatts_exp A A' <-> subsump_vatts_exp' A A'.
Proof. split; intro H.
unfold subsump_vatts_exp in H.
unfold subsump_vatts_exp'. intros x e c H0.
destruct H0 as [HIn He].
assert (HInsat: In (ae x e) A /\ sat e). 
split; [ | unfold sat; exists c]; auto.
apply H in HInsat. destruct HInsat as [e' HInsatee'].
destruct HInsatee' as [HIne' Hsatee'].
rewrite not_sat_not_prop in Hsatee'. 
rewrite <- sat_taut_comp in Hsatee'.
specialize Hsatee' with c. apply Hsatee' in He.
exists e'. eauto.

unfold subsump_vatts_exp' in H.
unfold subsump_vatts_exp. intros x e H0. 
 

destruct H0 as [HInA Hsat]. unfold sat in Hsat.
destruct Hsat as [c He]. 

assert (HInAe: In (ae x e) A /\ (E[[ e]] c) = true). eauto.
apply H in HInAe as HInA'e'. apply PNNP in HInA'e'.
apply Classical_Prop.NNPP. unfold not at 1 in HInA'e'.
rewrite <- all_ex in HInA'e'.
unfold not at 1.
rewrite <- all_ex. intro Hg.
apply HInA'e'. intro e'. specialize Hg with e'.
apply Classical_Prop.not_and_or in Hg.

destruct Hg as [HInxe'A' | Hnnsat].
apply Classical_Prop.or_not_and. left. assumption.
unfold not at 1 in Hnnsat. unfold sat in Hnnsat.
rewrite <- all_ex in Hnnsat.  

unfold not. intro. apply HInA'e'.

destruct HInA'e' as [e' HInA'e'].
destruct HInA'e' as [HInA' He']. exists e'.
  split. auto. 
intros c' Hec'.
specialize Hsatee' with c. apply Hsatee' in He.
exists e'. eauto. *)





