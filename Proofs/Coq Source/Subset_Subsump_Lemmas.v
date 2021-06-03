Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Export List.
Require Export Logic.
Import Coq.Lists.List.ListNotations.

Load VRA_VarPrsrvtn_Thm.


Module Subset_Subsump_Lemmas. 

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

Lemma nil_subset_nil: subset_velems_exp [] [].
Proof. unfold subset_velems_exp. intros x e c [H1 H2].
eauto. Qed.

Lemma forall_cons x e l: (forall c : config, (X[[ ae x e :: l]] c) = []) ->
(forall c : config,  (E[[ e]]c) = false) /\ (forall c : config, (X[[ l]] c) = []).
Proof. intros H. split; intro c; specialize H with c; simpl in H; 
try(destruct (E[[ e]] c); [pose (nil_cons) as Hnil_cons;
specialize Hnil_cons with string x (X[[ l]] c); symmetry in H; contradiction |
auto] ). Qed.

Lemma nilconfig_subset_nil l: (forall c, X[[ l]]c = []) -> subset_velems_exp l [].
Proof. intro H. induction l as [|(x , e)]. apply nil_subset_nil.
unfold subset_velems_exp. apply forall_cons in H. 
destruct H as [He Hl]. apply IHl in Hl. intros x' e' c HIn.
destruct HIn as [HIne Hsat]. simpl in HIne. destruct HIne as [Heq | HIn].
inversion Heq; subst. unfold sat in Hsat. apply PNNP in Hsat. 
rewrite not_true_iff_false in Hsat. specialize He with c. contradiction.
unfold subset_velems_exp in Hl.
assert (Hlp: In (ae x' e') l /\ (E[[ e']] c) = true). eauto. apply Hl in Hlp. eauto.
Qed.


(*Lemma not_cons_subset_nil l: (exists c, X[[ l]]c <> [])
-> ~ subset_velems_exp l []. *)
(*Proof. unfold not. intros x l H. destruct H
unfold subset_velems_exp in H.
destruct x as (x, e). specialize H with x e. simpl in H. Lia.lia.
reflexivity. Qed. *)

(*Lemma nil_subset_nil: subset [] [].
Proof. unfold subset. intros x. split; 
[ intro H | simpl ]; eauto. Qed.*)

Lemma subset_nil A : subset [] A.
Proof. unfold subset. intros x. split;
[ intro H; destruct H | simpl; Lia.lia ]. Qed.

Lemma not_subset_cons_nil: forall x l, ~ subset (x::l) [].
Proof. unfold not. intros x l H. unfold subset in H.
specialize H with x. destruct H as [H1 H2]. 
rewrite count_occ_cons_eq in H2. simpl in H2. Lia.lia.
reflexivity. Qed.

Theorem subset_velems_correctness A A' (HndpA: NoDupElem A) (HndpA': NoDupElem A'): 
       subset_velems_exp A A' <-> (forall c, subset (X[[ A]]c) (X[[ A']]c)). 
Proof. split; 
generalize dependent A'; generalize dependent A; 
induction A' as [|(a', ea') A' IHA'];  
intros HndpA' H. 

(*Goals -> :  1: A' := [] , 2: A' := [ae a ' ea':A']*)
1, 2: unfold subset_velems_exp in H; unfold subset; intros c x; 

try (split; (* 1: subset A []     to 1-1: In A []       1-2: count A [] *)
            (* 2: subset A [_:A'] to 2-1: In A [_:A'][] 2-2: count A [_:A'][] *)

[ (* 1-1 2-1 In: intro In x X[[A]]c  *) 
  intro HInxA |

  (* 1-2 2-2 count: destruct (count_occ A x) *)
  destruct (count_occ string_eq_dec (X[[ A]] c) x) eqn:Hcount;
  [(* Case 0: count_occ string_eq_dec (X[[ A]] c) x = 0 *)
   (* trivial 0 <= any *) simpl; auto; apply (count_occ_ge_0) |
   
   (* Case Sn: count_occ l x = S n -> HInxA: In x X[[A]]c *) 
   pose (gt_Sn_O n) as HInxA; rewrite <- Hcount in HInxA;  
   rewrite <- count_occ_In in HInxA ]
]); (* 1-1 ->1 , 2-1 -> 2, 2-1 -> 3, 2-2 -> 4*)

(* In x X[[A]]c -> exists e, In (x, e) A /\ E[[e]]c = true *)
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

(* 1: In x (X[[ ae a' ea' :: A']] c) ->  (x = a' /\ ea' = true) \/ In x X[[A']]c *)
(* 2: count_occ (X[[ ae a' ea' :: A']] c) x ->  
                    [case (x = a' /\ ea' = true): S (count_occ X[[A']]c x) 
                     case  _                    :    count_occ X[[A']]c x *)

(* destruct HIne': (ae a' ea' = ae x e' \/ In (ae x e') A') *) 
try (destruct HIne' as [Heq | Hin]; 

[(* Case Heq: ae a' ea' = ae x e' *) 
 inversion Heq; subst;
 simpl; rewrite Hsat; simpl 
 |
 (* Case HIn: In (ae x e') A'*) (* proves Goal 1 right *)
 
]). (** 1-> 1(Heq), 2(HIn)  2-> 3(Heq), 4(HIn)*)

3, 4: apply NoDupElem_NoDup_config with (c:=c) in HndpA as Hcount';
rewrite (NoDup_count_occ string_eq_dec) in Hcount'; specialize Hcount' with x; 
assert (Hn: n = 0); try (Lia.lia); rewrite Hn; 

inversion HndpA'; subst; apply notInElem_notIn_config with (c:=c) in H2;
rewrite (count_occ_not_In string_eq_dec) in H2.

{ (* 1: 1- Case Heq *)left. reflexivity. }
{ (* 2: 1- Case HIn *)simpl. destruct (E[[ ea']] c); try simpl;
                      try right; rewrite <- In_config_exists_true; exists e'; eauto. }

{ (* 3: 2- Case Heq *)case (string_eq_dec x x); intro Hx; [|contradiction]. 
                      Lia.lia. }
{ (* 4: 2- Case HIn *)simpl. destruct (E[[ ea']] c); try simpl; 
                      [ case (string_eq_dec a' x); intro; [ Lia.lia | ] |]; 

                       assert (HInxA': In x (X[[ A']]c));
                       try(rewrite <- In_config_exists_true; exists e'; eauto);
                       rewrite (count_occ_In string_eq_dec) in HInxA'; 
                       apply NoDupElem_NoDup_config with (c:=c) in H4 as HcountA';
                       rewrite (NoDup_count_occ string_eq_dec) in HcountA'; 
                       specialize HcountA' with x; Lia.lia. }

(* <- *)

(* case []: *)

(** Prove with two facts: subset (X[[A]]c) [] -> subset_velems_exp A [] 
1. forall c, (X[[A]]c)  = [] -> subset_velems_exp A []
2. exists c, (X[[A]]c) <> [] -> ~ subset (X[[A]]c) [] *)

(* introduce (forall c, (X[[A]]c) = []) \/ (exists c, (X[[A]]c) <> []) *)
pose Classical_Prop.classic as Hclassic.
specialize Hclassic with (forall c, (X[[ A]] c) = []).

destruct Hclassic as [Hall | Hexists].

{ (* case 1: forall c, (X[[A]]c) = [] *)
  apply nilconfig_subset_nil. assumption. }

{ (* case 2: exists c, (X[[A]]c) <> [] *)
  apply not_all_ex_not in Hexists. destruct Hexists as [c Hexists].
  specialize H with c.
  destruct ((X[[ A]] c)) eqn: HAc. contradiction. simpl in H. 
  apply not_subset_cons_nil in H. destruct H. }

(* case (ae a' ea': A'):  *)
unfold subset_velems_exp. intros x e c HInxeA.
destruct HInxeA as[ HInxeA Hsat].
unfold subset in H. 

specialize H with c x. 
destruct H as [HInxAA' Hcount].
assert (HInxA: In x (X[[A]]c)).
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

Lemma subset_vqtype_correctness X X' {HndpA: NoDupElem (fst X)} {HndpA': NoDupElem (fst X')}: 
       subset_vqtype_exp X X' <-> subset_vqtype X X'. 
Proof.  unfold subset_vqtype_exp, avelems_velems.
rewrite subset_velems_correctness. Search push_annot. 
split; intro. unfold subset_vqtype. intro. 
destruct X as (A, ea). destruct X' as (A', ea').
repeat (rewrite <- configVElemSet_push_annot). apply H.
intro. repeat (rewrite configVElemSet_push_annot).
unfold subset_vqtype in H. destruct X as (A, ea). destruct X' as (A', ea').
simpl fst. simpl snd. apply H. 
all: apply NoDupElem_push_annot; assumption.
Qed.

Lemma subsump_vqtype_equiv A A' B: A =vqtype= A' -> 
subsump_vqtype B A -> subsump_vqtype B A'.
Proof. intros HT HSImp. 
(* destruct vqtype into velem and fexp *)
destruct A as (A, ea).
destruct B as (B, eb).
destruct A' as (A', ea').
(* unfold subsump_vqtype in context and goal *)
unfold subsump_vqtype. unfold subsump_vqtype in HSImp.
intros x e HIn. 
(* HSImp: subsump_vqtype B A : In x B -> exists, In x A /\ sat
   -------------------------------------------------
   Goal: subsump_vqtype B A' : In x B -> exists, In x A' /\ sat
   
   ==> apply HSImp in (In x B) to get (exists, In x A /\ sat )
*) 

apply HSImp in HIn. 
(* unfold vqtype_quiv in A=vqtype=A' *)
unfold "=vqtype=", "=avset=" in HT.
(* unfold sat in (exists, In x A /\ sat ) || sat: exixts c, E[]c = true *)
unfold sat in HIn. destruct HIn as [e1 HIn].
destruct HIn as [HIn HSat].
destruct HSat as [c HSat]. simpl in HSat.

(* break down anded truth into individual truth *)
Search andb. rewrite andb_true_iff in HSat.
destruct HSat as [He Heb1a].
rewrite andb_true_iff in Heb1a.
destruct Heb1a as [Heb He1a].
rewrite andb_true_iff in He1a.
destruct He1a as [He1 Hea].

(* introduce existensial variables (e1 , c) in the context *)

(* specialize context with newly introduced config c *)
specialize HT with c. simpl in HT. rewrite Hea in HT.

destruct (E[[ ea']] c) eqn:Hea'. 

{ (* (E[[ ea']] c) = true -> X[[ A]] c =a= X[[ A']] c *)
  
  (* In (ae x e1) A /\ (E[[ e1]] c) = true -> In x (X[[ A]] c) *)
  assert (HInAnde: exists e, In (ae x e) A /\ (E[[ e]] c) = true).
  { exists e1. split; auto. }
  
  apply In_config_exists_true in HInAnde. 
  
  apply (In_equiv_elems _ HT) in HInAnde. 
  
  rewrite <- In_config_exists_true in HInAnde.
  
  destruct HInAnde as [eG [HInA' HeG] ].
  exists eG. split. auto.
  unfold sat. exists c. simpl.
  rewrite He, Heb, HeG, Hea'.
  auto.
}

{ (*  (E[[ ea']] c) = false -> X[[ A]] c =a= [] *)

  (* In (ae x e1) A -> (E[[ e1]] c) = true -> In x (X[[ A]] c) *)
  apply In_config_true with (c:=c) in HIn; try assumption.
  apply (In_equiv_elems _ HT) in HIn. destruct HIn.
}
Qed.


Lemma subsump_vqtype_inter_l B C:
subsump_vqtype (vqtype_inter_vq B C) B.
Proof. 
destruct B as (B, eb).
destruct C as (C, ec).
(* unfold subsump_vqtype in context and goal *)
unfold subsump_vqtype. simpl. 
intros x ex HIn. 
(* HIn:             In (x, ex) B /_\ C /\ sat (ex /\ eb /\ ec)
   -------------------------------------------------
   Goal: exists e', In (x, e') C /\ sat (ex /\ eb /\ ec /\ e')
*) 
destruct HIn as [HIn HSat].

unfold sat in HSat. destruct HSat as [c HSat].
simpl in HSat. rewrite andb_true_iff in HSat.
destruct HSat as [Hex Hebc].
rewrite andb_true_iff in Hebc.
destruct Hebc as [Heb Hec].

(* sat (ex /\ eb /\ ec) ->  (E[[ ex ]]c) = true *)

pose (conj HIn Hex) as HInBex. 
apply In_velems_inter_A in HInBex.

(* HInex:             In (x, ex) B /-\ C /\ (E[[ ex ]]c) = true
   HInCex: exists e', In (ae x e') C     /\ (E[[ e']] c) = true
   -------------------------------------------------
   Goal: exists e', In (x, e') C /\ sat (ex /\ eb /\ ec /\ e')
*) 

destruct HInBex as [exc [HInB HBex] ]. 

(*
   HInCex: In (ae x exc) C   
   HCex:   (E[[ exc]] c) = true
*)

exists exc.

split. assumption.

unfold sat. exists c.
simpl. rewrite Hex, Heb, Hec, HBex.
eauto.

Qed.

Lemma implies_sat e1 e2 e3: 
(forall c, E[[ e1]] c = true -> E[[ e2]] c = true )
-> sat(e1 /\(F) e3) -> sat(e2 /\(F) e3).
Proof. unfold sat. intros He1impe2 Hsate1e3.
destruct Hsate1e3 as [c Hsate1e3].
simpl in Hsate1e3. rewrite andb_true_iff in Hsate1e3.
destruct Hsate1e3. 
exists c. simpl. rewrite andb_true_iff.
split. eauto.
auto.
Qed.

Lemma sat_assoc e1 e2 e3:  sat (e1 /\(F) e2 /\(F) e3) <->
sat ((e1 /\(F) e2) /\(F) e3).
Proof. split; unfold sat; intro H;
destruct H as [c H];
simpl in H;
exists c; simpl;
[ rewrite andb_assoc in H |
  rewrite andb_assoc ];
auto.
Qed.

Lemma sat_comm e1 e2:  sat (e1 /\(F) e2) <->
sat (e2 /\(F) e1) .
Proof. split; unfold sat; intro H;
destruct H as [c H];
simpl in H;
exists c; simpl;
[ rewrite andb_comm in H |
  rewrite andb_comm ];
auto.
Qed.

Lemma sat_equiv e1 e2 e3:  e1 =e= e2 ->
sat (e1 /\(F) e3) ->
sat (e2 /\(F) e3).
Proof. unfold equivE.
unfold sat. intros Hequiv H.
destruct H as [c H].
simpl in H. 
exists c. simpl.
rewrite Hequiv in H.
auto.
Qed.


Lemma subsump_vqtype_inter_intro Ap (HndpAp: NoDupElem Ap) ep 
Aqs (HndpAqs: NoDupElem Aqs) eqs e: subsump_vqtype (Ap, ep) (Aqs, eqs /\(F) e) -> 
subsump_vqtype (vqtype_inter_vq (Ap, ep) (Aqs, eqs)) (Aqs, eqs /\(F) e).
Proof.
unfold subsump_vqtype. simpl. 
intros H x e12 HInpq.

destruct HInpq as [HInpq Hsatpq].
apply In_velems_inter_existsAB in HInpq as HInpq'.
destruct HInpq' as [HInp HInq].
destruct HInp as [e1 HInp].

pose (velems_inter_elemchc_more_specific_A x e12 e1 Aqs HndpAp) as He12impe1.
apply implies_sat with (e2:=e1) in Hsatpq.
apply sat_assoc in Hsatpq.

apply sat_and_dist in Hsatpq. 
destruct Hsatpq as [Hsatp Hsatq].

pose (conj HInp Hsatp) as HInAp.

apply H in HInAp.

destruct HInAp as [e2 [HInAqs HsatApAqse] ].

exists e2.

split. auto.

apply (In_velems_inter_equivE x e12 e1 e2 HndpAp
HndpAqs HInpq HInp) in HInAqs as Hequiv.

symmetry in Hequiv.

apply (sat_equiv Hequiv).

unfold sat. simpl.
unfold sat in HsatApAqse.
simpl in HsatApAqse.
destruct HsatApAqse as [c HsatApAqse].
exists c.

apply andb_true_iff in HsatApAqse.
 destruct HsatApAqse as [He1 HsatApAqse].
apply andb_true_iff in HsatApAqse.
 destruct HsatApAqse as [Hep HsatApAqse].
apply andb_true_iff in HsatApAqse.
 destruct HsatApAqse as [He2 HsatApAqse].
apply andb_true_iff in HsatApAqse.
 destruct HsatApAqse as [Heqs He].
 
apply andb_true_iff. split; eauto.
apply andb_true_iff. split; eauto.
apply andb_true_iff. split; eauto.
apply andb_true_iff. split; eauto.
apply andb_true_iff. split; eauto.
apply andb_true_iff. split; eauto.

apply He12impe1; eauto.
Qed.
     
(*Lemma subsump_vqtype_trans A B C: subsump_vqtype A B -> subsump_vqtype B C ->
subsump_vqtype A C.
Proof.
destruct A as (A, ea).
destruct B as (B, eb).
destruct C as (C, ec).
(* unfold subsump_vqtype in context and goal *)
unfold subsump_vqtype. simpl. 
intros HAB HBC x e1 HInA.
apply HAB in HInA as HInB.
destruct HInB as [e2 HInB].

destruct HInB as [HInB HsatAB].
apply sat_and_dist in HsatAB as Hsat.
*)


(*
Lemma subsump_vqtype_inter_l A B: subsump_vqtype (vqtype_inter_vq A B) A.
Admitted.

Lemma subsump_vqtype_inter_r A B: subsump_vqtype (vqtype_inter_vq A B) B.
Admitted.*)


(*Lemma In_velems_inter_A a e c A B: 
In (ae a e) (velems_inter A B) /\ (E[[ e]]c) = true -> 
exists e', In (ae a e') A /\ (E[[ e']]c) = true.
Proof. 
Admitted.


Lemma subsump_vqtype_inter_ B C:
subsump_vqtype (vqtype_inter_vq B C) B.
Proof. 
destruct B as (B, eb).
destruct C as (C, ec).
(* unfold subsump_vqtype in context and goal *)
unfold subsump_vqtype. simpl. 
intros x ex HIn. 
(* HIn:             In (x, ex) B /_\ C /\ sat (ex /\ eb /\ ec)
   -------------------------------------------------
   Goal: exists e', In (x, e') C /\ sat (ex /\ eb /\ ec /\ e')
*) 
destruct HIn as [HIn HSat].

unfold sat in HSat. destruct HSat as [c HSat].
simpl in HSat. rewrite andb_true_iff in HSat.
destruct HSat as [Hex Hebc].
rewrite andb_true_iff in Hebc.
destruct Hebc as [Heb Hec].

(* sat (ex /\ eb /\ ec) ->  (E[[ ex ]]c) = true *)

pose (conj HIn Hex) as HInBex. 
apply In_velems_inter_A in HInBex.

(* HInex:             In (x, ex) B /-\ C /\ (E[[ ex ]]c) = true
   HInCex: exists e', In (ae x e') C     /\ (E[[ e']] c) = true
   -------------------------------------------------
   Goal: exists e', In (x, e') C /\ sat (ex /\ eb /\ ec /\ e')
*) 

destruct HInBex as [exc [HInB HBex] ]. 

(*
   HInCex: In (ae x exc) C   
   HCex:   (E[[ exc]] c) = true
*)

exists exc.

split. assumption.

unfold sat. exists c.
simpl. rewrite Hex, Heb, Hec, HBex.
eauto.

Qed.

Lemma subsump_vqtype_inter_intro B C e:
subsump_vqtype B (fst C, (snd C /\(F) e)) ->
subsump_vqtype (vqtype_inter_vq B C) (fst C, (snd C /\(F) e)).
Proof. 
intros HB.
pose subsump_vqtype_inter_ as HBC.
specialize HBC with B C. 

destruct B as [B eb].
destruct C as [C ec]. simpl in *.

intros x ex HInBC.  

apply HBC in HInBC as HInC.

destruct HInBC as [HInBC HSatBC].
destruct HInC as [exc [HInC HSatC] ].

exists exc.

split. assumption.


Admitted.*)


(*Lemma subsump_vqtype_inter A B C(HndpA: NoDupElem (fst A)) :
subsump_vqtype B A -> subsump_vqtype (vqtype_inter_vq B C) A.
Proof. 
intros HSImp. 
(* destruct vqtype into velem and fexp *)
destruct A as (A, ea).
destruct B as (B, eb).
destruct C as (C, ec).
(* unfold subsump_vqtype in context and goal *)
unfold subsump_vqtype. unfold subsump_vqtype in HSImp.
intros x e HIn. 

simpl in HIn.
simpl.
Admitted.*)

 
End Subset_Subsump_Lemmas.  
(*================================================*)
   
(*
unfold subset_velems_exp in H;  
unfold subset; intro x;
split;
[ intro HInxA | 
  destruct (count_occ string_eq_dec (X[[ A]] c) x) eqn:Hcount;
  [(* Case 0: count_occ string_eq_dec (X[[ A]] c) x = 0 *)
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
destruct (existsb (stringDecF.eqb x) (X[[ A]] c)) eqn: HIn;
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




(*Lemma def_equiv (A A': velems): subset_velems_exp A A' <-> subset_velems_exp' A A'.
Proof. split; intro H.
unfold subset_velems_exp in H.
unfold subset_velems_exp'. intros x e c H0.
destruct H0 as [HIn He].
assert (HInsat: In (ae x e) A /\ sat e). 
split; [ | unfold sat; exists c]; auto.
apply H in HInsat. destruct HInsat as [e' HInsatee'].
destruct HInsatee' as [HIne' Hsatee'].
rewrite not_sat_not_prop in Hsatee'. 
rewrite <- sat_taut_comp in Hsatee'.
specialize Hsatee' with c. apply Hsatee' in He.
exists e'. eauto.

unfold subset_velems_exp' in H.
unfold subset_velems_exp. intros x e H0. 
 

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





