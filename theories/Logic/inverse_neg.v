From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

Require Import Coq.Arith.Wf_nat.

Require Import List.
Import ListNotations.

Definition dub_neg_sub_formula (A E : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (neg E)) E S.

Lemma dub_neg_formula_free :
  forall (A E : formula) (S : subst_ind),
      free_list (dub_neg_sub_formula A E S) = free_list A.
Proof.
intros A E S.
unfold dub_neg_sub_formula, formula_sub_ind.
case (subst_ind_fit A S) eqn:FIT.
- apply formula_sub_ind_free_list.
  reflexivity.
- reflexivity.
Qed.

Lemma dub_neg_sub_formula_closed :
    forall (A : formula),
        forall (E : formula) (S : subst_ind),
            closed A = closed (dub_neg_sub_formula A E S).
Proof.
intros A E S.
case (closed A) eqn:CA.
- unfold dub_neg_sub_formula.
  symmetry.
  apply (formula_sub_ind_closed _ _ _ CA).
  unfold closed; fold closed.
  intros CE.
  apply CE.
- case (closed (dub_neg_sub_formula A E S)) eqn:CnA.
  + apply closed_free_list in CnA.
    rewrite dub_neg_formula_free in CnA.
    apply free_list_closed in CnA.
    rewrite CnA in CA.
    inversion CA.
  + reflexivity.
Qed.

Fixpoint dub_neg_sub_ptree_fit
  (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (dub_neg_sub_ptree_fit P' E S)

| ord_up alpha P', _ => ord_up alpha (dub_neg_sub_ptree_fit P' E S)

| node A, _ => node (dub_neg_sub_formula A E S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (dub_neg_sub_formula A E S)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    (weakening_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E S_D))

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind (0) S_D))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| negation_a A d alpha P', _ =>
    (match S, form_eqb A E with
    | (1), true => ord_up (ord_succ alpha) P'
    | _, _ => P
    end)

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    (match S_A, form_eqb A E with
    | (1), true => ord_up (ord_succ alpha) (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    | _, _ => 
        negation_ad
          A
          (dub_neg_sub_formula D E S_D)
          d alpha
          (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    end)

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (dub_neg_sub_formula D E S_D)
      n t d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (0) S_D))


| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => P

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SC SA) =>
    loop_ca
      (dub_neg_sub_formula C E SC)
      A n d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind SC (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind SC (non_target A)))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (dub_neg_sub_formula C E S)
      A d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (dub_neg_sub_formula D E S) d1 d2 alpha1 alpha2
      P1
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (dub_neg_sub_formula C E S_C)
      A (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S_C (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint dub_neg_node_fit (P : ptree) (S : subst_ind) : list subst_ind :=
match P, S with
| deg_up d P', _ => dub_neg_node_fit P' S

| ord_up alpha P', _ => dub_neg_node_fit P' S

| node A, _ => [S]

| exchange_ab A B d alpha P', (lor_ind S_B S_A) => dub_neg_node_fit P' (lor_ind S_A S_B)

| exchange_cab C A B d alpha P', (lor_ind (lor_ind S_C S_B) S_A) => dub_neg_node_fit P' (lor_ind (lor_ind S_C S_A) S_B)

| exchange_abd A B D d alpha P', (lor_ind (lor_ind S_B S_A) S_D) => dub_neg_node_fit P' (lor_ind (lor_ind S_A S_B) S_D)

| exchange_cabd C A B D d alpha P', (lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D) => dub_neg_node_fit P' (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)

| contraction_a A d alpha P', _ => dub_neg_node_fit P' (lor_ind S S)

| contraction_ad A D d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' (lor_ind (lor_ind S_A S_A) S_D)

| weakening_ad A D d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' S_D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => dub_neg_node_fit P1 (0) ++ dub_neg_node_fit P2 (0)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_AB S_D) => dub_neg_node_fit P1 (lor_ind (0) S_D) ++ dub_neg_node_fit P2 (lor_ind (0) S_D)

| negation_a A d alpha P', _ => dub_neg_node_fit P' (non_target A)

| negation_ad A D d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' (lor_ind (non_target A) S_D)

| quantification_a A n t d alpha P', _ => dub_neg_node_fit P' (0)

| quantification_ad A D n t d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' (lor_ind (0) S_D)

| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => (snd (split (filter (fun X => if form_eq_dec A (fst X) then false else true) (combine (node_extract P2) (dub_neg_node_fit P2 (non_target A)))))) ++ dub_neg_node_fit P1 (non_target A)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_C S_A) => (snd (split (filter (fun X => if form_eq_dec (lor C A) (fst X) then false else true) (combine (node_extract P2) (dub_neg_node_fit P2 (lor_ind S_C (non_target A))))))) ++ dub_neg_node_fit P1 (lor_ind S_C (non_target A))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ => dub_neg_node_fit P1 (lor_ind S (non_target A)) ++ dub_neg_node_fit P2 (0)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ => dub_neg_node_fit P1 (non_target A) ++ dub_neg_node_fit P2 (lor_ind (0) S)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_C S_D) => dub_neg_node_fit P1 (lor_ind S_C (non_target A)) ++ dub_neg_node_fit P2 (lor_ind (0) S_D)

| _,_ => []
end.

Definition dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.

Definition dub_neg_node (P : ptree) (S : subst_ind) : list subst_ind :=
match subst_ind_fit (ptree_formula P) S with
| false => map non_target (node_extract P)
| true => dub_neg_node_fit P S
end.

Lemma dub_neg_ptree_formula_true :
    forall (P : ptree) (E : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_node_formula_true :
    forall (P : ptree) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_node_fit P S = dub_neg_node P S.
Proof. intros. unfold dub_neg_node. rewrite H. reflexivity. Qed.

Lemma dub_neg_axiom_id :
    forall (A E : formula) (S : subst_ind),
        PA_cyclic_axiom A = true ->
            dub_neg_sub_formula A E S = A.
Proof.
intros A E S AX.
induction A;
inversion AX as [AX'];
unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
fold form_eqb;
case subst_ind_fit;
try reflexivity.
destruct A;
inversion AX as [AX''].
unfold form_eqb.
reflexivity.
Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV.
induction P.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

all : intros S FS;
      unfold dub_neg_sub_ptree;
      try rewrite FS;
      unfold dub_neg_sub_ptree_fit;
      fold dub_neg_sub_ptree_fit;
      unfold ptree_formula in *;
      fold ptree_formula in *;
      try reflexivity.

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS).

8,11,14 :
    unfold dub_neg_sub_formula, formula_sub_ind;
    try rewrite FS;
    try reflexivity.

all : destruct S;
      inversion FS as [FS'];
      try reflexivity;
      try apply and_bool_prop in FS' as [FS' FS1];
      unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, form_eqb;
      fold form_eqb formula_sub_ind_fit ptree_formula subst_ind_fit.

6-8 : case (form_eqb a E) eqn:FEQ;
      try reflexivity;
      try apply form_eqb_eq in FEQ;
      try destruct FEQ;
      try apply PF.

2-4,6-8,10 : 
    destruct S1;
    inversion FS' as [FS''];
    try apply and_bool_prop in FS' as [FS' FS2].

4 : destruct S1_1;
    inversion FS'' as [FS'''];
    apply and_bool_prop in FS' as [FS' FS3].

all : unfold "&&";
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS3;
      unfold ptree_formula;
      fold ptree_formula;
      try reflexivity.

1 : rewrite dub_neg_ptree_formula_true, (IHP PSV);
    try rewrite PF;
    unfold dub_neg_sub_formula, subst_ind_fit;
    fold subst_ind_fit.
    rewrite formula_sub_ind_lor, non_target_sub.

2,3,4 : rewrite non_target_fit, FS1;
        reflexivity.

1 : unfold formula_sub_ind.
    rewrite FS1.
    reflexivity.
Qed.

Lemma dub_neg_ptree_formula : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          ptree_formula (dub_neg_sub_ptree P E S) =
              dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV S.
case (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula' _ _ PSV), FS.
- unfold dub_neg_sub_formula, formula_sub_ind, dub_neg_sub_ptree.
  rewrite FS.
  reflexivity.
Qed.

Lemma dub_neg_ptree_deg :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E PSV.
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PSV as [[PSV OU] NO].

7,8 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4,5 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- assert (subst_ind_fit (ptree_formula P) (lor_ind (non_target a) S2) = true) as FSP.
  { rewrite PF.
    unfold subst_ind_fit; fold subst_ind_fit.
    rewrite non_target_fit.
    unfold "&&".
    apply FS''. }
  pose proof (IHP PSV (lor_ind (non_target a) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

Lemma dub_neg_ptree_ord :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E PSV.
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PSV as [PSV DU].

7,8 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4,5 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

Definition dub_neg_trans (L : (list (formula * subst_ind))) (E : formula) := map (fun A => dub_neg_sub_formula (fst A) E (snd A)) L.

Lemma combine_eq_len :
    forall {A B : Type} (L1 L3 : list A) (L2 L4 : list B),
        length L1 = length L2 ->
            combine L1 L2 ++ combine L3 L4 = combine (L1 ++ L3) (L2 ++ L4).
Proof.
intros A B L1.
induction L1;
intros L3 L2 L4 EQ;
destruct L2.
- reflexivity.
- inversion EQ.
- inversion EQ.
- repeat rewrite <- app_comm_cons.
  unfold combine;
  fold (@combine A A).
  rewrite <- IHL1.
  reflexivity.
  apply eq_add_S, EQ.
Qed.

Lemma combine_filter_fst :
    forall {A B : Type} (L1 : list A) (L2 : list B) (f : A -> bool),
        length L1 = length L2 ->
            length (filter (fun X => f (fst X)) (combine L1 L2)) = length (filter f L1).
Proof.
intros A B L1.
induction L1;
intros L2 f EQL;
destruct L2.
- reflexivity.
- inversion EQL.
- inversion EQL.
- unfold combine;
  fold (@combine A B).
  unfold filter;
  fold (filter f) (filter (fun (X : A * B) => f (fst X))).
  unfold fst at 1.
  case (f a) eqn:T.
  + unfold length;
    fold (@length A) (@length (A*B)).
    rewrite IHL1.
    reflexivity.
    apply eq_add_S, EQL.
  + apply IHL1, eq_add_S, EQL.
Qed.

Lemma combine_non_target_triv : 
  forall (L : list formula) (E : formula),
      dub_neg_trans (combine L (map non_target L)) E = L.
Proof.
induction L;
intros E.
- reflexivity.
- unfold map, combine;
  fold (map non_target) (@combine formula subst_ind).
  unfold dub_neg_trans in *.
  unfold map at 1.
  fold (map (fun A : formula * subst_ind => dub_neg_sub_formula (fst A) E (snd A))).
  unfold dub_neg_sub_formula at 1.
  rewrite non_target_sub.
  rewrite (IHL E).
  reflexivity.
Qed.

Lemma non_target_lor :
    forall {A B : formula},
        (lor_ind (non_target A) (non_target B)) = (non_target (lor A B)). Proof. reflexivity. Qed.

Lemma eq_app_eq :
    forall {A : Type} (L1 L2 L3 L4 : list A),
        L1 = L2 -> L3 = L4 -> L1 ++ L3 = L2 ++ L4.
Proof.
intros A L1 L2 L3 L4 EQ1 EQ2.
rewrite EQ1, EQ2.
reflexivity.
Qed.

Lemma snd_split :
    forall {A B : Type} {L : list (A * B)} {a : A} {b : B},
        snd (split ((a,b) :: L)) = b :: snd (split L).
Proof.
intros A B L a b.
unfold split at 1.
fold (split L).
unfold snd at 1.
destruct (split L).
reflexivity.
Qed.
    
Lemma combine_with_filter_split :
    forall {A B : Type} (f : A -> bool) (L1 : list A) (L2 : list B),
        length L1 = length L2 ->
            combine (filter f L1) (snd (split (filter (fun X => f (fst X)) (combine L1 L2)))) = (filter (fun X => f (fst X)) (combine L1 L2)).
Proof.
intros A B f.
induction L1;
intros L2 EQL;
destruct L2.
- reflexivity.
- inversion EQL.
- inversion EQL.
- unfold length in EQL;
  fold (@length A) (@length B) in EQL.
  unfold combine;
  fold (@combine A B).
  unfold filter;
  fold (@filter A f) (@filter (A * B) (fun X => f (fst X))).
  unfold fst at 1 4.
  case (f a) eqn:Val.
  + rewrite snd_split.
    unfold combine at 1.
    fold (@combine A B).
    rewrite IHL1.
    reflexivity.
    apply (eq_add_S _ _ EQL).
  + rewrite IHL1.
    reflexivity.
    apply (eq_add_S _ _ EQL).
Qed.

Lemma filter_fst_non_target : 
    forall {A B : Type} (f : A -> bool) (m : A -> B) (L : list A),
        (snd (split (filter (fun X => f (fst X)) (combine L (map m L))))) = map m (filter (fun X => f X) L).
Proof.
intros A B f m L.
induction L.
- reflexivity.
- unfold combine, map.
  fold (map m) (combine L (map m L)).
  unfold filter;
  fold (filter f) (filter (fun (X : A * B) => (f (fst X)))).
  unfold fst at 1.
  case (f a) eqn:T;
  try rewrite snd_split;
  rewrite IHL;
  reflexivity.
Qed.

Lemma dub_neg_node_non_target :
    forall (P : ptree),
        struct_valid P ->
            dub_neg_node P (non_target (ptree_formula P)) = map non_target (node_extract P).
Proof.
intros P.
induction P;
intros PSV;
unfold dub_neg_node, node_extract, dub_neg_node_fit;
rewrite non_target_fit;
fold node_extract dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : reflexivity.


all : unfold ptree_formula;
      fold ptree_formula;
      unfold non_target;
      fold non_target;
      repeat rewrite dub_neg_node_formula_true;
      repeat rewrite non_target_lor.

all : try rewrite <- (IHP PSV);
      try rewrite map_app;
      try rewrite <- (IHP1 P1SV);
      try rewrite <- (IHP2 P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      unfold non_target;
      fold non_target;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      try reflexivity.

all : rewrite <- non_target_term_sub;
      rewrite (non_target_term_sub a n (succ (var n))) at 1;
      try rewrite non_target_lor;
      rewrite <- P2F;
      rewrite (IHP2 P2SV);
      try rewrite (filter_fst_non_target (fun X => if form_eq_dec a X then false else true));
      try rewrite (filter_fst_non_target (fun X => if form_eq_dec (lor c a) X then false else true));
      rewrite <- remove_alt;
      reflexivity.
Qed.

(*
Lemma dub_neg_node_transform :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                { L : list subst_ind & node_extract (dub_neg_sub_ptree P E S) = (dub_neg_trans (combine (node_extract P) L) E) /\ length L = length (node_extract P) }.
Proof.
intros P.
induction P;
intros E S PSV FS;
unfold dub_neg_sub_ptree, node_extract, dub_neg_sub_ptree_fit;
rewrite FS;
fold node_extract dub_neg_sub_ptree_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : refine (existT _ [S] (conj eq_refl eq_refl)).


3-6,8-15,18-20 :
  destruct S;
  inversion FS as [FS'];
  try rewrite FS';
  try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10,13,17 :
  destruct S1;
  inversion FS' as [FS''];
  try rewrite FS'';
  try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
  inversion FS'' as [FS'''];
  try rewrite FS''';
  destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,15 : case form_eqb eqn:EQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      unfold node_extract, ptree_formula in *;
      fold node_extract ptree_formula in *;
      try apply (IHP _ _ PSV);
      repeat rewrite app_length;
      try destruct (IHP1 E _ P1SV) as [L1 EQ1];
      try destruct (IHP2 _ _ P2SV) as [L2 EQ2];
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

  15 :  try refine (existT _ ((map non_target (node_extract P1)) ++ (projT1 (IHP2 E _ P2SV _))) (conj _ _));
        try destruct IHP2 as [L2 [EQ2 EL2]];
        unfold projT1, dub_neg_trans;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite app_length;
        try rewrite map_length;
        try rewrite EL2;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite EQ2;
        try reflexivity.

  14 :  try refine (existT _ ((projT1 (IHP1 E _ P1SV _)) ++ (map non_target (node_extract P2))) (conj _ _));
        try destruct IHP1 as [L1 [EQ1 EL1]];
        unfold projT1, dub_neg_trans;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym EL1));
        try rewrite map_app;
        try rewrite app_length;
        try rewrite map_length;
        try rewrite EL1;
        try rewrite (combine_non_target_triv (node_extract P2) E) at 1;
        try rewrite EQ1;
        try reflexivity.

  1,2,5-7 : refine (existT _ (map non_target (node_extract P)) (conj _ _));
            unfold dub_neg_trans;
            try rewrite (combine_non_target_triv (node_extract P) E) at 1;
            repeat rewrite map_length;
            reflexivity.
  
  1,2,5 : try refine (existT _ ((projT1 (IHP1 E _ P1SV _)) ++ (projT1 (IHP2 E _ P2SV _))) (conj _ _));
          try destruct IHP1 as [L1 [EQ1 EL1]], IHP2 as [L2 [EQ2 EL2]];
          unfold projT1;
          try rewrite <- (combine_eq_len _ _ _ _ (eq_sym EL1));
          try rewrite EQ1,EQ2;
          unfold dub_neg_trans;
          try rewrite map_app;
          try rewrite app_length, EL1, EL2;
          try reflexivity.

  1,2 : refine (existT _ (map non_target ((node_extract P1) ++ (node_extract P2))) (conj _ _));
        unfold dub_neg_trans;
        rewrite map_app;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite (combine_non_target_triv (node_extract P2) E) at 1;
        try rewrite app_length;
        repeat rewrite map_length;
        try reflexivity.

  1,2 : refine (existT _ (map non_target ((remove form_eq_dec a (node_extract P2)) ++ (node_extract P1))) (conj _ _));
        unfold dub_neg_trans;
        rewrite map_app;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite (combine_non_target_triv (remove form_eq_dec a (node_extract P2)) E) at 1;
        try rewrite app_length;
        repeat rewrite map_length;
        try reflexivity.

  1 : { assert (subst_ind_fit (ptree_formula P2) (lor_ind S1 (non_target a)) = true) as FSC.
        { rewrite P2F.
          unfold subst_ind_fit;
          fold subst_ind_fit.
          rewrite FS1.
          apply non_target_sub_fit. }
        try refine (existT _ ((snd (split (filter (fun X : (formula * subst_ind) => (if form_eq_dec (lor c a) (fst X) then false else true)) (combine (node_extract P2) (projT1 (IHP2 E _ P2SV FSC)))))) ++ (projT1 (IHP1 E _ P1SV _))) (conj _ _));
        try destruct IHP1 as [L1 [EQ1 EL1]], IHP2 as [L2 [EQ2 EL2]];
        unfold projT1.
        - unfold dub_neg_trans.
          rewrite <- combine_eq_len.
          + rewrite map_app, EQ1, EQ2.
            refine (eq_app_eq _ _ _ _ _ (eq_refl)).
            rewrite <- (remove_alt _ (lor c a)).
            unfold remove'.
            rewrite (combine_with_filter_split (fun Y => if form_eq_dec (lor c a) Y then false else true) (node_extract P2) L2 (eq_sym EL2)).

            admit.
          + admit.

        - rewrite app_length, split_length_r, EL1.
          rewrite (combine_filter_fst _ _ (fun X => (if form_eq_dec (lor c a) X then false else true)) (eq_sym EL2)).
          rewrite <- remove_alt.
          unfold remove'.
          reflexivity. }



Admitted.
*)

Lemma dub_neg_node_len : 
    forall (P : ptree) (S : subst_ind),
        struct_valid P ->
            length (node_extract P) = length (dub_neg_node P S).
Proof.
intros P;
induction P;
intros S PSV;
unfold dub_neg_node;
case subst_ind_fit eqn:FS;
try rewrite map_length;
try reflexivity;
unfold node_extract, dub_neg_node_fit;
fold node_extract dub_neg_node_fit.

1 : destruct PSV as [PSV DU]. (*deg up*)
2 : destruct PSV as [[PSV OU] NO]. (*ord up*)

3-12 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
13 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

14-18 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
19-20 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

all : unfold ptree_formula in *;
      fold ptree_formula in *.

3-6,8-15,18-20 :
  destruct S;
  inversion FS as [FS'];
  try rewrite FS';
  try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10,13,17 :
  destruct S1;
  inversion FS' as [FS''];
  try rewrite FS'';
  try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
  inversion FS'' as [FS'''];
  try rewrite FS''';
  destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : repeat rewrite dub_neg_node_formula_true;
      try apply IHP;
      repeat rewrite app_length;
      try rewrite <- IHP1;
      try rewrite <- IHP2;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
      try apply FS;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

all : rewrite split_length_r, <- remove_alt;
      unfold remove';
      rewrite (combine_filter_fst _ _ (fun X => if (form_eq_dec _ X) then false else true));
      try reflexivity;
      apply IHP2, P2SV.
Qed.

(*
Lemma dub_neg_non_target_triv_len :
    forall (LF : list formula) (P : ptree),
        LF = node_extract P ->
            forall (E : formula),
                struct_valid P ->
                    node_extract P = dub_neg_trans (combine (node_extract P) (dub_neg_node P (non_target (ptree_formula P)))) E.
Proof.
intros LF.
induction LF as [LF IND] using (induction_ltof1 _ (@length formula)).

induction P;
intros EQL E PSV;
unfold dub_neg_trans, dub_neg_node, dub_neg_node_fit, ptree_formula, node_extract;
rewrite non_target_fit;
fold ptree_formula node_extract dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : unfold combine, map, fst, snd, dub_neg_sub_formula.
    rewrite non_target_sub.
    reflexivity.

all : unfold non_target;
      fold non_target;
      unfold node_extract in EQL;
      fold node_extract in EQL;
      repeat rewrite dub_neg_node_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try apply non_target_fit;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try apply non_target_sub_fit;
      repeat rewrite non_target_lor;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F.

11,12 : fold (non_target (neg (substitution a m (projT1 t))));
        try rewrite non_target_lor;
        rewrite <- PF.

all : try apply (IHP EQL _ PSV).

1-5 : try rewrite <- (combine_eq_len _ _ _ _ (dub_neg_node_len _ _ P1SV));
      try rewrite map_app;
      unfold ltof in IND;
      rewrite EQL in IND;
      rewrite (IND _ (struct_node_sum_less_l) _ eq_refl E P1SV), (IND _ (struct_node_sum_less_r) _ eq_refl E P2SV) at 1;
      rewrite P1F, P2F;
      reflexivity.

1 : { rewrite <- remove_alt at 2.
      unfold remove'.
      rewrite <- combine_eq_len.
      rewrite (combine_with_filter_split (fun Y => if form_eq_dec a Y then false else true) (node_extract P2)).
      - rewrite map_app.
        destruct (remove form_eq_dec a (node_extract P2)) as [ | L2] eqn:EQ.
        + rewrite app_nil_l in *.
          rewrite (IHP1 EQL E P1SV) at 1.
          admit.
        + unfold ltof in IND;
        rewrite EQL in IND;
        rewrite (IND _ (struct_node_sum_less_l) _ EQ E P2SV), (IND _ (struct_node_sum_less_r) _ eq_refl E P2SV) at 1;
        rewrite P1F, P2F;
        reflexivity.

      - apply dub_neg_node_len, P2SV.
      - rewrite split_length_r.
        rewrite <- (combine_filter_fst _ (dub_neg_node P2 (non_target a))).
        reflexivity.
        apply dub_neg_node_len, P2SV. }

1 : { rewrite <- remove_alt at 2.
      unfold remove'.
      rewrite <- combine_eq_len.
      rewrite (combine_with_filter_split (fun Y => if form_eq_dec (lor c a) Y then false else true) (node_extract P2)).
      - admit.
      - apply dub_neg_node_len, P2SV.
      - rewrite split_length_r.
        rewrite <- (combine_filter_fst _ (dub_neg_node P2 (non_target (lor c a)))).
        reflexivity.
        apply dub_neg_node_len, P2SV. }


Qed.
*)

Lemma dub_neg_non_target_triv :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            node_extract P = dub_neg_trans (combine (node_extract P) (dub_neg_node P (non_target (ptree_formula P)))) E.
Proof.
intros P;
induction P;
intros E PSV;
unfold dub_neg_trans, dub_neg_node, dub_neg_node_fit, ptree_formula, node_extract;
rewrite non_target_fit;
fold ptree_formula node_extract dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : unfold combine, map, fst, snd, dub_neg_sub_formula.
    rewrite non_target_sub.
    reflexivity.

all : unfold non_target;
      fold non_target;
      repeat rewrite dub_neg_node_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try apply non_target_fit;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try apply non_target_sub_fit;
      repeat rewrite non_target_lor;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F.

11,12 :  fold (non_target (neg (substitution a m (projT1 t))));
      try rewrite non_target_lor;
      rewrite <- PF.

all : try apply (IHP _ PSV).

1-5 : try rewrite <- (combine_eq_len _ _ _ _ (dub_neg_node_len _ _ P1SV));
      try rewrite map_app;
      try rewrite (IHP1 E P1SV) at 1;
      try rewrite (IHP2 E P2SV) at 1;
      try rewrite P1F, P2F;
      try reflexivity.
      
1 : { rewrite <- remove_alt at 2.
      unfold remove'.
      rewrite <- combine_eq_len.
      rewrite (combine_with_filter_split (fun Y => if form_eq_dec a Y then false else true) (node_extract P2)).
      - rewrite map_app.
        fold (dub_neg_trans (combine (node_extract P1) (dub_neg_node P1 (non_target a))) E).
        rewrite (non_target_term_sub a n zero) at 2.
        rewrite <- P1F.
        rewrite <- (IHP1 _ P1SV).
        admit.

      - apply dub_neg_node_len, P2SV.
      - rewrite split_length_r.
        rewrite <- (combine_filter_fst _ (dub_neg_node P2 (non_target a))).
        reflexivity.
        apply dub_neg_node_len, P2SV. }

1 : { rewrite <- remove_alt at 2.
      unfold remove'.
      rewrite <- combine_eq_len.
      rewrite (combine_with_filter_split (fun Y => if form_eq_dec (lor c a) Y then false else true) (node_extract P2)).
      - admit.
      - apply dub_neg_node_len, P2SV.
      - rewrite split_length_r.
        rewrite <- (combine_filter_fst _ (dub_neg_node P2 (non_target (lor c a)))).
        reflexivity.
        apply dub_neg_node_len, P2SV. }
Admitted.

Lemma dub_neg_node_transform_other :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                node_extract (dub_neg_sub_ptree P E S) = (dub_neg_trans (combine (node_extract P) (dub_neg_node P S)) E).
Proof.
intros P.
induction P;
intros E S PSV FS;
unfold dub_neg_sub_ptree, node_extract, dub_neg_sub_ptree_fit, dub_neg_node, dub_neg_node_fit;
rewrite FS;
fold node_extract dub_neg_sub_ptree_fit dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : reflexivity.

3-6,8-15,18-20 :
  destruct S;
  inversion FS as [FS'];
  try rewrite FS';
  try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10,13,17 :
  destruct S1;
  inversion FS' as [FS''];
  try rewrite FS'';
  try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
  inversion FS'' as [FS'''];
  try rewrite FS''';
  destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,15 : case form_eqb eqn:EQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      repeat rewrite dub_neg_node_formula_true;
      unfold node_extract, ptree_formula in *;
      fold node_extract ptree_formula in *;
      try rewrite (IHP _ _ PSV);
      try rewrite (IHP1 _ _ P1SV);
      try rewrite (IHP2 _ _ P2SV); 
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

  15 :  try refine (existT _ ((map non_target (node_extract P1)) ++ (projT1 (IHP2 E _ P2SV _))) (conj _ _));
        try destruct IHP2 as [L2 [EQ2 EL2]];
        unfold projT1, dub_neg_trans;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite app_length;
        try rewrite map_length;
        try rewrite EL2;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite EQ2;
        try reflexivity.

  14 :  try refine (existT _ ((projT1 (IHP1 E _ P1SV _)) ++ (map non_target (node_extract P2))) (conj _ _));
        try destruct IHP1 as [L1 [EQ1 EL1]];
        unfold projT1, dub_neg_trans;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym EL1));
        try rewrite map_app;
        try rewrite app_length;
        try rewrite map_length;
        try rewrite EL1;
        try rewrite (combine_non_target_triv (node_extract P2) E) at 1;
        try rewrite EQ1;
        try reflexivity.

  1,2,5-7 : unfold 
  refine (existT _ (map non_target (node_extract P)) (conj _ _));
            unfold dub_neg_trans;
            try rewrite (combine_non_target_triv (node_extract P) E) at 1;
            repeat rewrite map_length;
            reflexivity.
  
  1,2,5 : try refine (existT _ ((projT1 (IHP1 E _ P1SV _)) ++ (projT1 (IHP2 E _ P2SV _))) (conj _ _));
          try destruct IHP1 as [L1 [EQ1 EL1]], IHP2 as [L2 [EQ2 EL2]];
          unfold projT1;
          try rewrite <- (combine_eq_len _ _ _ _ (eq_sym EL1));
          try rewrite EQ1,EQ2;
          unfold dub_neg_trans;
          try rewrite map_app;
          try rewrite app_length, EL1, EL2;
          try reflexivity.

  1,2 : refine (existT _ (map non_target ((node_extract P1) ++ (node_extract P2))) (conj _ _));
        unfold dub_neg_trans;
        rewrite map_app;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite (combine_non_target_triv (node_extract P2) E) at 1;
        try rewrite app_length;
        repeat rewrite map_length;
        try reflexivity.

  1,2 : refine (existT _ (map non_target ((remove form_eq_dec a (node_extract P2)) ++ (node_extract P1))) (conj _ _));
        unfold dub_neg_trans;
        rewrite map_app;
        try rewrite <- (combine_eq_len _ _ _ _ (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite (combine_non_target_triv (remove form_eq_dec a (node_extract P2)) E) at 1;
        try rewrite app_length;
        repeat rewrite map_length;
        try reflexivity.

  1 : { assert (subst_ind_fit (ptree_formula P2) (lor_ind S1 (non_target a)) = true) as FSC.
        { rewrite P2F.
          unfold subst_ind_fit;
          fold subst_ind_fit.
          rewrite FS1.
          apply non_target_sub_fit. }
        try refine (existT _ ((snd (split (filter (fun X : (formula * subst_ind) => (if form_eq_dec (lor c a) (fst X) then false else true)) (combine (node_extract P2) (projT1 (IHP2 E _ P2SV FSC)))))) ++ (projT1 (IHP1 E _ P1SV _))) (conj _ _));
        try destruct IHP1 as [L1 [EQ1 EL1]], IHP2 as [L2 [EQ2 EL2]];
        unfold projT1.
        - unfold dub_neg_trans.
          rewrite <- combine_eq_len.
          + rewrite map_app, EQ1, EQ2.
            refine (eq_app_eq _ _ _ _ _ (eq_refl)).
            rewrite <- (remove_alt _ (lor c a)).
            unfold remove'.
            rewrite (combine_with_filter_split (fun Y => if form_eq_dec (lor c a) Y then false else true) (node_extract P2) L2 (eq_sym EL2)).

            admit.
          + admit.

        - rewrite app_length, split_length_r, EL1.
          rewrite (combine_filter_fst _ _ (fun X => (if form_eq_dec (lor c a) X then false else true)) (eq_sym EL2)).
          rewrite <- remove_alt.
          unfold remove'.
          reflexivity. }



Admitted.


(*
Lemma dub_neg_node_size :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                length (node_extract P) = length (node_extract (dub_neg_sub_ptree P E S)).
Proof.
intros P.
induction P;
intros E S PSV FS;
unfold dub_neg_sub_ptree, node_extract, dub_neg_sub_ptree_fit;
rewrite FS;
fold node_extract dub_neg_sub_ptree_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : reflexivity.

3-6,8-15,18-20 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
4-6,10,13,17 :
    destruct S1;
    inversion FS' as [FS''];
    try rewrite FS'';
    try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
6 : destruct S1_1;
    inversion FS'' as [FS'''];
    try rewrite FS''';
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,15 : case form_eqb eqn:EQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      unfold node_extract, ptree_formula in *;
      fold node_extract ptree_formula in *;
      try apply (IHP _ _ PSV);
      repeat rewrite app_length;
      try rewrite <- (IHP1 _ _ P1SV);
      try rewrite <- (IHP2 _ _ P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

      rewrite remove_length.

      admit.


Lemma dub_neg_free_sub_aux :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                forall (A : formula),
                    In A (node_extract (dub_neg_sub_ptree P E S)) ->
                        { B : formula & In B (node_extract P) /\ free_list B = free_list A }.
Proof.
  intros P E.
  induction P;
  intros S PSV FS C INC.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
  
  1 : { exists a.
        repeat split.
        apply or_introl, eq_refl.
        unfold dub_neg_sub_ptree, node_extract, dub_neg_sub_ptree_fit in INC.
        rewrite FS in INC.
        inversion INC as [EQ | FAL].
        destruct EQ.
        rewrite dub_neg_formula_free.
        reflexivity.
        inversion FAL. }
  
  3-6,8-15,18-20 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,10,13,17 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  6 : destruct S1_1;
      inversion FS'' as [FS'''];
      try rewrite FS''';
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold dub_neg_sub_ptree in INC;
        rewrite FS in INC;
        unfold dub_neg_sub_ptree_fit in INC;
        fold dub_neg_sub_ptree_fit in INC;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true in INC;
        try rewrite dub_neg_ptree_formula_true in INC;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

24 :  { try apply (@in_app_bor _ form_eq_dec) in INC as [INC1 | INC2].
        - apply in_remove in INC1 as [INC1 NE].
          destruct (fun FSUB => IHP2 _ P2SV FSUB C INC1) as [B [INB FB]].
          + rewrite P2F.
            unfold subst_ind_fit;
            fold subst_ind_fit.
            rewrite FS1.
            apply non_target_sub_fit.
          + 
        - destruct (fun FSUB => IHP1 _ P1SV FSUB C INC2) as [B [INB FB]].
          + rewrite P1F.
            unfold subst_ind_fit;
            fold subst_ind_fit.
            rewrite FS1.
            apply non_target_sub_fit.
          + apply (existT _ B (conj (in_or_app _ _ _ (or_intror INB)) FB)).
      }

  all : try case form_eqb eqn:EQ;
        unfold flat_map;
        fold (flat_map free_list);
        repeat rewrite flat_map_app;
        repeat apply incl_app_app;
        try apply incl_refl;
        try apply (fun FSUB => IHP _ PSV FSUB _ INC);
        try apply (existT _ C (conj INC eq_refl));
        try apply (@in_app_bor _ form_eq_dec) in INC as [INC1 | INC2];
        try apply (existT _ C (conj (in_or_app _ _ _ (or_introl INC1)) eq_refl));
        try apply (existT _ C (conj (in_or_app _ _ _ (or_intror INC2)) eq_refl));
        try destruct (fun FSUB => IHP1 _ P1SV FSUB C INC1) as [B [INB FB]];
        try destruct (fun FSUB => IHP1 _ P1SV FSUB C INC2) as [B [INB FB]];
        try destruct (fun FSUB => IHP2 _ P2SV FSUB C INC1) as [B [INB FB]];
        try destruct (fun FSUB => IHP2 _ P2SV FSUB C INC2) as [B [INB FB]];
        try apply (existT _ B (conj (in_or_app _ _ _ (or_introl INB)) FB));
        try apply (existT _ B (conj (in_or_app _ _ _ (or_intror INB)) FB));
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.
Qed.

Lemma dub_neg_free_sub :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                incl (flat_map free_list (node_extract P)) (flat_map free_list (node_extract (dub_neg_sub_ptree P E S))).
Proof.
  intros P E.
  induction P;
  intros S PSV FS.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
  
  1 : { intros A INA.
        unfold dub_neg_sub_ptree.
        rewrite FS.
        unfold dub_neg_sub_ptree_fit.
        unfold node_extract, flat_map in *.
        rewrite app_nil_r in *.
        rewrite dub_neg_formula_free.
        apply INA. }
  
  3-6,8-15,18-20 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,10,13,17 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  6 : destruct S1_1;
      inversion FS'' as [FS'''];
      try rewrite FS''';
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold dub_neg_sub_ptree;
        rewrite FS;
        unfold dub_neg_sub_ptree_fit;
        fold dub_neg_sub_ptree_fit;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  24 :  { unfold flat_map;
          fold (flat_map free_list).
          repeat rewrite flat_map_app.
          apply incl_app_app.
          - refine (@flat_map_equiv _ _ form_eq_dec nat_eq_dec _ _ _ _ _ _ _ INA).
            + rewrite <- (dub_neg_formula_free (lor c a) E (lor_ind S1 (non_target a))).
              unfold dub_neg_sub_formula.
              rewrite formula_sub_ind_lor.
              rewrite non_target_sub.
              reflexivity.
              rewrite FS1.
              apply non_target_fit.
            + apply IHP2.
          - apply (fun FSUB => IHP1 _ P1SV FSUB).
          

 }

  all : try case form_eqb eqn:EQ;
        try case (closed (univ n a)) eqn:CuA;
        unfold flat_map;
        fold (flat_map free_list);
        repeat rewrite flat_map_app;
        repeat apply incl_app_app;
        try apply incl_refl;
        try apply (fun FSUB => IHP _ PSV FSUB);
        try apply (fun FSUB => IHP1 _ P1SV FSUB);
        try apply (fun FSUB => IHP2 _ P2SV FSUB);
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.
Qed.

Lemma dub_neg_not_ax_not_ax :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = false -> (exists (B : formula), In B (node_extract P) /\ PA_cyclic_axiom B = false)).
Proof.
  intros P E.
  induction P;
  intros S PSV FS A IN NAX.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
  
  1 : { unfold dub_neg_sub_ptree in IN.
        rewrite FS in IN.
        unfold dub_neg_sub_ptree_fit in IN.
        destruct IN as [EQ | FAL];
        try inversion FAL.
        destruct EQ.
        exists a.
        unfold node_extract.
        split.
        - left.
          reflexivity.
        - unfold dub_neg_sub_formula, formula_sub_ind in NAX.
          unfold ptree_formula in FS.
          rewrite FS in NAX.
          destruct a;
          unfold formula_sub_ind_fit, form_eqb in NAX;
          fold formula_sub_ind_fit form_eqb in NAX;
          try apply NAX;
          try reflexivity.
          case form_eqb eqn:EQ.
          + apply form_eqb_eq in EQ.
            rewrite EQ.
            reflexivity.
          + apply NAX. }

  3-6,8-15,18-20 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,10,13,17 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  6 : destruct S1_1;
      inversion FS'' as [FS'''];
      try rewrite FS''';
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold dub_neg_sub_ptree in IN;
        rewrite FS in IN;
        unfold dub_neg_sub_ptree_fit in IN;
        fold dub_neg_sub_ptree_fit in IN;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true in IN;
        try rewrite dub_neg_ptree_formula_true in IN;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  all : try case form_eqb eqn:EQ;
        try apply (fun FSUB => IHP _ PSV FSUB _ IN NAX);
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  3-9,11,12 :
      exists A;
      split;
      auto.

  1-3,5,6 :
      try apply in_app_or in IN as [IN1 | IN2];
      try destruct (fun FSUB => IHP1 _ P1SV FSUB A IN1 NAX) as [B1 [INB1 BAX1]];
      try destruct (fun FSUB => IHP2 _ P2SV FSUB A IN2 NAX) as [B2 [INB2 BAX2]];
      try exists B1;
      try exists B2;
      try exists A;
      try split;
      try apply NAX;
      try apply BAX1;
      try apply BAX2;
      try apply (in_or_app _ _ _ (or_introl IN1));
      try apply (in_or_app _ _ _ (or_intror IN2));
      try apply (in_or_app _ _ _ (or_introl INB1));
      try apply (in_or_app _ _ _ (or_intror INB2));
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold ptree_formula in FS;
      fold ptree_formula in FS;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite non_target_fit;
      try reflexivity.

  apply in_app_or in IN as [IN1 | IN2].

  { exists A.
    exact (conj (in_or_app _ _ _ (or_introl IN1)) NAX). }

  { destruct (fun FSUB => IHP1 _ P1SV FSUB A IN2 NAX) as [B1 [INB1 BAX1]].
    - rewrite P1F.
      unfold subst_ind_fit;
      fold subst_ind_fit.
      rewrite FS1;
      apply non_target_sub_fit. 
    - exists B1.
      split.
      apply (in_or_app _ _ _ (or_intror INB1)).
      apply BAX1. }
Qed.
*)

Lemma dub_neg_all_ax_trans : 
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                    (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true).
Proof.
intros P E S PSV FS PAX A INA.
case (PA_cyclic_axiom A) eqn:AX.
- reflexivity.
- destruct (dub_neg_not_ax_not_ax _ _ _ PSV FS _ INA AX) as [B [INB NAX]].
  rewrite (PAX _ INB) in NAX.
  inversion NAX.
Qed.

Lemma dub_neg_valid :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E [PSV PAX].
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.

all : try apply (PSV,PAX).

1 : { repeat split.
      unfold node_extract in *.
      specialize (PAX _ (or_introl eq_refl)).
      intros A IN.
      destruct a;
      try destruct a;
      inversion PAX as [AX'];
      unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb in IN;
      rewrite FS in IN;
      inversion IN as [EQ | FAL];
      try inversion FAL;
      destruct EQ;
      reflexivity. }

1 : destruct PSV as [PSV DU].
2 : destruct PSV as [[PSV OU] NO].
3-11 : destruct PSV as [[[PF PSV] PD] PO].
12 : destruct PSV as [[[[PF PSV] PD] PO] FC].
13-16: destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O].
17: destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA].

3-6,8-13,16,17 : 
    destruct S; inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,11 : case (form_eqb a E) eqn:EQ.

all : try apply form_eqb_eq in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg;
      try rewrite dub_neg_ptree_ord;
      try rewrite dub_neg_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold dub_neg_sub_formula, formula_sub_ind;
      try apply (PSV,PAX);
      try rewrite PD;
      try rewrite PO;
      try apply P1SV;
      try apply (P1SV,(fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))));
      try rewrite P1D;
      try rewrite P1O;
      try apply P2SV;
      try apply (P2SV,(fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))));
      try rewrite P2D;
      try rewrite P2O;
      try apply DU;
      try apply OU;
      try apply NO;
      try apply INA;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold node_extract;
      fold node_extract;
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB)));
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB)));
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub_term';
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try case form_eqb eqn:FEQ;
      try reflexivity.

1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply (incl_tran FC), dub_neg_free_sub.
      apply PSV.
      rewrite PF.
      apply FS2.
      reflexivity. }

all : intros A IN;
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P1SV FSUB (fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
      try apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P2SV FSUB (fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite non_target_fit;
      try reflexivity.

3,4 : try apply PAX;
      try apply in_or_app;
      try apply (or_introl IN1);
      try apply (or_intror IN2).

all : unfold node_extract in *; fold node_extract in *;
      try apply (PAX _ (in_or_app _ _ _ (or_intror IN)));
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
      apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P1SV FSUB (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB))) _ IN2);
      rewrite P1F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      rewrite FS1, non_target_sub_fit;
      reflexivity.
Qed.