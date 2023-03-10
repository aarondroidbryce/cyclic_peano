From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

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
      P2

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SA SD) =>
    loop_ad
      A (dub_neg_sub_formula D E SD)
      n d1 d2 alpha1 alpha2
      P1 (dub_neg_sub_ptree_fit P2 E (lor_ind (non_target A) SD))

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind (lor_ind SC SA) SD) =>
    loop_cad
      (dub_neg_sub_formula C E SC)
      A
      (dub_neg_sub_formula D E SD)
      n d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind SC (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (non_target A) SD))

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

Definition dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.

Lemma dub_neg_ptree_formula_true :
    forall (P : ptree) (E : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV.
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula, node_extract in *; fold ptree_formula node_extract in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.
  
1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
13-14 : destruct PSV as [[[PF PSV] PD] PO].

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS).

1 : reflexivity.

5 : reflexivity.

all : destruct S;
      inversion FS as [FS'];
      try reflexivity;
      try apply and_bool_prop in FS' as [FS' FS1];
      unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, form_eqb;
      fold form_eqb formula_sub_ind_fit ptree_formula subst_ind_fit.

8-10 :  case (form_eqb a E) eqn:FEQ;
        try reflexivity;
        try apply form_eqb_eq in FEQ;
        try destruct FEQ;
        try apply PF.

2-4,7-10,12,13 :  destruct S1;
                  inversion FS' as [FS''];
                  try apply and_bool_prop in FS' as [FS' FS2].

4 : destruct S1_1;
    inversion FS'' as [FS'''];
    apply and_bool_prop in FS' as [FS' FS3].

16 :  destruct S1_2;
      inversion FS2 as [FS'''];
      apply and_bool_prop in FS'' as [FS'' FS3].

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

2-4 : rewrite non_target_fit, FS1;
      reflexivity.

1 : unfold formula_sub_ind.
    rewrite FS1.
    reflexivity.
Qed.

Lemma dub_neg_ptree_formula :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_formula (dub_neg_sub_ptree P E S) =
                    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula' _ _ PSV _ FS).
- unfold dub_neg_sub_ptree, dub_neg_sub_formula, formula_sub_ind.
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

1 : destruct PSV as [[IO PSV] NO].

9,10 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ;
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

1 : destruct PSV as [ID PSV].

9,10 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

Lemma dub_neg_ptree_free_aux : 
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                (flat_map free_list (node_extract (dub_neg_sub_ptree_fit P E S)) = flat_map free_list (node_extract P)).
Proof.
intros P E PSV.
induction P;
intros S;
unfold dub_neg_sub_ptree_fit, node_extract, ptree_formula in *;
fold dub_neg_sub_ptree_fit node_extract ptree_formula in *;
try reflexivity.

1 : destruct PSV as [LT PSV]. (*deg up*)
2 : destruct PSV as [[LT PSV] NO]. (*ord up*)
3 : destruct PSV as []. (*node*)
4-9,12-14 :  destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
13 : destruct PSV as [[[[PF CPF] PSV] PD] PO]. (*weakening*)
14-20 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O]. (*double hyp*)

all : try rewrite PF in IHP;
      try rewrite P1F in IHP1;
      try rewrite P2F in IHP2.

3 : { unfold flat_map.
      rewrite dub_neg_formula_free.
      reflexivity. }

1,2 : try pose proof (IHP PSV S) as IHPS;
      try rewrite FS in IHPS;
      try apply IHPS.

16 :  { repeat rewrite flat_map_app.
        rewrite (IHP2 P2SV).
        reflexivity. }

15 :  { repeat rewrite flat_map_app.
        rewrite (IHP1 P1SV).
        reflexivity. }

5 : apply IHP, PSV.

all : destruct S;
      try rewrite IHP;
      try reflexivity.

2-4,7,13 :  destruct S1;
            try rewrite IHP;
            try reflexivity.

4 : destruct S1_1;
    try rewrite IHP;
    try reflexivity.

6,10 :  case (form_eqb a E) eqn:EQ;
        try rewrite IHP;
        try reflexivity.

all : unfold node_extract;
      fold node_extract;
      repeat rewrite flat_map_app;
      try rewrite (IHP PSV);
      try rewrite (IHP1 P1SV);
      try rewrite (IHP2 P2SV);
      try reflexivity.

all : repeat rewrite <- dub_neg_sub_formula_closed;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      unfold flat_map; fold (flat_map free_list);
      repeat rewrite flat_map_app;
      try rewrite (IHP PSV);
      try rewrite (IHP1 P1SV);
      try rewrite (IHP2 P2SV);
      try reflexivity.
      
7 : {  }
Qed.

Lemma dub_neg_struct_valid :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    struct_valid (dub_neg_sub_ptree P E S).
Proof.
intros P E PSV.
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.

all : try apply PSV.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11-13 : destruct PSV as [[[PF PSV] PD] PO].
10,14-19: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3-6,8-19 :  destruct S; inversion FS as [FS'];
            try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,12,22 : destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

8,9,22,23 : case (form_eqb f E) eqn:EQ.

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
      try apply PSV;
      try rewrite PD;
      try rewrite PO;
      try apply P1SV;
      try rewrite P1D;
      try rewrite P1O;
      try apply P2SV;
      try rewrite P2D;
      try rewrite P2O;
      try apply ID;
      try apply IO;
      try apply NO;
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
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub_term';
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity.

1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.
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

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11-13 : destruct PSV as [[[PF PSV] PD] PO].
10,14-19: destruct PSV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

3-6,8-19 :  destruct S; inversion FS as [FS'];
            try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,12,22 : destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

8,9,22,23 : case (form_eqb f E) eqn:EQ.

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
      try apply P1V;
      try rewrite P1D;
      try rewrite P1O;
      try apply P2V;
      try rewrite P2D;
      try rewrite P2O;
      try apply ID;
      try apply IO;
      try apply NO;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity.

1,3 : apply ord_succ_monot.

all : apply nf_nf_succ;
      apply ptree_ord_nf;
      apply PSV.
Qed.