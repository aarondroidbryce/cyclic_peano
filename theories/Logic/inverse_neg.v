From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

Require Import List.
Require Import Lia.
Import ListNotations.

Require Import Coq.Arith.Wf_nat.

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

Lemma dub_neg_ptree_formula_struct' : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV.
induction P.

3 : { try intros S FS;
      unfold dub_neg_sub_ptree;
      rewrite FS;
      reflexivity. }

all : try intros S FS;
      unfold dub_neg_sub_ptree;
      rewrite FS;
      unfold ptree_formula, node_extract in *; fold ptree_formula node_extract in *;
      unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.
  
1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
12-13 : destruct PSV as [[[PF PSV] PD] PO].

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS).

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

2-4,7-10 :  destruct S1;
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

Lemma dub_neg_ptree_formula_struct : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          ptree_formula (dub_neg_sub_ptree P E S) =
              dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV S.
case (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula_struct' _ _ PSV), FS.
- unfold dub_neg_sub_formula, formula_sub_ind, dub_neg_sub_ptree.
  rewrite FS.
  reflexivity.
Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E [PSV PAX].
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
      apply (IHP PSV PAX _ FS).

1 : { specialize (PAX _ (or_introl eq_refl)). 
      unfold PA_cyclic_axiom in PAX.
      unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit.
      destruct a;
      inversion PAX as [AX'];
      destruct S;
      unfold subst_ind_fit, form_eqb;
      fold form_eqb;
      try apply IN;
      destruct a;
      inversion PAX as [AX''];
      unfold form_eqb;
      reflexivity. }

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

2-4,7-10 :  destruct S1;
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

1 : rewrite dub_neg_ptree_formula_true, (IHP PSV PAX);
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
        valid P ->
            forall (S : subst_ind),
                ptree_formula (dub_neg_sub_ptree P E S) =
                    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E [PSV PAX] S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula' _ _ (PSV,PAX) _ FS).
- unfold dub_neg_sub_ptree, dub_neg_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma dub_neg_ptree_deg :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E [PSV PAX].
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
    pose proof (IHP PSV PAX S) as IHPS.
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
  pose proof (IHP PSV PAX (lor_ind (non_target a) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

Lemma dub_neg_ptree_deg_struct :
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
        valid P ->
            forall (S : subst_ind),
                (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E [PSV PAX].
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
    pose proof (IHP PSV PAX S) as IHPS.
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

Lemma dub_neg_ptree_ord_struct :
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

4,5 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

(**TEMP***)

Lemma nin_split {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L1 L2 : list A) (a : A),
        ~ In a (L1 ++ L2) ->
            ~ In a L1 /\ ~ In a L2.
Proof.
intros L1 L2 a NIN.
case (in_dec DEC a L1) as [IN' | NIN'].
contradict NIN.
apply in_or_app, or_introl, IN'.
apply (conj NIN').
case (in_dec DEC a L2) as [IN'' | NIN''].
contradict NIN.
apply in_or_app, or_intror, IN''.
apply NIN''.
Qed.

Lemma nin_ne_weaken {A : Type} (DEC : forall (a b : A), {a = b} + {a <> b}) :
    forall (L : list A) (a b : A),
        a <> b ->
            ~ In a (remove DEC b L) ->
                ~ In a L.
Proof.
intros L a b NE NIN IN.
apply NIN.
apply (in_in_remove _ _ NE IN).
Qed.

(***End temp : this belongs in lists**)

Lemma missing_non_ax :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract P) -> ~ In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = false).
Proof.
intros P E.
induction P;
intros S PSV FS A IN NIN.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3 : { unfold dub_neg_sub_ptree in NIN.
      rewrite FS in NIN.
      unfold dub_neg_sub_ptree_fit in NIN.
      destruct IN as [EQ | FAL];
      try inversion FAL.
      destruct EQ.
      case (PA_cyclic_axiom a) eqn:AX.
      rewrite (dub_neg_axiom_id _ _ _ AX) in NIN.
      contradict NIN.
      apply (or_introl eq_refl).
      reflexivity. }

3-6,8-13,16-20 : 
    destruct S;
    inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,11,18,21 :
      destruct S1;
      inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
    inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold dub_neg_sub_ptree in NIN;
      rewrite FS in NIN;
      unfold dub_neg_sub_ptree_fit in NIN;
      fold dub_neg_sub_ptree_fit in NIN;
      unfold node_extract in *;
      fold node_extract in *;
      try case form_eqb eqn:EQ;
      try rewrite dub_neg_ptree_formula_true in NIN;
      try rewrite dub_neg_ptree_formula_true in NIN;
      try apply (IHP _ PSV FS _ IN NIN);
      try refine (IHP _ PSV _ _ IN NIN);
      try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
      try apply in_app_or in IN as [IN1 | IN2];
      try refine (IHP1 _ P1SV _ _ IN1 NIN1);
      try refine (IHP2 _ P2SV _ _ IN2 NIN2);
      try contradict (NIN IN);
      try contradict (NIN1 IN1);
      try contradict (NIN2 IN2);
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

1 : repeat rewrite <- dub_neg_sub_formula_closed in *;
    try case (closed c) eqn:CC;
    try case (free_list a) eqn:FREE;
    try case nat_eqb eqn:EQ;
    try destruct l;
    try destruct IN as [EQ' | IN];
    try destruct EQ';
    try reflexivity;
    try apply not_in_cons in NIN as [NE' NIN];
    try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
    try apply in_app_or in IN as [IN1 | IN2];
    try contradict (NIN1 IN1);
    try contradict (NIN1 IN2);
    try contradict (NIN2 IN1);
    try contradict (NIN2 IN2);
    try apply in_remove in IN1 as [IN1 NE1];
    try apply (nin_ne_weaken _ _ _ _ NE1) in NIN1;
    try refine (IHP1 _ P1SV _ _ IN2 NIN2);
    try refine (IHP2 _ P2SV _ _ IN1 NIN1);
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

Lemma all_ax_sub :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                    incl (node_extract P) (node_extract (dub_neg_sub_ptree P E S)).
Proof.
intros P E S PSV FS PAX A INA.
case (in_dec form_eq_dec A (node_extract (dub_neg_sub_ptree P E S))) as [IN | NIN].
- apply IN.
- pose proof (missing_non_ax _ _ _ PSV FS _ INA NIN) as FAL.
  rewrite (PAX _ INA) in FAL.
  inversion FAL.
Qed.

Lemma missing_non_ax_inv :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> ~ In A (node_extract P) -> PA_cyclic_axiom A = false \/ (A = E /\ PA_cyclic_axiom E = true)).
Proof.
intros P E.
induction P;
intros S PSV FS A IN NIN.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-21 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3 : { unfold dub_neg_sub_ptree in IN.
      rewrite FS in IN.
      unfold dub_neg_sub_ptree_fit in IN.
      destruct IN as [EQ | FAL];
      try inversion FAL.
      destruct EQ.
      case (PA_cyclic_axiom a) eqn:AX.
      - rewrite (dub_neg_axiom_id _ _ _ AX) in NIN.
        contradict NIN.
        apply (or_introl eq_refl).

      - unfold ptree_formula in FS.
        unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit in *.
        rewrite FS in *.
        unfold PA_cyclic_axiom in AX;
        destruct a;
        inversion AX as [AX'];
        fold formula_sub_ind_fit in *;
        unfold form_eqb;
        fold form_eqb.
        + left. reflexivity.
        + destruct a;
          inversion AX as [AX''];
          unfold form_eqb in *;
          fold form_eqb in *;
          try case form_eqb eqn:EQ;
          try destruct S;
          try contradict (NIN (or_introl eq_refl)).
          case (PA_cyclic_axiom E); auto.
        + destruct S; left; reflexivity.
        + left. reflexivity. }

3-6,8-13,16-20 : 
    destruct S;
    inversion FS as [FS'];
    try rewrite FS';
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,11,18,21 :
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
      try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => IHP _ PSV FSUB A IN NIN);
      try apply (fun FSUB => IHP1 _ P1SV FSUB A IN1 NIN1);
      try apply (fun FSUB => IHP2 _ P2SV FSUB A IN2 NIN2);
      try contradict (NIN IN);
      try contradict (NIN1 IN1);
      try contradict (NIN2 IN2);
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

1 : repeat rewrite <- dub_neg_sub_formula_closed in *;
    try case (closed c) eqn:CC;
    try case (free_list a) eqn:FREE;
    try case nat_eqb eqn:EQ;
    try destruct l;
    try destruct IN as [EQ' | IN];
    try destruct EQ';
    auto;
    try apply not_in_cons in NIN as [NE' NIN];
    try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
    try apply in_app_or in IN as [IN1 | IN2];
    try contradict (NIN1 IN1);
    try contradict (NIN1 IN2);
    try contradict (NIN2 IN1);
    try contradict (NIN2 IN2);
    try apply in_remove in IN1 as [IN1 NE1];
    try apply (nin_ne_weaken _ _ _ _ NE1) in NIN1;
    try refine (IHP1 _ P1SV _ _ IN2 NIN2);
    try refine (IHP2 _ P2SV _ _ IN1 NIN1);
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

Lemma all_ax_sub_inv :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true) ->
                    incl (node_extract (dub_neg_sub_ptree P E S)) (E :: (node_extract P)).
Proof.
intros P E S PSV FS PAX A INA.
case (in_dec form_eq_dec A (node_extract P)) as [IN | NIN].
- apply (or_intror IN).
- pose proof (missing_non_ax_inv _ _ _ PSV FS _ INA NIN) as [FAL | [EQ _]].
  + rewrite (PAX _ INA) in FAL.
    inversion FAL.
  + destruct EQ.
    apply (or_introl eq_refl).
Qed.

Lemma non_e_len :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                length (node_extract (dub_neg_sub_ptree P E S)) = length (node_extract P).
Proof.
  intros P E.
  induction P;
  intros S PSV FS.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].
  
  3 : { unfold dub_neg_sub_ptree, dub_neg_sub_ptree_fit, dub_neg_sub_formula, formula_sub_ind in *.
        unfold ptree_formula in *.
        rewrite FS in *.
        unfold node_extract.
        reflexivity. }
  
    3-6,8-13,16-20 : 
        destruct S;
        inversion FS as [FS'];
        try rewrite FS';
        try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
    
    4-6,11,18,21 :
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
        try case form_eqb eqn:EQ;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite dub_neg_ptree_formula_true;
        repeat rewrite <- dub_neg_sub_formula_closed;
        repeat rewrite app_length;
        try rewrite IHP;
        try rewrite IHP1;
        try rewrite IHP2;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
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

  1 : try case (closed c) eqn:CC;
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ';
      unfold length;
      fold (@length formula);
      repeat rewrite app_length;
      try rewrite IHP;
      try rewrite IHP1;
      try rewrite IHP2;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
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

Lemma missing_non_ax_inv_other :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                forall (A : formula),
                    In A (node_extract (dub_neg_sub_ptree P E S)) ->
                        PA_cyclic_axiom A = true ->
                            A <> E ->
                                In A (node_extract P).
Proof.
intros P E S PSV FS A INA AX NE.
case (in_dec form_eq_dec A (node_extract P)) as [IN | NIN].
apply IN.
destruct (missing_non_ax_inv _ _ _ PSV FS _ INA NIN) as [FAL | [EQ _] ].
- rewrite AX in FAL.
  inversion FAL.
- contradict (NE EQ).
Qed.

Lemma missing_non_ax_other :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                forall (A : formula),
                    In A (node_extract P) ->
                        PA_cyclic_axiom A = false ->
                            A <> neg (neg E) ->
                                exists B, In B (node_extract (dub_neg_sub_ptree P E S)) /\ PA_cyclic_axiom B = false.
Proof.
  intros P E.
  induction P;
  intros S PSV FS A IN NAX NE.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].
  
  3 : { exists (dub_neg_sub_formula A E S).
        destruct IN as [EQ | FAL];
        try inversion FAL.
        destruct EQ.
        unfold dub_neg_sub_ptree, dub_neg_sub_ptree_fit, dub_neg_sub_formula, formula_sub_ind.
        unfold ptree_formula in *.
        rewrite FS.
        split.
        - apply (or_introl eq_refl).
        - destruct a;
          unfold formula_sub_ind_fit;
          fold formula_sub_ind_fit;
          unfold form_eqb;
          try reflexivity;
          try apply NAX;
          try destruct a;
          fold form_eqb;
          destruct S;
          try case form_eqb eqn:EQ;
          try reflexivity;
          try apply NAX.
          apply form_eqb_eq in EQ.
          destruct EQ.
          contradict (NE eq_refl). }
  
  3-6,8-13,16-20 : 
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,11,18,21 :
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
  
  all : try case form_eqb eqn:EQ;
        try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
        try apply in_app_or in IN as [IN1 | IN2];
        try apply (fun FSUB => IHP _ PSV FSUB A IN NAX NE);        
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
        try reflexivity;
        repeat rewrite <- dub_neg_sub_formula_closed in *.

  5-8,14-18,20,21 :
        exists A;
        split;
        try apply NAX;
        try apply IN;
        try apply (in_or_app _ _ _ (or_introl IN1));
        try apply (in_or_app _ _ _ (or_intror IN1));
        try apply (in_or_app _ _ _ (or_introl IN2));
        try apply (in_or_app _ _ _ (or_intror IN2)).

  11 : destruct (fun FSUB => IHP2 (lor_ind (0) S) P2SV FSUB A IN2 NAX NE) as [B2 [INB2 BAX2]].

  10 : destruct (fun FSUB => IHP1 (lor_ind (S) (non_target a)) P1SV FSUB A IN1 NAX NE) as [B1 [INB1 BAX1]].

  9 : destruct (fun FSUB => IHP2 (lor_ind (0) S2) P2SV FSUB A IN2 NAX NE) as [B1 [INB1 BAX1]].

  8 : destruct (fun FSUB => IHP1 (lor_ind (S1) (non_target a)) P1SV FSUB A IN1 NAX NE) as [B1 [INB1 BAX1]].

  1,2,3,4 : try destruct (fun FSUB => IHP1 (lor_ind (0) S2) P1SV FSUB A IN1 NAX NE) as [B1 [INB1 BAX1]];
            try destruct (fun FSUB => IHP2 (lor_ind (0) S2) P2SV FSUB A IN2 NAX NE) as [B2 [INB2 BAX2]].


  all : try exists B1;
        try exists B2;
        try split;
        try apply (in_or_app _ _ _ (or_introl INB1));
        try apply (in_or_app _ _ _ (or_intror INB1));
        try apply (in_or_app _ _ _ (or_intror INB2));
        try apply BAX1;
        try apply BAX2;
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


  3 : case (closed c) eqn:CC.

  4 : exists (univ n a);
      exact (conj (or_introl eq_refl) eq_refl).

  all : try case (free_list a) eqn:FREE;
        try destruct l;
        try case nat_eqb eqn:EQ.

  3,4,7,8,11,12 :
      exists (univ n a);
      exact (conj (or_introl eq_refl) eq_refl).

 1-4 :  exists A;
        try exact (conj IN NAX).

  all : apply in_app_or in IN as [IN1 | IN2].

  1,3 : exists A;
        try exact (conj (in_or_app _ _ _ (or_introl IN1)) NAX).

  all : destruct (fun FSUB => IHP1 (lor_ind S1 (non_target a)) P1SV FSUB A IN2 NAX NE) as [B1 [INB1 BAX1]];
        try exists B1;
        try split;
        try apply (in_or_app _ _ _ (or_intror INB1));
        try apply BAX1;
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

Lemma missing_non_ax_inv_better :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = false -> (exists (B : formula), In B (node_extract P) /\ PA_cyclic_axiom B = false)).
Proof.
  intros P E.
  induction P;
  intros S PSV FS A IN NAX.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].
  
  3 : { unfold dub_neg_sub_ptree in IN.
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
  
  3-6,8-13,16-20 : 
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,11,18,21 :
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

  3-4,9-13 :
      exists A;
      split;
      auto.

  1,2,6-8 :
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

  3 : rewrite <- dub_neg_sub_formula_closed in *;
      case (closed c) eqn:CC.

  1-3 : destruct (free_list a) eqn:FREE;
        try destruct l;
        try case nat_eqb eqn:EQ'.

  3,4,7,8,11-13 : 
      exists (univ n a);
      exact (conj (or_introl eq_refl) eq_refl).

  1-4 : exists A;
        exact (conj IN NAX).

  all : apply in_app_or in IN as [IN1 | IN2].

  1,3 : exists A;
        exact (conj (in_or_app _ _ _ (or_introl IN1)) NAX).

  all : destruct (fun FSUB => IHP1 _ P1SV FSUB A IN2 NAX) as [B1 [INB1 BAX1]];
        try exists B1;
        try split;
        try apply (in_or_app _ _ _ (or_intror INB1));
        try apply BAX1;
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
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.
Qed.
  

Lemma missing_non_ax_inv_better_4 :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> (exists (B : formula) (SUB : subst_ind), subst_ind_fit B SUB = true /\ A = dub_neg_sub_formula B E SUB /\ In B (node_extract P))).
Proof.
intros P E.
induction P;
intros S PSV FS A IN.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-23: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3 : { unfold dub_neg_sub_ptree in IN.
      rewrite FS in IN.
      unfold dub_neg_sub_ptree_fit in IN.
      destruct IN as [EQ | FAL];
      try inversion FAL.
      destruct EQ.
      exists a, S.
      simpl in *.
      auto. }

3-6,8-15,18-22 : 
    destruct S;
    inversion FS as [FS'];
    try rewrite FS';
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,11,15,16,20 :
    destruct S1;
    inversion FS' as [FS''];
    try rewrite FS'';
    try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
    inversion FS'' as [FS'''];
    try rewrite FS''';
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

20 :  destruct S2;
      inversion FS2 as [FS''];
      try rewrite FS''.

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
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => IHP _ PSV FSUB A IN);
      try apply (fun FSUB => IHP1 _ P1SV FSUB A IN1);
      try apply (fun FSUB => IHP2 _ P2SV FSUB A IN2);
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

21-22 : try case (in_dec form_eq_dec A (node_extract (dub_neg_sub_ptree P E (0)))) as [IN' | NIN'];
        try apply (fun FSUB => IHP (0) PSV FSUB _ IN');
        try rewrite PF;
        try reflexivity;
        try exists A, (non_target A);
        unfold dub_neg_sub_formula;
        try rewrite non_target_fit, non_target_sub;
        try rewrite PF;
        auto.

18-20 : try case (in_dec form_eq_dec A (node_extract (dub_neg_sub_ptree P E (non_target a)))) as [IN' | NIN'];
        try apply (fun FSUB => IHP (0) PSV FSUB _ IN');
        try rewrite PF;
        try reflexivity;
        try exists A, (non_target A);
        unfold dub_neg_sub_formula;
        try rewrite non_target_fit, non_target_sub;
        try rewrite PF;
        try rewrite non_target_fit;
        repeat split;
        auto.

all :   try destruct (fun FSUB => IHP1 (lor_ind (0) S2) P1SV FSUB _ IN1) as [B [SB [FSB [FEQ INB]]]];
        try destruct (fun FSUB => IHP2 (lor_ind (0) S2) P2SV FSUB _ IN2) as [B [SB [FSB [FEQ INB]]]];
        try destruct (fun FSUB => IHP1 (lor_ind S1 (non_target a)) P1SV FSUB _ IN1) as [B [SB [FSB [FEQ INB]]]];
        try destruct (fun FSUB => IHP1 (lor_ind S (non_target a)) P1SV FSUB _ IN1) as [B [SB [FSB [FEQ INB]]]];
        try destruct (fun FSUB => IHP2 (lor_ind (0) S) P2SV FSUB _ IN2) as [B [SB [FSB [FEQ INB]]]];
        try rewrite P1F;
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS2;
        try rewrite FS1;
        try rewrite FS;
        try rewrite non_target_fit;
        try reflexivity;
        try exists B, SB;
        repeat split;
        auto;
        try apply (in_or_app _ _ _ (or_introl INB));
        try apply (in_or_app _ _ _ (or_intror INB)).

4,5,6,7,12,13 : try exists A, (non_target A);
      unfold dub_neg_sub_formula;
      try rewrite non_target_fit, non_target_sub;
      try rewrite (fun FSUB => missing_non_ax _ _ _ PSV FSUB _ IN NIN');
      try rewrite PF;
      try rewrite non_target_fit;
      try rewrite NAX;
      repeat split;
      try apply (in_or_app _ _ _ (or_introl IN1));
      try apply (in_or_app _ _ _ (or_intror IN2)).

all : repeat rewrite <- dub_neg_sub_formula_closed in *;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      destruct (free_list a) eqn:FREE;
      try destruct l;
      try case nat_eqb eqn:EQ';
      try destruct IN as [EQ | IN];
      try apply in_app_or in IN as [IN1 | IN2].



Admitted.


Lemma missing_non_ax_inv_better_2 :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = false -> (exists (B : formula) (SUB : subst_ind), subst_ind_fit B SUB = true /\ A = dub_neg_sub_formula B E SUB /\ In B (node_extract P) /\ PA_cyclic_axiom B = false)).
Proof.
intros P E.
induction P;
intros S PSV FS A IN NAX.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-23: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3 : { unfold dub_neg_sub_ptree in IN.
      rewrite FS in IN.
      unfold dub_neg_sub_ptree_fit in IN.
      destruct IN as [EQ | FAL];
      try inversion FAL.
      destruct EQ.
      case (PA_cyclic_axiom a) eqn:AX.
      - rewrite (dub_neg_axiom_id _ _ _ AX) in NAX.
        rewrite AX in NAX.
        inversion NAX.
      - unfold ptree_formula in FS.
        unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit in *;
        rewrite FS in *.
        unfold PA_cyclic_axiom in AX;
        destruct a;
        inversion AX as [AX'];
        fold formula_sub_ind_fit in *;
        unfold form_eqb in *;
        fold form_eqb in *.
        + exists (atom a), S.
          rewrite FS.
          simpl.
          auto.
        + destruct S;
          inversion FS as [FS'].
          * case form_eqb eqn:EQ;
            exists (neg a), (0);
            rewrite FS;
            simpl;
            try rewrite EQ;
            auto.
          * case form_eqb eqn:EQ.
            --  apply form_eqb_eq in EQ.
                rewrite EQ in *.
                exists (neg (neg E)), (1).
                simpl.
                rewrite form_eqb_refl.
                auto.
            --  exists (neg a), (0).
                simpl.
                rewrite EQ.
                auto.
        + destruct S;
          inversion FS as [FS'].
          exists (lor a1 a2), (lor_ind S1 S2).
          rewrite FS.
          simpl.
          auto.
        + exists (univ n a), (S).
          rewrite FS.
          simpl.
          auto. }

3-6,8-15,18-22 : 
    destruct S;
    inversion FS as [FS'];
    try rewrite FS';
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,11,15,16,20 :
    destruct S1;
    inversion FS' as [FS''];
    try rewrite FS'';
    try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
    inversion FS'' as [FS'''];
    try rewrite FS''';
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

20 :  destruct S2;
      inversion FS2 as [FS''];
      try rewrite FS''.

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
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => IHP _ PSV FSUB A IN NAX);
      try apply (fun FSUB => IHP1 _ P1SV FSUB A IN1 NAX);
      try apply (fun FSUB => IHP2 _ P2SV FSUB A IN2 NAX);
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

21-22 : try case (in_dec form_eq_dec A (node_extract (dub_neg_sub_ptree P E (0)))) as [IN' | NIN'];
        try apply (fun FSUB => IHP (0) PSV FSUB _ IN' NAX);
        try rewrite PF;
        try reflexivity;
        try exists A, (non_target A);
        unfold dub_neg_sub_formula;
        try rewrite non_target_fit, non_target_sub;
        try rewrite (fun FSUB => missing_non_ax _ _ _ PSV FSUB _ IN NIN');
        try rewrite PF;
        auto.

18-20 : try case (in_dec form_eq_dec A (node_extract (dub_neg_sub_ptree P E (non_target a)))) as [IN' | NIN'];
        try apply (fun FSUB => IHP (0) PSV FSUB _ IN' NAX);
        try rewrite PF;
        try reflexivity;
        try exists A, (non_target A);
        unfold dub_neg_sub_formula;
        try rewrite non_target_fit, non_target_sub;
        try rewrite (fun FSUB => missing_non_ax _ _ _ PSV FSUB _ IN NIN');
        try rewrite PF;
        try rewrite non_target_fit;
        repeat split;
        auto.

all :   try destruct (fun FSUB => IHP1 (lor_ind (0) S2) P1SV FSUB _ IN1 NAX) as [B [SB [FSB [FEQ [INB BNAX]]]]];
        try destruct (fun FSUB => IHP2 (lor_ind (0) S2) P2SV FSUB _ IN2 NAX) as [B [SB [FSB [FEQ [INB BNAX]]]]];
        try destruct (fun FSUB => IHP1 (lor_ind S1 (non_target a)) P1SV FSUB _ IN1 NAX) as [B [SB [FSB [FEQ [INB BNAX]]]]];
        try destruct (fun FSUB => IHP1 (lor_ind S (non_target a)) P1SV FSUB _ IN1 NAX) as [B [SB [FSB [FEQ [INB BNAX]]]]];
        try destruct (fun FSUB => IHP2 (lor_ind (0) S) P2SV FSUB _ IN2 NAX) as [B [SB [FSB [FEQ [INB BNAX]]]]];
        try rewrite P1F;
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS2;
        try rewrite FS1;
        try rewrite FS;
        try rewrite non_target_fit;
        try reflexivity;
        try exists B, SB;
        repeat split;
        auto;
        try apply (in_or_app _ _ _ (or_introl INB));
        try apply (in_or_app _ _ _ (or_intror INB)).

4,5,6,7,12,13 : try exists A, (non_target A);
      unfold dub_neg_sub_formula;
      try rewrite non_target_fit, non_target_sub;
      try rewrite (fun FSUB => missing_non_ax _ _ _ PSV FSUB _ IN NIN');
      try rewrite PF;
      try rewrite non_target_fit;
      try rewrite NAX;
      repeat split;
      try apply (in_or_app _ _ _ (or_introl IN1));
      try apply (in_or_app _ _ _ (or_intror IN2)).

all : repeat rewrite <- dub_neg_sub_formula_closed in *;
      try case (closed c) eqn:CC.

4,8,10 : destruct IN as [EQ | IN].

4,6,8 : exists (univ n a), (0);
      destruct EQ;
      unfold dub_neg_sub_formula, formula_sub_ind;
      simpl;
      auto.


4-6 : admit.

all : try case (closed d) eqn:CD.

2,4,6 : destruct IN as [EQ | IN].

2,4,6 : exists (univ n a), (0);
        destruct EQ;
        unfold dub_neg_sub_formula, formula_sub_ind;
        simpl;
        auto.

2-4 : admit.

all : destruct (free_list a);
      try destruct l.

3,6,9,12,15,18,21 : destruct IN as [EQ | IN].

3,5,7,9,11,13,15 :
    exists (univ n a), (0);
    destruct EQ;
    unfold dub_neg_sub_formula, formula_sub_ind;
    simpl;
    auto.

3-9 : admit.

2,4,6,8,10,12,14 : case nat_eqb eqn:EQ'.

3,5,7,9,11,13,15 : destruct IN as [EQ | IN].

3,5,7,9,11,13,15 :
    exists (univ n a), (0);
    destruct EQ;
    unfold dub_neg_sub_formula, formula_sub_ind;
    simpl;
    auto.

3-9 : admit.

all : admit.
Admitted.

Lemma missing_non_ax_inv_hard :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> ~ In A (node_extract P) -> (exists (B : formula) (SUB : subst_ind), subst_ind_fit B SUB = true /\ A = dub_neg_sub_formula B E SUB /\ In B (node_extract P) /\ PA_cyclic_axiom B = false) \/ (A = E /\ PA_cyclic_axiom E = true)).
Proof.
intros P E.
induction P;
intros S PSV FS A IN NIN.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-23: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3 : { unfold dub_neg_sub_ptree in IN.
      rewrite FS in IN.
      unfold dub_neg_sub_ptree_fit in IN.
      destruct IN as [EQ | FAL];
      try inversion FAL.
      destruct EQ.
      case (PA_cyclic_axiom a) eqn:AX.
      - rewrite (dub_neg_axiom_id _ _ _ AX) in NIN.
        contradict (NIN (or_introl eq_refl)).
      - unfold ptree_formula in FS.
        unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit in *;
        rewrite FS in *.
        unfold PA_cyclic_axiom in AX;
        destruct a;
        inversion AX as [AX'];
        fold formula_sub_ind_fit in *;
        unfold form_eqb;
        fold form_eqb.
        + contradict (NIN (or_introl eq_refl)).
        + destruct a;
          inversion AX as [AX''];
          unfold form_eqb in *;
          fold form_eqb in *;
          try case form_eqb eqn:EQ;
          try destruct S;
          try contradict (NIN (or_introl eq_refl)).
          case (PA_cyclic_axiom E); auto.
          apply form_eqb_eq in EQ.
          destruct EQ.
          left.
          exists (neg (neg a)), (1).
          rewrite FS.
          unfold formula_sub_ind_fit;
          rewrite form_eqb_refl.
          repeat split.
          apply (or_introl eq_refl).
        + destruct S;
          try contradict (NIN (or_introl eq_refl)).
          left.
          exists (lor a1 a2), (lor_ind S1 S2).
          rewrite FS.
          repeat split.
          apply (or_introl eq_refl).
        + contradict (NIN (or_introl eq_refl)). }

3-6,8-15,18-22 : 
    destruct S;
    inversion FS as [FS'];
    try rewrite FS';
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,11,15,16,20 :
    destruct S1;
    inversion FS' as [FS''];
    try rewrite FS'';
    try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
    inversion FS'' as [FS'''];
    try rewrite FS''';
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

20 :  destruct S2;
      inversion FS2 as [FS''];
      try rewrite FS''.

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
      try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => IHP _ PSV FSUB A IN NIN);
      try apply (fun FSUB => IHP1 _ P1SV FSUB A IN1 NIN1);
      try apply (fun FSUB => IHP2 _ P2SV FSUB A IN2 NIN2);
      try contradict (NIN IN);
      try contradict (NIN1 IN1);
      try contradict (NIN2 IN2);
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
      try reflexivity;
      repeat rewrite <- dub_neg_sub_formula_closed in *;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      try case (free_list a) eqn:FREE;
      try case nat_eqb eqn:EQ;
      try destruct l;
      try destruct IN as [EQ' | IN];
      try destruct EQ';
      auto;
      try apply not_in_cons in NIN as [NE' NIN];
      try apply (nin_split form_eq_dec) in NIN as [NIN1 NIN2];
      try apply in_app_or in IN as [IN1 | IN2];
      try contradict (NIN1 IN1);
      try contradict (NIN1 IN2);
      try contradict (NIN2 IN1);
      try contradict (NIN2 IN2);
      try apply in_remove in IN1 as [IN1 NE1];
      try apply (nin_ne_weaken _ _ _ _ NE1) in NIN1;
      try destruct (fun FSUB => IHP1 _ P1SV FSUB _ IN2 NIN2);
      try destruct (IHP2 _ P2SV _ _ IN1 NIN1);
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
      try reflexivity;
      try contradict (NE' eq_refl).
Admitted.
*)

Lemma all_ax : 
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                    (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true).
Proof.
intros P E S PSV FS PAX A INA.
case (in_dec form_eq_dec A (node_extract P)) as [IN | NIN].
- apply (PAX _ IN).
- 
(*destruct (missing_non_ax_inv_hard _ _ _ PSV FS _ INA NIN) as [[B [S' [FS' [EQ FAL]]]] | [EQ AX]].
 + admit.
 + destruct EQ.
   apply AX. *)
Admitted.

Lemma dub_neg_node_eq_aux :
    forall (L : list formula),
        forall (P : ptree) (E : formula) (S : subst_ind),
            L = node_extract P ->
                struct_valid P ->
                    subst_ind_fit (ptree_formula P) S = true ->
                        (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                            (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true).
Proof.
induction L as [L IND] using (induction_ltof1 _ (@length _)); unfold ltof in IND.
induction P;
intros E S EQ PSV FS PAX A IN;
unfold dub_neg_sub_ptree in *;
unfold node_extract, dub_neg_sub_ptree_fit, ptree_formula, ptree_ord in *;
fold ptree_formula ptree_ord dub_neg_sub_ptree_fit in *;
try rewrite FS in *;
fold node_extract in *;
try rewrite (dub_neg_ptree_formula_true _ _ _ FS).

1 : destruct PSV as [LT PSV]. (*deg up*)
2 : destruct PSV as [[LT PSV] NO]. (*ord up*)
3 : destruct PSV as []. (*node*)
4-9,13-16 :  destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF CPF] PSV] PD] PO]. (*weakening*)
15-23 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O]. (*double hyp*)

1 : apply (IHP E _ EQ PSV FS PAX).
    rewrite FS.
    apply IN.

1 : apply (IHP E _ EQ PSV FS PAX).
    rewrite FS.
    apply IN.

1 : { specialize (PAX _ (or_introl eq_refl)).
      destruct a;
      try destruct a;
      inversion PAX as [AX'];
      unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb in IN;
      rewrite FS in IN;
      inversion IN as [EQ' | FAL];
      try inversion FAL;
      destruct EQ';
      reflexivity. }

all : try apply (PAX _ IN);
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try apply and_bool_prop in FS' as [FS1 FS2];
      rewrite EQ in *.

2-4,11,12,14,16,17 : destruct S1;
            inversion FS as [FS'];
            try rewrite FS';
            try apply and_bool_prop in FS1 as [FS1 FS3].

4 : destruct S1_1;
    inversion FS as [FS''];
    rewrite FS'';
    try apply and_bool_prop in FS1 as [FS1 FS4].

6,19 : case form_eqb eqn:EQ'.

16 :  destruct S1_2;
      inversion FS as [FS''];
      rewrite FS'';
      try apply and_bool_prop in FS3 as [FS3 FS4].

all : unfold node_extract in *;
      fold node_extract in *;
      try rewrite dub_neg_ptree_formula_true in IN;
      try rewrite dub_neg_ptree_formula_true in IN;
      try refine (IHP _ _ eq_refl PSV _ PAX _ IN);
      (*try refine (IND _ (ptree_ord_nf_struct_hyp _ _ PO PSV) (ord_succ_monot _) _ _ _ PO PSV _ PAX _ IN);*)
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.

1,2 : pose proof (IND _ struct_node_sum_less_l _ E (lor_ind (0) S2) eq_refl P1SV) as TEMP1;
      pose proof (IND _ struct_node_sum_less_r _ E (lor_ind (0) S2) eq_refl P2SV) as TEMP2.
9 : pose proof (IND _ struct_node_sum_less_l  _ E (lor_ind (0) (non_target a)) eq_refl P1SV) as TEMP1.
10 : pose proof (IND _ struct_node_sum_less_l _ E (lor_ind (1) (non_target a)) eq_refl P1SV) as TEMP1.
11 : pose proof (IND _ struct_node_sum_less_l _ E (lor_ind (lor_ind S1 S2) (non_target a)) eq_refl P1SV) as TEMP1.
12 : pose proof (IND _ struct_node_sum_less_r _ E (lor_ind (0) (0)) eq_refl P2SV) as TEMP2.
13 : pose proof (IND _ struct_node_sum_less_r _ E (lor_ind (0) (1)) eq_refl P2SV) as TEMP2.
14 : pose proof (IND _ struct_node_sum_less_r _ E (lor_ind (0) (lor_ind S1 S2)) eq_refl P2SV) as TEMP2.
15 : pose proof (IND _ struct_node_sum_less_l _ E (lor_ind S1 (non_target a)) eq_refl P1SV) as TEMP1;
     pose proof (IND _ struct_node_sum_less_r _ E (lor_ind (0) S2) eq_refl P2SV) as TEMP2.

all : try rewrite dub_neg_ptree_formula_true in *;
      rewrite P1F in *;
      rewrite P2F in *;
      unfold subst_ind_fit in *;
      fold subst_ind_fit in *;      
      try rewrite FS' in *;
      try rewrite FS1 in *;
      try rewrite FS2 in *;
      try rewrite non_target_fit in *;
      unfold "&&" in *;
      try reflexivity;
      try specialize (TEMP1 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_introl INB))));
      try specialize (TEMP2 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_intror INB))));
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (TEMP1 _ IN1);
      try apply (TEMP2 _ IN2);
      try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
      try apply (PAX _ (in_or_app _ _ _ (or_intror IN2))).

all : repeat rewrite <- dub_neg_sub_formula_closed in *;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ';
      try pose proof (PAX _ (or_introl eq_refl)) as FAL;
      try inversion FAL.
      admit.
      admit.
      admit.
      admit.


{ try apply in_app_or in IN as [IN1 | IN2];
  try apply (TEMP1 _ IN1);
  try apply (TEMP2 _ IN2);
  try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
  try apply (PAX _ (in_or_app _ _ _ (or_intror IN2))).
  (*assert (length (node_extract P1) < length ((f :: l) ++ node_extract P1)) as IE. { rewrite app_length. simpl. lia. }
    pose proof (IND _ IE _ E (non_target a) eq_refl P1SV) as TEMP1. *)
    pose proof (IND _ struct_node_sum_less_r _ E (lor_ind (non_target a) S2) _ P2SV) as TEMP2.
      try rewrite P1F in *;
      try rewrite P2F in *;
      unfold subst_ind_fit in *;
      fold subst_ind_fit in *;
      try rewrite FS' in *;
      try rewrite FS1 in *;
      try rewrite FS2 in *;
      try rewrite non_target_fit in *;
      try rewrite non_target_sub_fit in *;
      unfold "&&" in *.
      specialize (TEMP1 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_intror INB)))).
      specialize (TEMP2 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_introl INB)))).
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.
*)

(*
Lemma dub_neg_node_eq_aux :
    forall (alpha : ord),
        nf alpha ->
            forall (P : ptree) (E : formula) (S : subst_ind),
                alpha = ptree_ord P ->
                    struct_valid P ->
                        subst_ind_fit (ptree_formula P) S = true ->
                            (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true).
Proof.
apply (transfinite_induction (fun (alpha : ord) => (forall (P : ptree) (E : formula) (S : subst_ind), alpha = ptree_ord P -> struct_valid P -> subst_ind_fit (ptree_formula P) S = true -> (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
(forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true)))).
intros alpha NA IND.
induction P;
intros E S EQ PSV FS PAX A IN;
unfold dub_neg_sub_ptree in *;
unfold node_extract, dub_neg_sub_ptree_fit, ptree_formula, ptree_ord in *;
fold ptree_formula ptree_ord dub_neg_sub_ptree_fit in *;
try rewrite FS in *;
fold node_extract in *;
try rewrite (dub_neg_ptree_formula_true _ _ _ FS).

1 : destruct PSV as [LT PSV]. (*deg up*)
2 : destruct PSV as [[LT PSV] NO]. (*ord up*)
3 : destruct PSV as []. (*node*)
4-9,13-16 :  destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF CPF] PSV] PD] PO]. (*weakening*)
15-23 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O]. (*double hyp*)

1 : apply (IHP E _ EQ PSV FS PAX).
    rewrite FS.
    apply IN.

1 : destruct EQ;
    apply (IND _ (ptree_ord_nf_struct _ PSV) LT _ E _ eq_refl PSV FS PAX).
    rewrite FS.
    apply IN.

1 : { specialize (PAX _ (or_introl eq_refl)).
      destruct a;
      try destruct a;
      inversion PAX as [AX'];
      unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb in IN;
      rewrite FS in IN;
      inversion IN as [EQ' | FAL];
      try inversion FAL;
      destruct EQ';
      reflexivity. }

all : try apply (PAX _ IN);
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try apply and_bool_prop in FS' as [FS1 FS2];
      rewrite EQ in *.

2-4,11,12,14,16,17 : destruct S1;
            inversion FS as [FS'];
            try rewrite FS';
            try apply and_bool_prop in FS1 as [FS1 FS3].

4 : destruct S1_1;
    inversion FS as [FS''];
    rewrite FS'';
    try apply and_bool_prop in FS1 as [FS1 FS4].

6,19 : case form_eqb eqn:EQ'.

16 :  destruct S1_2;
      inversion FS as [FS''];
      rewrite FS'';
      try apply and_bool_prop in FS3 as [FS3 FS4].

all : unfold node_extract in *;
      fold node_extract in *;
      try rewrite dub_neg_ptree_formula_true in IN;
      try rewrite dub_neg_ptree_formula_true in IN;
      try refine (IHP _ _ PO PSV _ PAX _ IN);
      try refine (IND _ (ptree_ord_nf_struct_hyp _ _ PO PSV) (ord_succ_monot _) _ _ _ PO PSV _ PAX _ IN);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.

1,2 : pose proof (IND _ struct_node_sum_less_l (ord_lt_max_succ_l _ _) _ E (lor_ind (0) S2) P1O P1SV) as TEMP1;
      pose proof (IND _ struct_node_sum_less_r (ord_lt_max_succ_r _ _) _ E (lor_ind (0) S2) P2O P2SV) as TEMP2.
9 : pose proof (IND _ struct_node_sum_less_l (ord_lt_max_succ_l _ _) _ E (lor_ind (0) (non_target a)) P1O P1SV) as TEMP1.
10 : pose proof (IND _ struct_node_sum_less_l (ord_lt_max_succ_l _ _) _ E (lor_ind (1) (non_target a)) P1O P1SV) as TEMP1.
11 : pose proof (IND _ struct_node_sum_less_l (ord_lt_max_succ_l _ _) _ E (lor_ind (lor_ind S1 S2) (non_target a)) P1O P1SV) as TEMP1.
12 : pose proof (IND _ struct_node_sum_less_r (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)) _ E (lor_ind (0) (0)) P2O P2SV) as TEMP2.
13 : pose proof (IND _ struct_node_sum_less_r (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)) _ E (lor_ind (0) (1)) P2O P2SV) as TEMP2.
14 : pose proof (IND _ struct_node_sum_less_r (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)) _ E (lor_ind (0) (lor_ind S1 S2)) P2O P2SV) as TEMP2.
15 : pose proof (IND _ struct_node_sum_less_l (ord_lt_max_succ_l _ _) _ E (lor_ind S1 (non_target a)) P1O P1SV) as TEMP1;
     pose proof (IND _ struct_node_sum_less_r (ord_lt_max_succ_r _ _) _ E (lor_ind (0) S2) P2O P2SV) as TEMP2.

all : try rewrite dub_neg_ptree_formula_true in *;
      rewrite P1F in *;
      rewrite P2F in *;
      unfold subst_ind_fit in *;
      fold subst_ind_fit in *;      
      try rewrite FS' in *;
      try rewrite FS1 in *;
      try rewrite FS2 in *;
      try rewrite non_target_fit in *;
      unfold "&&" in *;
      try reflexivity;
      try specialize (TEMP1 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_introl INB))));
      try specialize (TEMP2 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_intror INB))));
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (TEMP1 _ IN1);
      try apply (TEMP2 _ IN2);
      try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
      try apply (PAX _ (in_or_app _ _ _ (or_intror IN2))).

all : repeat rewrite <- dub_neg_sub_formula_closed in *;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ'.

{ 

      pose proof (IND _ struct_node_sum_less_l (lt_succ_mult_add_r _ _) _ E (lor_ind (non_target a) S2) P1O P1SV) as TEMP1.
      pose proof (IND _ struct_node_sum_less_r (lt_succ_mult_add_l _ _) _ E (lor_ind (non_target a) S2) P2O P2SV) as TEMP2.
      try rewrite P1F in *;
      try rewrite P2F in *;
      unfold subst_ind_fit in *;
      fold subst_ind_fit in *;
      try rewrite FS' in *;
      try rewrite FS1 in *;
      try rewrite FS2 in *;
      try rewrite non_target_fit in *;
      try rewrite non_target_sub_fit in *;
      unfold "&&" in *;
      try specialize (TEMP1 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_intror INB)))).
      specialize (TEMP2 eq_refl (fun B INB => PAX _ (in_or_app _ _ _ (or_introl INB)))).
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.
Admitted.
*)

Lemma dub_neg_node_eq_aux :
    forall (alpha : ord),
        nf alpha ->
            (forall (P : ptree) (E : formula) (S : subst_ind),
                alpha = ptree_ord P ->
                    struct_valid P ->
                        subst_ind_fit (ptree_formula P) S = true ->
                            node_extract P = node_extract (dub_neg_sub_ptree P E S)).
Proof.
apply (transfinite_induction (fun (alpha : ord) => (forall (P : ptree) (E : formula) (S : subst_ind), alpha = ptree_ord P -> struct_valid P -> subst_ind_fit (ptree_formula P) S = true -> node_extract P = node_extract (dub_neg_sub_ptree P E S)))).
intros alpha NA IND.
induction P;
intros E S EQ PSV FS;
unfold dub_neg_sub_ptree;
unfold node_extract, dub_neg_sub_ptree_fit, ptree_formula, ptree_ord in *;
fold ptree_formula ptree_ord dub_neg_sub_ptree_fit in *;
rewrite FS in *;
fold node_extract in *;
try rewrite (dub_neg_ptree_formula_true _ _ _ FS).

1 : destruct PSV as [LT PSV]. (*deg up*)
2 : destruct PSV as [[LT PSV] NO]. (*ord up*)
3 : destruct PSV as []. (*node*)
4-9,13-16 :  destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF CPF] PSV] PD] PO]. (*weakening*)
15-23 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O]. (*double hyp*)

1 : apply (IHP _ _ EQ PSV FS).

1 : destruct EQ;
    apply (IND _ (ptree_ord_nf_struct _ PSV) LT _ _ _ eq_refl PSV FS).

1 : {  }

all : try reflexivity;
      destruct S;
      inversion FS as [FS'];
      try apply and_bool_prop in FS' as [FS1 FS2];
      rewrite EQ in *.

2-4,11,12,14,16,17 : destruct S1;
            inversion FS as [FS'];
            try apply and_bool_prop in FS1 as [FS1 FS3].

4 : destruct S1_1;
    inversion FS as [FS''];
    try apply and_bool_prop in FS1 as [FS1 FS4].

6,19 : case form_eqb eqn:EQ'.

16 :  destruct S1_2;
      inversion FS as [FS''];
      try apply and_bool_prop in FS3 as [FS3 FS4].

all : unfold node_extract;
      fold node_extract;
      repeat rewrite dub_neg_ptree_formula_true;
      try apply (IHP _ _ PO);
      try refine (IND _ (ptree_ord_nf_struct_hyp _ _ PO PSV) (ord_succ_monot _) _ _ _ PO PSV _);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P1O P1SV) (ord_lt_max_succ_l _ _) _ _ (lor_ind _ (non_target a)) P1O P1SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P1O P1SV) (ord_lt_max_succ_l _ _) _ _ (lor_ind (0) S2) P1O P1SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P2O P2SV) (ord_lt_max_succ_r _ _) _ _ (lor_ind (0) _) P2O P2SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P2O P2SV) (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)) _ _ _ P2O P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.

all : repeat rewrite <- dub_neg_sub_formula_closed;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ';
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P1O P1SV) (lt_succ_mult_add_r _ _) _ _ _ P1O P1SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P2O P2SV) (lt_succ_mult_add_l _ _) _ _ _ P2O P2SV);
      try reflexivity;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.
Admitted.

Lemma dub_neg_node_eq :
    (forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
                node_extract P = node_extract (dub_neg_sub_ptree P E S)).
Proof.
intros P E S PSV.
unfold dub_neg_sub_ptree.
case subst_ind_fit eqn:FS.
- rewrite (dub_neg_ptree_formula_true _ _ _ FS).
  apply (dub_neg_node_eq_aux (ptree_ord P) (ptree_ord_nf_struct _ PSV) _ _ _ eq_refl PSV FS).
- reflexivity.
Qed.

(*
Lemma problem :
    forall (P : ptree) (A D E : formula) (S : subst_ind),
        ptree_formula P = lor A D ->
            struct_valid P ->
                subst_ind_fit D S = true ->
                    closed D = true ->
                      (forall (B : formula), In B (remove form_eq_dec A (node_extract P)) -> PA_cyclic_axiom B = true) ->
                          struct_valid (dub_neg_sub_ptree P E (lor_ind (non_target A) S)).
Proof.
induction P;
intros A D E S FEQ PSV FS CD PAX;
unfold dub_neg_sub_ptree;
unfold ptree_formula in *;
fold ptree_formula in *;
try rewrite FEQ;
unfold subst_ind_fit;
fold subst_ind_fit;
rewrite non_target_fit, FS;
unfold "&&";
unfold dub_neg_sub_ptree_fit;
fold dub_neg_sub_ptree_fit;
try apply PSV.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11,12 : destruct PSV as [[[PF PSV] PD] PO].
10,13-18: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

2 : { rewrite dub_neg_ptree_formula_true.
      repeat split.
      rewrite dub_neg_ptree_ord_struct.
      apply IO.
      apply PSV.
      apply (IHP A D E S FEQ PSV FS CD PAX).
      apply NO.
      rewrite FEQ.
      unfold subst_ind_fit;
      fold subst_ind_fit.
      rewrite non_target_fit.
      apply FS. }

1 : { rewrite dub_neg_ptree_formula_true.
      repeat split.
      rewrite dub_neg_ptree_deg_struct.
      apply ID.
      apply PSV.
      apply (IHP A D E S FEQ PSV FS CD PAX).
      rewrite FEQ.
      unfold subst_ind_fit;
      fold subst_ind_fit.
      rewrite non_target_fit.
      apply FS. }

all : inversion FEQ;
      unfold non_target;
      fold non_target;
      try destruct H0;
      try destruct H1.

7 : assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
7 : { unfold closed; fold closed;
      intros CE;
      apply CE. }

all : repeat rewrite dub_neg_ptree_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite FEQ;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      repeat rewrite FS;
      try reflexivity.

{ repeat split.
admit.
Admitted.
*)

Lemma dub_neg_struct_valid :
    forall (alpha : ord),
        nf alpha ->
            forall (P : ptree) (E : formula),
                ptree_ord P = alpha ->
                    struct_valid P ->
                        forall (S : subst_ind),
                            subst_ind_fit (ptree_formula P) S = true ->
                                struct_valid (dub_neg_sub_ptree P E S).
Proof.
apply (transfinite_induction (fun alpha => forall (P : ptree) (E : formula), ptree_ord P = alpha -> struct_valid P -> forall (S : subst_ind), subst_ind_fit (ptree_formula P) S = true -> struct_valid (dub_neg_sub_ptree P E S))).
intros alpha NA Ind P.
induction P;
intros E OEQ PSV S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_ord, ptree_formula in *;
fold ptree_ord ptree_formula in *;
unfold dub_neg_sub_ptree_fit;
fold dub_neg_sub_ptree_fit.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-23: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

4-7,9,10,12,14-16,19-23 :
  destruct S;
  inversion FS as [FS'];
  try apply and_bool_prop in FS' as [FS1 FS2].

5-7,13,17 :
  destruct S1;
  inversion FS as [FS''];
  try apply and_bool_prop in FS1 as [FS1 FS3].

7 : destruct S1_1;
    inversion FS as [FS'''];
    apply and_bool_prop in FS1 as [FS1 FS4].

10,18 : case (form_eqb a E) eqn:FEQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite FEQ;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      repeat rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS3;
      try rewrite FS4;
      try reflexivity;
      repeat split;
      repeat rewrite dub_neg_ptree_deg_struct;
      repeat rewrite dub_neg_ptree_ord_struct;
      try apply ID;
      try apply IO;
      try apply NO;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply PF;
      try apply P1F;
      try apply P2F;
      try rewrite PO in *;
      try apply ord_succ_monot;
      try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

23 : { admit. }

all : try apply (IHP E OEQ PSV);      
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite FEQ;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      repeat rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS3;
      try rewrite FS4;
      try reflexivity.
Admitted.

(*
Lemma dub_neg_struct_valid_2 :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    (forall A : formula, In A (node_extract P) /\ (PA_cyclic_axiom A = false) -> ~ In A (target_check (ptree_formula P) S)) ->
                        struct_valid (dub_neg_sub_ptree P E S).
Proof.
intros P E PSV.
induction P; try intros S FS NonTar;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold node_extract in NonTar;
fold node_extract in NonTar.

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

9,23 : case (form_eqb a E) eqn:EQ.

17 :  { repeat split;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite P2F;
        try rewrite dub_neg_ptree_formula_struct;
        try rewrite P2F;
        unfold dub_neg_sub_formula, formula_sub_ind;
        unfold subst_ind_fit, formula_sub_ind_fit;
        fold subst_ind_fit formula_sub_ind_fit;
        try rewrite non_target_sub_fit;
        try rewrite non_target_sub_term';
        try rewrite FS2;
        unfold "&&";
        try rewrite dub_neg_ptree_deg_struct;
        try rewrite dub_neg_ptree_ord_struct;
        auto.

        apply (IHP2 P2SV);
        rewrite P2F.

        2 : { unfold subst_ind_fit;
              fold subst_ind_fit.
              rewrite non_target_sub_fit.
              apply FS2. }

        1 : 
        
        admit. }
16 : { admit. }
7 : { admit. }

all : try apply form_eqb_eq in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg_struct;
      try rewrite dub_neg_ptree_ord_struct;
      try rewrite dub_neg_ptree_formula_struct;
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
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity;
      try apply PSV;
      try apply NonTar.
  (*
1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply FC.
      reflexivity. }

all : try case form_eqb eqn:EQ;
      try reflexivity;
      try rewrite <- (dub_neg_node_eq _ _ _ P1SV);
      try rewrite <- (dub_neg_node_eq _ _ _ P2SV);
      apply PAX. *)
Admitted.
*)

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

3 : { repeat split.
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

9,23 : case (form_eqb a E) eqn:EQ.

17 :  { pose proof PAX as PAX2.
        unfold node_extract in PAX;
        fold node_extract in PAX.
        case (closed d) eqn:CD;
        case (free_list a) eqn:FREE;
        try destruct l;
        try case nat_eqb eqn:EQ;
        try pose proof (PAX _ (or_introl eq_refl)) as FAL;
        try inversion FAL;
        repeat split;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite P2F;
        try rewrite dub_neg_ptree_formula_struct;
        try rewrite P2F;
        unfold dub_neg_sub_formula, formula_sub_ind;
        unfold subst_ind_fit, formula_sub_ind_fit;
        fold subst_ind_fit formula_sub_ind_fit;
        try rewrite non_target_sub_fit;
        try rewrite non_target_sub_term';
        try rewrite FS2;
        unfold "&&";
        try rewrite dub_neg_ptree_deg_struct;
        try rewrite dub_neg_ptree_ord_struct;
        auto.
        4 : { assert ((loop_ad a (formula_sub_ind_fit d (neg (neg E)) E S2) n d1 d2 alpha1 alpha2 P1 (dub_neg_sub_ptree P2 E (lor_ind (non_target a) S2))) = (dub_neg_sub_ptree (loop_ad a d n d1 d2 alpha1 alpha2 P1 P2) E (lor_ind (0) S2))) as EQ'.
              { unfold dub_neg_sub_ptree, ptree_formula, dub_neg_sub_ptree_fit;
                fold ptree_formula dub_neg_sub_ptree_fit.
                rewrite P2F.
                unfold dub_neg_sub_formula, formula_sub_ind.
                unfold subst_ind_fit;
                fold subst_ind_fit.
                rewrite non_target_sub_fit, FS2.
                reflexivity. }
              rewrite EQ', <- dub_neg_node_eq.
              apply PAX2.
              repeat split; auto. }

        2 : { assert ((loop_ad a (formula_sub_ind_fit d (neg (neg E)) E S2) n d1 d2 alpha1 alpha2 P1 (dub_neg_sub_ptree P2 E (lor_ind (non_target a) S2))) = (dub_neg_sub_ptree (loop_ad a d n d1 d2 alpha1 alpha2 P1 P2) E (lor_ind (0) S2))) as EQ'.
              { unfold dub_neg_sub_ptree, ptree_formula, dub_neg_sub_ptree_fit;
                fold ptree_formula dub_neg_sub_ptree_fit.
                rewrite P2F.
                unfold dub_neg_sub_formula, formula_sub_ind.
                unfold subst_ind_fit;
                fold subst_ind_fit.
                rewrite non_target_sub_fit, FS2.
                reflexivity. }
              rewrite EQ', <- dub_neg_node_eq.
              apply PAX2.
              repeat split; auto. }

        2 : { admit. }
        1 : admit. }
16 : { admit. }
7 : { admit. }

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
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity.

1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply FC.
      reflexivity. }

all : try case form_eqb eqn:EQ;
      try reflexivity;
      try rewrite <- (dub_neg_node_eq _ _ _ P1SV);
      try rewrite <- (dub_neg_node_eq _ _ _ P2SV);
      apply PAX.
Admitted.

(*
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

9,23 : case (form_eqb a E) eqn:EQ.

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

1 : { unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      + apply (incl_tran FC), dub_neg_ptree_node_free, PSV.
      + reflexivity. }

all : case form_eqb;
      try reflexivity.
Qed.

Lemma dub_neg_valid :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E [PSV PAX] S FS.
split.
- apply (dub_neg_struct_valid _ _ PSV _ FS).
- intros A INA.
  apply PAX.
Admitted.*)