(******************************************************************************)
(*                                                                            *)
(*     Optimal Risk Allocation (AM-GM) for Risk-Limiting Audits              *)
(*                                                                            *)
(*     The uniform allocation minimizes false assurance for a given total     *)
(*     risk budget. Extracted from auditing_1.v.                                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import sequences exp.

From Auditing Require Import auditing_1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

Section Allocation.

Variable R : realType.

(** Distributing division over a sum: [\sum (f i / c) = (\sum f i) / c]. *)
Lemma sum_divr (n : nat) (f : 'I_n -> R) (c : R) :
  c != 0 -> \sum_(i < n) (f i / c) = (\sum_(i < n) f i) / c.
Proof.
move=> Hc; elim/big_ind2: _ => //.
- by rewrite mul0r.
- by move=> a1 b1 a2 b2 -> ->; rewrite -mulrDl.
Qed.

(** ** Optimal risk allocation (AM-GM)

    The uniform allocation minimizes false assurance for a given total
    risk budget. This is the AM-GM inequality applied to pass
    probabilities: among all vectors [(1 - alpha_i)] with fixed sum,
    the product is maximized when all entries are equal. *)

(** AM-GM inequality: the geometric mean is at most the arithmetic mean (strict positivity). *)
Lemma am_gm (k : nat) (x : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 < x i) ->
  \prod_(i < k) x i <= ((\sum_(i < k) x i) / k%:R) ^+ k.
Proof.
move=> Hk Hpos.
set S := \sum_(i < k) x i.
set M := S / k%:R.
have Hk_pos : (0 : R) < k%:R by rewrite ltr0n.
have Hk_ne0 : k%:R != (0 : R) by rewrite pnatr_eq0 -lt0n.
have HS_pos : 0 < S.
  apply: (lt_le_trans (Hpos (Ordinal Hk))).
  rewrite /S (bigD1 (Ordinal Hk)) // lerDl.
  by apply: sumr_ge0 => i _; exact: ltW.
have HS_ne0 : S != 0 by rewrite gt_eqF.
have HM_pos : 0 < M by rewrite /M divr_gt0.
have HM_ne0 : M != 0 by rewrite gt_eqF.
have HMk_pos : 0 < M ^+ k by exact: exprn_gt0.
(* Quotient product: prod(x_i/M) = (prod x_i) / M^k *)
pose q := fun i : 'I_k => x i / M.
have Hq_pos : forall i, 0 < q i.
  by move=> i; rewrite /q divr_gt0.
have Hfactor : \prod_(i < k) q i = \prod_(i < k) x i / M ^+ k.
  by rewrite /q big_split big_const_ord iter_mulr_1 exprVn.
(* Reduce to prod(q_i) <= 1 *)
suff Hq1 : \prod_(i < k) q i <= 1.
  have H := ler_wpM2r (ltW HMk_pos) Hq1.
  by rewrite mul1r Hfactor divfK ?gt_eqF // in H.
(* Prove prod(q_i) <= 1 via exp bound: q_i <= expR(q_i - 1) *)
have Hprod_pos : 0 < \prod_(i < k) q i by apply: prodr_gt0 => i _.
(* sum(q_i) = k *)
have Hsum_q : \sum_(i < k) q i = k%:R.
  rewrite /q sum_divr ?gt_eqF // -/S.
  have HMk : M * k%:R = S by rewrite /M divfK ?gt_eqF.
  by rewrite -{1}HMk -mulrA mulrCA mulfV ?gt_eqF // mulr1.
(* prod(q_i) <= prod(expR(q_i - 1)) = expR(sum(q_i - 1)) = expR(0) = 1 *)
apply: (le_trans (y := \prod_(i < k) expR (q i - 1))).
  apply: ler_prod => i _; apply/andP; split; first exact: ltW (Hq_pos i).
  by have := expR_ge1Dx (q i - 1); rewrite addrCA subrr addr0.
rewrite -expR_sum.
have -> : \sum_(i < k) (q i - 1) = 0.
  by rewrite sumrB Hsum_q sumr_const card_ord subrr.
by rewrite expR0.
Qed.

(** AM-GM inequality extended to non-negative entries (allows zeros). *)
Lemma am_gm_ge0 (k : nat) (x : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 <= x i) ->
  \prod_(i < k) x i <= ((\sum_(i < k) x i) / k%:R) ^+ k.
Proof.
move=> Hk Hge0.
case: (boolP [forall i, 0 < x i]) => [/forallP Hpos|].
  exact: am_gm Hk Hpos.
rewrite negb_forall => /existsP [j Hj].
have Hxj0 : x j = 0.
  have := Hge0 j; rewrite le_eqVlt (negbTE Hj) orbF => /eqP.
  by move/esym.
have Hprod0 : \prod_(i < k) x i = 0.
  by rewrite (bigD1 j) //= Hxj0 mul0r.
rewrite Hprod0.
by apply: exprn_ge0; apply: divr_ge0; [apply: sumr_ge0 | rewrite ler0n].
Qed.

(** The uniform allocation minimizes false assurance for a given total risk budget. *)
Lemma uniform_allocation_optimal (k : nat) (alphas : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  false_assurance ((\sum_(i < k) alphas i) / k%:R) k <=
    false_assurance_hetero alphas.
Proof.
move=> Hk Ha0 Ha1.
rewrite /false_assurance /false_assurance_hetero lerD2l lerN2.
(* Goal: prod(1 - alpha_i) <= (1 - sum(alpha_i)/k)^k *)
pose y := fun i : 'I_k => 1 - alphas i.
have Hy : forall i, 0 < y i by move=> i; rewrite /y subr_gt0.
have Ham := am_gm Hk Hy.
(* Ham : prod(y_i) <= (sum(y_i)/k)^k *)
(* Connect: sum(1 - alpha_i)/k = 1 - sum(alpha_i)/k *)
suff Heq : (\sum_(i < k) y i) / k%:R = 1 - (\sum_(i < k) alphas i) / k%:R.
  by rewrite -Heq; exact: Ham.
rewrite /y sumrB sumr_const card_ord.
have Hk_ne0 : k%:R != (0 : R) by rewrite pnatr_eq0 -lt0n.
by rewrite mulrBl divff // mul1r.
Qed.

(** Optimal allocation (weakened to non-negative entries): uniform minimizes false assurance. *)
Lemma uniform_allocation_optimal_ge0 (k : nat) (alphas : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 <= alphas i) -> (forall i, alphas i <= 1) ->
  false_assurance ((\sum_(i < k) alphas i) / k%:R) k <=
    false_assurance_hetero alphas.
Proof.
move=> Hk Ha0 Ha1.
rewrite /false_assurance /false_assurance_hetero lerD2l lerN2.
pose y := fun i : 'I_k => 1 - alphas i.
have Hy : forall i, 0 <= y i by move=> i; rewrite /y subr_ge0.
have Ham := am_gm_ge0 Hk Hy.
suff Heq : (\sum_(i < k) y i) / k%:R = 1 - (\sum_(i < k) alphas i) / k%:R.
  by rewrite -Heq; exact: Ham.
rewrite /y sumrB sumr_const card_ord.
have Hk_ne0 : k%:R != (0 : R) by rewrite pnatr_eq0 -lt0n.
by rewrite mulrBl divff // mul1r.
Qed.

(** Strict optimality: any non-uniform split yields strictly higher false assurance. *)
Lemma uniform_allocation_strict (k : nat) (alphas : 'I_k -> R) (j : 'I_k) :
  (0 < k)%N ->
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  alphas j != (\sum_(i < k) alphas i) / k%:R ->
  false_assurance ((\sum_(i < k) alphas i) / k%:R) k <
    false_assurance_hetero alphas.
Proof.
move=> Hk Ha0 Ha1 Hne.
rewrite /false_assurance /false_assurance_hetero ltrD2l ltrN2.
pose y := fun i : 'I_k => 1 - alphas i.
have Hy : forall i, 0 < y i by move=> i; rewrite /y subr_gt0.
set S := \sum_(i < k) y i.
set M := S / k%:R.
have Hk_pos : (0 : R) < k%:R by rewrite ltr0n.
have Hk_ne0 : k%:R != (0 : R) by rewrite pnatr_eq0 -lt0n.
have HS_pos : 0 < S.
  apply: (lt_le_trans (Hy (Ordinal Hk))).
  rewrite /S (bigD1 (Ordinal Hk)) // lerDl.
  by apply: sumr_ge0 => i _; exact: ltW.
have HM_pos : 0 < M by rewrite /M divr_gt0.
have HM_ne0 : M != 0 by rewrite gt_eqF.
(* y j != M *)
have Hyj_ne : y j != M.
  apply/eqP => Heq; move/eqP: Hne; apply.
  have H1 : alphas j = 1 - M by rewrite -Heq /y opprB addrCA subrr addr0.
  rewrite H1 /M /S /y sumrB sumr_const card_ord.
  have Hku : (k%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
  rewrite mulrBl (divff Hku).
  by rewrite opprB addrCA subrr addr0.
(* Key: ln(y_j/M) < y_j/M - 1 since y_j != M *)
pose q := fun i => y i / M.
have Hq_pos : forall i, 0 < q i by move=> i; rewrite /q divr_gt0.
have Hqj_ne1 : q j != 1.
  rewrite /q; apply/eqP => H.
  by move: Hyj_ne; rewrite -(divfK HM_ne0 (y j)) H mul1r eqxx.
have Hsum_q : \sum_(i < k) q i = k%:R.
  rewrite /q sum_divr ?HM_ne0 // -/S.
  have HMk : M * k%:R = S by rewrite /M divfK ?HM_ne0.
  by rewrite -{1}HMk -mulrA mulrCA mulfV ?HM_ne0 // mulr1.
(* Strict: sum ln(q_i) < 0 because one term is strict *)
have Hprod_pos : 0 < \prod_(i < k) q i by apply: prodr_gt0 => i _.
have Hln_strict : \sum_(i < k) ln (q i) < 0.
  rewrite (bigD1 j) //=.
  have Hj_strict : ln (q j) < q j - 1 := ln_lt_sub1 (Hq_pos j) Hqj_ne1.
  have Hrest : \sum_(i < k | i != j) ln (q i) <=
      \sum_(i < k | i != j) (q i - 1).
    by apply: ler_sum => i _; exact: ln_le_sub1 (Hq_pos i).
  apply: (lt_le_trans (ltr_leD Hj_strict Hrest)).
  have Hsum0 : \sum_(i < k) (q i - 1) = 0.
    by rewrite sumrB Hsum_q sumr_const card_ord subrr.
  move: Hsum0; rewrite (bigD1 j) //= => ->.
  exact: lexx.
(* From sum ln < 0: prod q < 1, hence prod y < M^k *)
have Hprod_lt1 : \prod_(i < k) q i < 1.
  have Hppos : (\prod_(i < k) q i) \is Num.pos by rewrite posrE.
  have H1pos : (1 : R) \is Num.pos by rewrite posrE ltr01.
  rewrite -(ltr_ln Hppos H1pos) ln1 (ln_prod (fun i => Hq_pos i)).
  exact: Hln_strict.
(* Factor: prod y = prod q * M^k *)
have Hfactor : \prod_(i < k) q i = \prod_(i < k) y i / M ^+ k.
  by rewrite /q big_split big_const_ord iter_mulr_1 exprVn.
have HMk_pos : 0 < M ^+ k by exact: exprn_gt0.
have Hprod_lt : \prod_(i < k) y i < M ^+ k.
  move: Hprod_lt1; rewrite Hfactor => H.
  by rewrite -(ltr_pM2r HMk_pos) divfK ?mul1r ?expf_neq0 // HM_ne0 in H.
rewrite /M /S /y sumrB sumr_const card_ord in Hprod_lt.
have Hku : (k%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
by rewrite mulrBl (divff (x := k%:R)) ?unitfE // mul1r in Hprod_lt.
Qed.

(** Unique minimizer: if heterogeneous false assurance equals the uniform value,
    every risk limit equals the mean. *)
Lemma uniform_allocation_unique (k : nat) (alphas : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  false_assurance ((\sum_(i < k) alphas i) / k%:R) k =
    false_assurance_hetero alphas ->
  forall i, alphas i = (\sum_(i < k) alphas i) / k%:R.
Proof.
move=> Hk Ha0 Ha1 Heq i.
case: (boolP (alphas i == (\sum_(j < k) alphas j) / k%:R)) => [/eqP // | Hne].
suff : false_assurance ((\sum_(j < k) alphas j) / k%:R) k <
         false_assurance_hetero alphas.
  by rewrite Heq ltxx.
exact: (uniform_allocation_strict Hk Ha0 Ha1 Hne).
Qed.

End Allocation.

(* --- Bibliography ---

   am_gm, am_gm_ge0:
     A.-L. Cauchy, Cours d'analyse de l'École Royale
     Polytechnique.  Première partie: Analyse algébrique,
     L'Imprimerie Royale, Paris, 1821, pp. 457-459 (Note VII).
     Modern annotated translation: R. E. Bradley and
     C. E. Sandifer, Cauchy's Cours d'analyse: An Annotated
     Translation, Springer, 2009.
     DOI: 10.1007/978-1-4419-0549-9
     Standard modern reference: G. H. Hardy, J. E. Littlewood,
     and G. Pólya, Inequalities, 2nd ed., Cambridge University
     Press, 1952, Ch. II.

   uniform_allocation_optimal, uniform_allocation_optimal_ge0,
   uniform_allocation_strict, uniform_allocation_unique:
     Application of AM-GM to optimal risk allocation is implicit
     in the Šidák/Bonferroni literature.  See Z. Šidák,
     "Rectangular confidence regions for the means of multivariate
     normal distributions," J. Amer. Statist. Assoc., 62(318):
     626-633, 1967.  DOI: 10.1080/01621459.1967.10482935
*)

Print Assumptions am_gm.
Print Assumptions uniform_allocation_optimal.
Print Assumptions uniform_allocation_strict.
