(******************************************************************************)
(*                                                                            *)
(*     SHANGRLA: Sets of Half-Average Nulls Generate Risk-Limiting Audits    *)
(*                                                                            *)
(*     Stark 2020.  An "assorter" [A : C -> R] with values in [0, u] has     *)
(*     null-hypothesis mean [u/2]; under the alternative, the mean exceeds   *)
(*     [u/2].  The SHANGRLA test statistic is the cumulative product of      *)
(*     [2 * A(b_i) / u], which is a martingale under the null (E = 1).       *)
(*     Ville's inequality yields the risk bound.                             *)
(*                                                                            *)
(*     This file derives Stark's risk bound as a corollary of                *)
(*     [null_ville_abs] in [bravo_7.v].                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Close Scope N_scope.
Open Scope ring_scope.

From Auditing Require Import auditing_1 probability_4 ville_6 bravo_7.

(** ** SHANGRLA assorter and test statistic *)

Section SHANGRLA.

Variable R : realType.
Variable C : finType.

(** Null distribution: each ballot outcome has positive mass. *)
Variable mu0 : C -> R.
Hypothesis mu0_pos : forall c, 0 < mu0 c.
Hypothesis mu0_sum1 : \sum_(c : C) mu0 c = 1.

(** The assorter upper bound [u] is positive. *)
Variable u : R.
Hypothesis Hu_pos : 0 < u.

(** The assorter: values in [0, u]. *)
Variable assorter : C -> R.
Hypothesis Hassorter_ge0 : forall c, 0 <= assorter c.
Hypothesis Hassorter_le_u : forall c, assorter c <= u.

(** The half-average null: under [mu0], the mean of the assorter
    equals [u/2].  Stark's boundary case where the null mean saturates. *)
Hypothesis Hnull_halfavg : \sum_(c : C) mu0 c * assorter c = u / 2%:R.

(** The SHANGRLA alternative distribution is obtained by re-weighting
    [mu0] with [2 * A / u].  Its mass is non-negative (by
    [Hassorter_ge0]) and sums to 1 (by the half-average null hypothesis). *)
Definition shangrla_mu_alt (c : C) : R := mu0 c * (2%:R * assorter c / u).

Lemma shangrla_mu_alt_ge0 (c : C) : 0 <= shangrla_mu_alt c.
Proof.
rewrite /shangrla_mu_alt; apply: mulr_ge0; first exact: ltW.
apply: divr_ge0; last exact: ltW.
by apply: mulr_ge0; [rewrite ler0n | exact: Hassorter_ge0].
Qed.

(** Equivalent form of the half-average null: [sum mu0 * 2 * A = u]. *)
Lemma shangrla_twice_null : \sum_(c : C) mu0 c * (2%:R * assorter c) = u.
Proof.
have H2_ne0 : (2%:R : R) != 0 by rewrite pnatr_eq0.
have -> : \sum_(c : C) mu0 c * (2%:R * assorter c) =
          2%:R * \sum_(c : C) mu0 c * assorter c.
  by rewrite mulr_sumr; apply: eq_bigr => c _; rewrite mulrCA.
by rewrite Hnull_halfavg mulrC divfK.
Qed.

Lemma shangrla_mu_alt_sum1 : \sum_(c : C) shangrla_mu_alt c = 1.
Proof.
rewrite /shangrla_mu_alt.
have Hu_ne0 : u != 0 by rewrite gt_eqF.
have Heq1 : \sum_(c : C) mu0 c * (2%:R * assorter c / u) =
            (\sum_(c : C) mu0 c * (2%:R * assorter c)) / u.
  rewrite big_distrl /=; apply: eq_bigr => c _; by rewrite mulrA.
rewrite Heq1 shangrla_twice_null.
exact: (divff Hu_ne0).
Qed.

(** The reversed likelihood ratio equals [2 * A / u].  At each ballot,
    this is the [rev_lr] from [bravo_7.v]'s [AbstractNullVille]. *)
Lemma shangrla_rev_lr_val (c : C) :
  @rev_lr R C mu0 shangrla_mu_alt c = 2%:R * assorter c / u.
Proof.
rewrite /rev_lr /shangrla_mu_alt.
have Hmu0_ne0 : mu0 c != 0 by rewrite gt_eqF.
by rewrite -mulrA mulrCA mulfV // mulr1.
Qed.

(** SHANGRLA test supermartingale: the cumulative product
    [prod 2 * A(b_i) / u] under the product null measure is bounded
    by [1/alpha] with probability at most [alpha].  Stark's risk
    bound, derived from [null_ville_abs]. *)
Variable N : nat.
Hypothesis HN : (0 < N)%N.

Theorem shangrla_risk_bound (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R {ffun 'I_N -> C}
      (@null_prod_mu R C mu0 N)
      (fun f => alpha^-1 <= @rev_M R C mu0 shangrla_mu_alt N n f)
  <= alpha.
Proof.
apply: null_ville_abs.
- exact: mu0_pos.
- exact: mu0_sum1.
- exact: shangrla_mu_alt_ge0.
- exact: shangrla_mu_alt_sum1.
Qed.

End SHANGRLA.

Print Assumptions shangrla_risk_bound.
