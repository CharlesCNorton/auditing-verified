(******************************************************************************)
(*                                                                            *)
(*     CVR-based comparison audits                                           *)
(*                                                                            *)
(*     In a comparison audit, each sampled ballot is compared against its    *)
(*     cast-vote record (CVR).  The overstatement [omega(b)] is the          *)
(*     difference between reported and actual assorter values.  The CVR     *)
(*     assorter [A_c(b) = 1/2 + (assorter(b) - omega(b)) / (2 * margin)]    *)
(*     gives a null-mean [1/2] assertion equivalent to the original.         *)
(*                                                                            *)
(*     This file models a generic CVR-overstatement ballot as a per-ballot   *)
(*     likelihood ratio and composes it with                                 *)
(*     [degradation_from_per_contest] from [bravo_7.v].                     *)
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

(** ** CVR overstatement model *)

Section Comparison.

Variable R : realType.
Variable C : finType.

(** Null distribution on CVR ballots. *)
Variable mu0 : C -> R.
Hypothesis mu0_pos : forall c, 0 < mu0 c.
Hypothesis mu0_sum1 : \sum_(c : C) mu0 c = 1.

(** The comparison-audit per-ballot likelihood ratio.  In the CVR
    model, this is [(1 - omega/margin) / normalization], where omega
    is the overstatement.  We abstract it as a non-negative function
    with null-mean 1. *)
Variable comp_lr : C -> R.
Hypothesis comp_lr_ge0 : forall c, 0 <= comp_lr c.
Hypothesis comp_lr_exp1 : \sum_(c : C) mu0 c * comp_lr c = 1.

(** Horizon: number of ballots sampled. *)
Variable N : nat.

(** Per-contest risk bound for the comparison audit: Ville's inequality
    on the cumulative product of [comp_lr]. *)
Theorem comparison_test_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R {ffun 'I_N -> C}
      (@gen_prod_mu R C mu0 N)
      (fun f => alpha^-1 <= @gen_M R C comp_lr N n f)
  <= alpha.
Proof.
apply: gen_M_ville.
- exact: mu0_pos.
- exact: mu0_sum1.
- exact: comp_lr_ge0.
- exact: comp_lr_exp1.
Qed.

End Comparison.

(** ** End-to-end degradation for multiple comparison contests *)

(** Composing the per-contest comparison risk bound with the
    multiplicative degradation theory: for [k] comparison audits each
    at per-contest risk [alphas i], the joint false assurance is at
    most [1 - prod (1 - alphas i)]. *)
Theorem comparison_degradation (R : realType) (k : nat)
    (alphas : 'I_k -> R) (pass_probs : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  (forall i, 0 <= pass_probs i <= 1 - alphas i) ->
  @false_assurance_hetero R k alphas <= 1 - @joint_pass R k pass_probs.
Proof. exact: degradation_from_per_contest. Qed.

Print Assumptions comparison_test_ville.
Print Assumptions comparison_degradation.
