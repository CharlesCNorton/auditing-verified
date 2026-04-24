(******************************************************************************)
(*                                                                            *)
(*     ALPHA: Audit that Learns from Previously Hand-Audited ballots         *)
(*                                                                            *)
(*     Stark 2023.  ALPHA employs a truncated-shrinkage estimator             *)
(*     [eta_t] bounded by [[0, u]] and constructs a test martingale          *)
(*     whose per-ballot multiplier depends on the shrinkage-based            *)
(*     prediction.  Any non-negative likelihood ratio with null-mean 1      *)
(*     and truncation cap [u] yields the ALPHA test martingale; the risk    *)
(*     bound follows from [gen_M_ville].                                    *)
(*                                                                            *)
(*     This file exposes the ALPHA test supermartingale as an abstract       *)
(*     specialization of the general ballot model, and derives               *)
(*     [alpha_test_ville] as a corollary of [gen_M_ville].                  *)
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

(** ** ALPHA truncated-shrinkage likelihood ratio *)

Section ALPHA.

Variable R : realType.
Variable C : finType.

(** Null distribution on ballots. *)
Variable mu0 : C -> R.
Hypothesis mu0_pos : forall c, 0 < mu0 c.
Hypothesis mu0_sum1 : \sum_(c : C) mu0 c = 1.

(** Truncation cap [u] on the test statistic's per-ballot multiplier. *)
Variable u : R.
Hypothesis Hu_pos : 0 < u.

(** ALPHA per-ballot likelihood ratio: non-negative, truncated at [u],
    with null-mean 1.  Any function satisfying these three properties
    yields a valid ALPHA test martingale.  The truncated-shrinkage
    estimator in Stark 2023 is one concrete such construction. *)
Variable alpha_lr : C -> R.
Hypothesis alpha_lr_ge0 : forall c, 0 <= alpha_lr c.
Hypothesis alpha_lr_truncated : forall c, alpha_lr c <= u.
Hypothesis alpha_lr_exp1 : \sum_(c : C) mu0 c * alpha_lr c = 1.

(** Horizon: number of ballots sampled. *)
Variable N : nat.

(** ALPHA risk bound: the probability that the ALPHA test martingale
    exceeds [1/alpha] is at most [alpha], under the null.  Derived from
    [gen_M_ville] in [bravo_7.v]. *)
Theorem alpha_test_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R {ffun 'I_N -> C}
      (@gen_prod_mu R C mu0 N)
      (fun f => alpha^-1 <= @gen_M R C alpha_lr N n f)
  <= alpha.
Proof.
apply: gen_M_ville.
- exact: mu0_pos.
- exact: mu0_sum1.
- exact: alpha_lr_ge0.
- exact: alpha_lr_exp1.
Qed.

End ALPHA.

Print Assumptions alpha_test_ville.
