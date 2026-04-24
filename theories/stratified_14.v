(******************************************************************************)
(*                                                                            *)
(*     Stratified / batch-level audits                                       *)
(*                                                                            *)
(*     In stratified audits, the ballot population is partitioned into       *)
(*     strata (e.g. precincts, ballot styles), and each stratum is sampled   *)
(*     independently.  The operational MACRO model applies at the stratum   *)
(*     level: a single combined supermartingale across all strata yields    *)
(*     the overall risk bound via Ville's inequality, independent of the    *)
(*     number of strata.                                                     *)
(*                                                                            *)
(*     This file re-exports [macro_operational_bound] and                    *)
(*     [MACRO_bonferroni_bound] from [macro_10.v] under                      *)
(*     stratum-level names, noting that the filtration can represent        *)
(*     batch/stratum observations rather than per-ballot draws.              *)
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

From Auditing Require Import auditing_1 probability_4 ville_6 bravo_7 macro_10.

(** ** Stratified / batch-level MACRO *)

(** The stratified-audit risk bound is [macro_operational_bound]
    applied with a batch-level filtration.  When [F n] represents the
    information available after observing [n] complete strata rather
    than individual ballots, the soundness hypothesis
    [any surviving wrong outcome forces M_n >= 1/alpha] transfers
    directly from the per-ballot setting.  The joint
    false-certification probability is bounded by [alpha], independent
    of the number of strata [k]. *)
Definition stratified_risk_bound := macro_operational_bound.

(** Stratified Bonferroni construction: the arithmetic mean of
    per-stratum likelihood-ratio supermartingales is itself a
    supermartingale with [E[M_0] <= 1], and any per-stratum
    threshold crossing at rate [k/alpha] forces the combined statistic
    above [1/alpha].  This mirrors the per-contest construction in
    [macro_10.v], reinterpreted with strata in place of contests. *)
Definition stratified_bonferroni := MACRO_bonferroni_bound.

Print Assumptions stratified_risk_bound.
Print Assumptions stratified_bonferroni.
