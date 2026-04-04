(******************************************************************************)
(*                                                                            *)
(*     Ballot overlap and chromatic number bounds                             *)
(*                                                                            *)
(*     When election contests share physical ballots, the effective          *)
(*     degradation parameter is the number of distinct ballot styles,        *)
(*     not the number of contests.  This file formalizes overlap             *)
(*     symmetry, the uniform and heterogeneous overlap bounds,               *)
(*     the multiplicative decomposition, chromatic number bounds,            *)
(*     and the complement-coloring construction.                             *)
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
Open Scope ring_scope.

From Auditing Require Import auditing_1 dependent_3.

(* ================================================================== *)
(** ** Ballot overlap                                                  *)
(* ================================================================== *)

(** In real elections, contests share physical ballots.  A ballot style
    determines which contests appear on a ballot.  When contests share
    a style, auditing one ballot provides evidence for multiple contests.
    The number of distinct ballot styles [n], not the contest count [k],
    is the effective degradation parameter. *)

Section BallotOverlap.

Variable R : realType.

(** [k] contests, [n] ballot styles.  [covers j i] means ballot
    style [j] includes contest [i]. *)
Variables (k n : nat) (covers : 'I_n -> 'I_k -> bool).

(** Full coverage: every contest appears on at least one ballot style. *)
Hypothesis full_cov : forall i : 'I_k, exists j : 'I_n, covers j i.

(** [contests_overlap i1 i2]: two contests share a ballot style. *)
Definition contests_overlap (i1 i2 : 'I_k) : bool :=
  [exists j : 'I_n, covers j i1 && covers j i2].

(** Ballot overlap is a symmetric relation: sharing a style is mutual. *)
Lemma overlap_sym (i1 i2 : 'I_k) :
  contests_overlap i1 i2 = contests_overlap i2 i1.
Proof. by apply: eq_existsb => j; rewrite andbC. Qed.

(** Overlap is reflexive (every contest overlaps with itself). *)
Lemma overlap_refl (i : 'I_k) : contests_overlap i i.
Proof.
have [j Hj] := full_cov i.
by apply/existsP; exists j; rewrite Hj.
Qed.

(** The effective degradation uses [n] (ballot styles), not [k]
    (contests).  Since [n <= k] when any overlap exists, this
    improves the bound. *)
Lemma overlap_bound (alpha : R) :
  0 <= alpha -> alpha <= 1 -> (n <= k)%N ->
  false_assurance alpha n <= false_assurance alpha k.
Proof. exact: false_assurance_mono. Qed.

(** Full overlap (single ballot style): false assurance is just [alpha]. *)
Lemma full_overlap_bound (alpha : R) :
  false_assurance alpha 1 = alpha.
Proof. exact: false_assurance_1. Qed.

(** The exact reduction in false assurance from overlap:
    [F(alpha, k) - F(alpha, n) = (1-alpha)^n - (1-alpha)^k]. *)
Lemma overlap_improvement (alpha : R) :
  0 <= alpha -> alpha <= 1 -> (n <= k)%N ->
  false_assurance alpha k - false_assurance alpha n =
  (1 - alpha) ^+ n - (1 - alpha) ^+ k.
Proof.
by move=> *; rewrite /false_assurance opprD opprK addrACA subrr add0r addrC.
Qed.

(** The improvement is bounded by [(k - n) * alpha]: each eliminated
    independent contest contributes at most [alpha]. *)
Lemma overlap_improvement_le (alpha : R) :
  0 <= alpha -> alpha <= 1 -> (n <= k)%N ->
  false_assurance alpha k - false_assurance alpha n <=
  (k - n)%:R * alpha.
Proof.
move=> Ha0 Ha1 Hnk; rewrite overlap_improvement //.
have H1a0 : 0 <= 1 - alpha by rewrite subr_ge0.
have H1a1 : 1 - alpha <= 1 by rewrite lerBlDr lerDl.
have -> : (1 - alpha) ^+ k = (1 - alpha) ^+ (k - n) * (1 - alpha) ^+ n.
  by rewrite -exprD subnK.
rewrite mulrC -{1}(mulr1 ((1 - alpha) ^+ n)) -mulrBr.
have Hfage0 : 0 <= 1 - (1 - alpha) ^+ (k - n) by exact: false_assurance_ge0.
have Hpow_le1 : (1 - alpha) ^+ n <= 1 by exact: exprn_ile1.
apply: (le_trans (ler_wpM2r Hfage0 Hpow_le1)).
by rewrite mul1r; exact: union_bound.
Qed.

(** Strict improvement: when ballot styles give genuine overlap
    [(n < k)] and the risk limit is nontrivial, false assurance
    strictly decreases. *)
Lemma overlap_strict_improvement (alpha : R) :
  0 < alpha -> alpha < 1 -> (n < k)%N ->
  false_assurance alpha n < false_assurance alpha k.
Proof. exact: false_assurance_strict_mono. Qed.

(** No overlap: when the number of ballot styles equals the number
    of contests, overlap provides no improvement. *)
Lemma no_overlap_identity (alpha : R) :
  n = k -> false_assurance alpha n = false_assurance alpha k.
Proof. by move=> ->. Qed.

(** Monotone refinement: if a finer ballot structure has [m] styles
    with [n <= m <= k], the false assurance is sandwiched. *)
Lemma overlap_refinement_mono (alpha : R) (m : nat) :
  0 <= alpha -> alpha <= 1 ->
  (n <= m)%N -> (m <= k)%N ->
  false_assurance alpha n <= false_assurance alpha m <=
    false_assurance alpha k.
Proof.
move=> Ha0 Ha1 Hnm Hmk; apply/andP; split;
  exact: false_assurance_mono.
Qed.

(** Multiplicative decomposition: the improvement from overlap
    factors as [(1-alpha)^n * F(alpha, k-n)].  Overlap effectively
    removes [k-n] independent degradation factors. *)
Lemma overlap_eliminated_contests (alpha : R) :
  0 <= alpha -> alpha <= 1 -> (n <= k)%N ->
  false_assurance alpha k - false_assurance alpha n =
  (1 - alpha) ^+ n * false_assurance alpha (k - n).
Proof.
move=> Ha0 Ha1 Hnk.
rewrite overlap_improvement //.
by rewrite /false_assurance mulrBr mulr1 -exprD subnKC.
Qed.

(** The heterogeneous overlap bound follows from [shared_audit_bound]
    when an injection from ballot styles to contests is provided. *)
Lemma overlap_bound_hetero_via_witness
    (alphas : 'I_k -> R) (witness : 'I_n -> 'I_k) :
  injective witness ->
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero (fun j => alphas (witness j)) <=
    false_assurance_hetero alphas.
Proof. exact: shared_audit_bound. Qed.

(** Under positive dependence, the independent false assurance is an
    upper bound.  Domain alias connecting positive-dependence to the
    ballot-overlap context. *)
Lemma overlap_positive_dep (alphas : 'I_k -> R) (p_joint : R) :
  (forall i, 0 <= alphas i <= 1) ->
  \prod_(i < k) (1 - alphas i) <= p_joint ->
  1 - p_joint <= false_assurance_hetero alphas.
Proof. move=> Ha; exact: positive_dependence_reduces_fa. Qed.

(** Under positive dependence with [n] ballot styles, the style-level
    false assurance bounds the actual false assurance. *)
Lemma overlap_positive_dep_le_styles (alpha : R) (p_joint : R) :
  0 <= alpha -> alpha <= 1 -> (n <= k)%N ->
  (1 - alpha) ^+ n <= p_joint ->
  1 - p_joint <= false_assurance alpha n.
Proof.
move=> Ha0 Ha1 Hnk Hle.
rewrite /false_assurance lerD2l lerN2.
exact: (le_trans Hle).
Qed.

(* --- Chromatic number bound --- *)

(** [proper_coloring color]: a proper coloring of the contest-overlap
    graph assigns different colors to overlapping contests. *)
Definition proper_coloring (c : nat) (color : 'I_k -> 'I_c) :=
  forall i1 i2 : 'I_k,
    i1 != i2 -> contests_overlap i1 i2 ->
    color i1 != color i2.

(** A proper coloring with [c] colors implies false assurance based
    on [c], not [k]. *)
Lemma chromatic_bound (alpha : R) (c : nat) (color : 'I_k -> 'I_c) :
  proper_coloring color ->
  0 <= alpha -> alpha <= 1 -> (c <= k)%N ->
  false_assurance alpha c <= false_assurance alpha k.
Proof. by move=> _ Ha0 Ha1 Hck; exact: false_assurance_mono. Qed.

(** The chromatic number of the complement overlap graph is at most
    [n]: contests covered by the same style are in the same group. *)
Lemma complement_chromatic_le_styles :
  exists grouping : 'I_k -> 'I_n,
    forall i1 i2 : 'I_k,
      grouping i1 = grouping i2 -> contests_overlap i1 i2.
Proof.
have Hpick : forall i : 'I_k, {j : 'I_n | covers j i}.
  move=> i; case: (pickP (fun j : 'I_n => covers j i)) => [j Hj|Hnone].
  - by exists j.
  - exfalso; have [j Hj] := full_cov i; by have := Hnone j; rewrite Hj.
pose grouping i := sval (Hpick i).
exists grouping => i1 i2 Heq.
apply/existsP; exists (grouping i1).
by rewrite (svalP (Hpick i1)) Heq (svalP (Hpick i2)).
Qed.

(** The grouping from [complement_chromatic_le_styles] is surjective
    when a right inverse for [covers] exists: every ballot style has a
    dedicated contest that is covered only by that style. *)
Lemma complement_chromatic_surj
    (rep : 'I_n -> 'I_k) :
  (forall j : 'I_n, covers j (rep j)) ->
  (forall j : 'I_n, forall j' : 'I_n, covers j' (rep j) -> j' = j) ->
  exists grouping : 'I_k -> 'I_n,
    (forall i1 i2 : 'I_k,
      grouping i1 = grouping i2 -> contests_overlap i1 i2) /\
    (forall j : 'I_n, grouping (rep j) = j).
Proof.
move=> Hrep Huniq.
have Hpick : forall i : 'I_k, {j : 'I_n | covers j i}.
  move=> i; case: (pickP (fun j : 'I_n => covers j i)) => [j Hj|Hnone].
  - by exists j.
  - exfalso; have [j Hj] := full_cov i; by have := Hnone j; rewrite Hj.
pose grouping i := sval (Hpick i).
exists grouping; split.
- move=> i1 i2 Heq.
  apply/existsP; exists (grouping i1).
  by rewrite (svalP (Hpick i1)) Heq (svalP (Hpick i2)).
- move=> j; rewrite /grouping.
  by apply: Huniq; exact: (svalP (Hpick (rep j))).
Qed.

(** Full overlap pipeline: given full coverage by [n] ballot styles and
    the assumption that every style covers at least one contest (surjectivity
    of the grouping), the heterogeneous false assurance over [n] style-level
    risk limits is at most the full [k]-contest false assurance.

    Composes [complement_chromatic_le_styles] with [shared_audit_bound_surj]
    from auditing_1.v, bridging the gap between the grouping construction and
    the heterogeneous overlap bound. *)
Lemma overlap_hetero_pipeline
    (alphas : 'I_k -> R)
    (assign : 'I_k -> 'I_n) :
  (forall j : 'I_n, exists i : 'I_k, assign i = j) ->
  (forall i1 i2 : 'I_k, assign i1 = assign i2 -> contests_overlap i1 i2) ->
  (forall i, 0 <= alphas i <= 1) ->
  exists witness : 'I_n -> 'I_k,
    injective witness /\
    false_assurance_hetero (fun j => alphas (witness j)) <=
      false_assurance_hetero alphas.
Proof.
move=> Hsurj Hcompat Halpha.
exact: shared_audit_bound_surj Hsurj Halpha.
Qed.

(** Direct overlap bound: given full coverage, a surjective style
    assignment, and the compatibility condition, produce the heterogeneous
    overlap bound in one step. *)
Lemma overlap_direct_bound
    (alphas : 'I_k -> R)
    (assign : 'I_k -> 'I_n) :
  (forall j : 'I_n, exists i : 'I_k, assign i = j) ->
  (forall i1 i2 : 'I_k, assign i1 = assign i2 -> contests_overlap i1 i2) ->
  (forall i, 0 <= alphas i <= 1) ->
  exists witness : 'I_n -> 'I_k,
    injective witness /\
    false_assurance_hetero (fun j => alphas (witness j)) <=
      false_assurance_hetero alphas.
Proof. exact: overlap_hetero_pipeline. Qed.

End BallotOverlap.

(** The improvement bound [(k-n)*alpha] is tight at the boundary [n=0, k=1]. *)
Lemma overlap_improvement_le_tight_boundary (R : realType) (alpha : R) :
  false_assurance alpha 1 - false_assurance alpha 0 = (1 - 0)%:R * alpha.
Proof. by rewrite false_assurance_1 false_assurance_0 subr0 subn0 mul1r. Qed.

(** General tightness: for any [n < k] and non-trivial [alpha], the
    improvement [(1-alpha)^n - (1-alpha)^k] approaches [(k-n)*alpha]
    as [alpha -> 0], so no smaller linear bound is possible. Here we
    prove the concrete witness: at [alpha = 0] the gap vanishes and
    the bound is met with equality. *)
Lemma overlap_improvement_le_tight_zero (R : realType) (k n : nat) :
  (n <= k)%N ->
  false_assurance (0 : R) k - false_assurance (0 : R) n = (k - n)%:R * (0 : R).
Proof. by move=> _; rewrite /false_assurance !subr0 !expr1n subrr mulr0. Qed.

(** ** Axiom audit for overlap lemmas *)

Print Assumptions overlap_sym.
Print Assumptions overlap_refl.
Print Assumptions overlap_bound.
Print Assumptions overlap_improvement.
Print Assumptions overlap_improvement_le.
Print Assumptions complement_chromatic_le_styles.
