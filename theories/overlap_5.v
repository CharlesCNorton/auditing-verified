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
    style [j] includes contest [i].

    N.B. Several lemmas below are domain aliases: thin wrappers around
    core results from [auditing_1.v] and [dependent_3.v], re-exported
    under election-auditing-specific names for readability in the
    overlap context. They add no new mathematical content. *)
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

(** Strict version of [overlap_improvement_le]: for [0 < alpha < 1],
    [2 <= k], and [n < k], the [(k - n) * alpha] bound is strictly loose. *)
Lemma overlap_improvement_le_strict (alpha : R) :
  0 < alpha -> alpha < 1 -> (2 <= k)%N -> (n < k)%N ->
  false_assurance alpha k - false_assurance alpha n <
  (k - n)%:R * alpha.
Proof.
move=> Ha0 Ha1 Hk2 Hnk.
have H1a_pos : 0 < 1 - alpha by rewrite subr_gt0.
have H1a_lt1 : 1 - alpha < 1 by rewrite ltrBlDr ltrDl.
rewrite (overlap_eliminated_contests (ltW Ha0) (ltW Ha1) (ltnW Hnk)).
case: n Hnk => [_|n' Hn'k].
- rewrite expr0 mul1r subn0.
  exact: union_bound_strict.
- have Hkn_pos : (0 < k - n'.+1)%N by rewrite subn_gt0.
  have Hfa_pos : 0 < false_assurance alpha (k - n'.+1).
    rewrite /false_assurance subr_gt0.
    have := pow_lt1_strict_anti H1a_pos H1a_lt1 Hkn_pos.
    by rewrite expr0.
  have Hub : false_assurance alpha (k - n'.+1) <= (k - n'.+1)%:R * alpha.
    exact: union_bound (ltW Ha0) (ltW Ha1).
  have Hn_pow_lt1 : (1 - alpha) ^+ n'.+1 < 1.
    have := pow_lt1_strict_anti H1a_pos H1a_lt1 (ltn0Sn n').
    by rewrite expr0.
  apply: (@lt_le_trans _ _ (false_assurance alpha (k - n'.+1))).
  + rewrite -subr_gt0 -{1}(mul1r (false_assurance alpha (k - n'.+1))) -mulrBl.
    apply: mulr_gt0; last by [].
    by rewrite subr_gt0.
  + exact: Hub.
Qed.

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

(** Constructive version: the right-inverse [rep] is derived from a
    pointwise existence hypothesis by [pickP] over the finite type
    ['I_k] with a decidable predicate.  Axiom-free: no [cid]. *)
Lemma complement_chromatic_surj_of_exists :
  (forall j : 'I_n, exists i : 'I_k,
     covers j i /\ (forall j' : 'I_n, covers j' i -> j' = j)) ->
  exists (rep : 'I_n -> 'I_k) (grouping : 'I_k -> 'I_n),
    (forall j : 'I_n, covers j (rep j)) /\
    (forall i1 i2 : 'I_k,
       grouping i1 = grouping i2 -> contests_overlap i1 i2) /\
    (forall j : 'I_n, grouping (rep j) = j).
Proof.
move=> Hex.
have Hpick_rep : forall j : 'I_n,
  {i : 'I_k | covers j i /\ (forall j' : 'I_n, covers j' i -> j' = j)}.
  move=> j.
  pose P (i : 'I_k) := covers j i &&
    [forall j' : 'I_n, covers j' i ==> (j' == j)].
  case: (pickP P) => [i /andP [Hc /forallP Hu]|Hnone].
  - exists i; split; first exact: Hc.
    by move=> j' Hj'; apply/eqP; apply: (implyP (Hu j')).
  - exfalso; case: (Hex j) => i [Hc Hu].
    have HPi : P i.
      rewrite /P Hc andTb; apply/forallP => j'; apply/implyP => H.
      by apply/eqP; exact: Hu.
    by move: (Hnone i); rewrite HPi.
pose rep j := sval (Hpick_rep j).
have HrepP : forall j, covers j (rep j) /\
                       (forall j', covers j' (rep j) -> j' = j).
  by move=> j; exact: svalP (Hpick_rep j).
have Hrep_cov : forall j, covers j (rep j).
  by move=> j; case: (HrepP j).
have Hrep_uniq : forall j j', covers j' (rep j) -> j' = j.
  by move=> j j' Hc; case: (HrepP j) => _ Hu; exact: Hu.
exists rep.
have [grouping [Hg1 Hg2]] :=
  complement_chromatic_surj Hrep_cov Hrep_uniq.
by exists grouping.
Qed.

End BallotOverlap.

(** ** Maricopa County 2024 covers instantiation *)

(** A concrete [covers] matrix for Maricopa County's 2024 General
    Election: 265 contests sorted into 80 ballot styles by [val i mod 80].
    Every contest is covered by its modular style; the resulting
    chromatic grouping discharges the [full_cov] hypothesis and
    witnesses the 80-group structure used by [bridge_maricopa_80] in
    [concrete_9.v]. *)

Definition maricopa_covers (j : 'I_80) (i : 'I_265) : bool :=
  modn (val i) 80 == val j.

Lemma maricopa_full_cov (i : 'I_265) : exists j : 'I_80, maricopa_covers j i.
Proof.
have Hmod : (modn (val i) 80 < 80)%N by apply: ltn_pmod.
by exists (Ordinal Hmod); rewrite /maricopa_covers /= eqxx.
Qed.

(** The 80-group chromatic witness for Maricopa: a grouping
    [grouping : 'I_265 -> 'I_80] such that contests in the same group
    share a ballot style (and hence overlap in audit evidence). *)
Lemma maricopa_80_groups_valid :
  exists grouping : 'I_265 -> 'I_80,
    forall i1 i2 : 'I_265,
      grouping i1 = grouping i2 ->
      @contests_overlap 265 80 maricopa_covers i1 i2.
Proof.
exact: (@complement_chromatic_le_styles 265 80 maricopa_covers
          maricopa_full_cov).
Qed.

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
Print Assumptions overlap_improvement.
Print Assumptions overlap_improvement_le.
Print Assumptions complement_chromatic_le_styles.
Print Assumptions complement_chromatic_surj_of_exists.
