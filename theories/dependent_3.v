(******************************************************************************)
(*                                                                            *)
(*     Dependent Audit Model for Risk-Limiting Audits                        *)
(*                                                                            *)
(*     Dependence analysis, Frechet bounds, and quantitative dependence      *)
(*     theory for joint audit pass probabilities. Extracted from             *)
(*     auditing_1.v.                                                            *)
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

Section Dependent.

Variable R : realType.

(** ** Dependent audit model *)
(* ---
   The independent model assumes joint_pass = prod p_i. Under arbitrary
   dependence, the joint pass probability p_joint satisfies only the
   marginal constraints: p_joint <= 1 - alpha_i for each contest i.

   N.B. Some lemmas (e.g. [macro_fa_le_hetero], [overlap_bound])
   are domain aliases: thin wrappers around core [auditing_1.v]
   results, re-exported under election-auditing names for
   readability.  They add no new mathematical content.
   No product structure is assumed.

   The union bound (F <= sum alpha_i) does NOT follow from marginals
   alone — it requires subadditivity of the probability measure, which
   is external to this algebraic formalization. What IS provable from
   the marginals: each contest's risk is a lower bound on F, and the
   independent product lies between the Frechet bounds. *)

(** Per-contest lower bound: any joint model gives [F >= alpha_j]. *)
Lemma dependent_fa_ge_alpha (alpha p_joint : R) :
  p_joint <= 1 - alpha -> alpha <= 1 - p_joint.
Proof. by rewrite lerBrDl addrC -lerBrDl. Qed.

(** The independent product satisfies all marginal constraints: [prod(1-alpha_i) <= 1-alpha_j]. *)
Lemma independent_satisfies_marginals (k : nat) (alphas : 'I_k -> R)
    (j : 'I_k) :
  (forall i, 0 <= alphas i <= 1) ->
  \prod_(i < k) (1 - alphas i) <= 1 - alphas j.
Proof.
move=> Ha; rewrite (bigD1 j) //=.
have Hge0 : 0 <= 1 - alphas j by move: (Ha j) => /andP [_ H]; rewrite subr_ge0.
have Hle1 : \prod_(i < k | i != j) (1 - alphas i) <= 1.
  elim/big_rec: _ => [|i x _ Hx]; first exact: lexx.
  move: (Ha i) => /andP [H0i H1i].
  apply: (le_trans (ler_wpM2l _ Hx)); first by rewrite subr_ge0.
  by rewrite mulr1 lerBlDr lerDl.
rewrite -[X in _ <= X]mulr1.
by apply: ler_wpM2l.
Qed.

(** Independence worsens assurance: [alpha_j <= F_hetero] for every contest [j]. *)
Lemma independence_worsens_assurance (k : nat)
    (alphas : 'I_k -> R) (j : 'I_k) :
  (forall i, 0 <= alphas i <= 1) ->
  alphas j <= false_assurance_hetero alphas.
Proof.
move=> Ha.
by apply: dependent_fa_ge_alpha; exact: independent_satisfies_marginals.
Qed.

(** Frechet upper bound: the independent product is at most [1 - alpha_j] for each [j]. *)
Lemma frechet_upper_bound (k : nat) (alphas : 'I_k -> R)
    (j : 'I_k) :
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero alphas <= 1 - \prod_(i < k) (1 - alphas i).
Proof. by []. Qed.

(** Weierstrass product inequality: [prod(1-alpha_i) >= 1 - sum(alpha_i)]. *)
Lemma weierstrass_product (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  1 - \sum_(i < k) alphas i <= \prod_(i < k) (1 - alphas i).
Proof.
move=> Ha; have H := false_assurance_hetero_union_bound Ha.
rewrite /false_assurance_hetero lerBlDr in H.
by rewrite lerBlDr addrC.
Qed.

(** The independent product [prod(1-alpha_i)] lies in [0,1] when all risk limits are in [0,1]. *)
Lemma independent_product_in_01 (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  0 <= \prod_(i < k) (1 - alphas i) <= 1.
Proof.
move=> Ha; apply/andP; split.
- by apply: prodr_ge0 => i _; move: (Ha i) => /andP [H0 H1]; rewrite subr_ge0.
- elim/big_rec: _ => [//|i x _ Hx].
  move: (Ha i) => /andP [H0 H1].
  apply: (le_trans (ler_wpM2l _ Hx)); first by rewrite subr_ge0.
  by rewrite mulr1 lerBlDr lerDl.
Qed.

(** The independent product is sandwiched between Frechet bounds:
    [1 - sum(alpha_i) <= prod(1-alpha_i) <= 1 - alpha_j]. *)
Lemma independent_between_frechet (k : nat)
    (alphas : 'I_k -> R) (j : 'I_k) :
  (forall i, 0 <= alphas i <= 1) ->
  1 - \sum_(i < k) alphas i <= \prod_(i < k) (1 - alphas i)
    <= 1 - alphas j.
Proof.
move=> Ha; apply/andP; split.
- exact: weierstrass_product.
- exact: independent_satisfies_marginals.
Qed.

(** Frechet lower bound: [prod(1-alpha_i) >= max(0, 1 - sum alpha_i)]. *)
Lemma frechet_lower_bound (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  Num.max 0 (1 - \sum_(i < k) alphas i) <= \prod_(i < k) (1 - alphas i).
Proof.
move=> Ha; rewrite maxEle; case: ifP => _.
- exact: weierstrass_product.
- by apply: prodr_ge0 => i _; move: (Ha i) => /andP [H0 H1]; rewrite subr_ge0.
Qed.

(** Full Frechet sandwich: [max(0, 1-sum alpha_i) <= prod(1-alpha_i) <= 1-alpha_j]. *)
Lemma frechet_sandwich (k : nat)
    (alphas : 'I_k -> R) (j : 'I_k) :
  (forall i, 0 <= alphas i <= 1) ->
  Num.max 0 (1 - \sum_(i < k) alphas i) <= \prod_(i < k) (1 - alphas i)
    <= 1 - alphas j.
Proof.
move=> Ha; apply/andP; split.
- exact: frechet_lower_bound.
- exact: independent_satisfies_marginals.
Qed.

(** Positive dependence reduces false assurance: [p_joint >= prod(1-alpha_i)]
    implies [1-p_joint <= F_hetero]. *)
Lemma positive_dependence_reduces_fa (k : nat)
    (alphas : 'I_k -> R) (p_joint : R) :
  \prod_(i < k) (1 - alphas i) <= p_joint ->
  1 - p_joint <= false_assurance_hetero alphas.
Proof. by rewrite /false_assurance_hetero lerD2l lerN2. Qed.

(** Negative dependence worsens false assurance: [p_joint <= prod(1-alpha_i)]
    implies [F_hetero <= 1-p_joint]. *)
Lemma negative_dependence_worsens_fa (k : nat)
    (alphas : 'I_k -> R) (p_joint : R) :
  p_joint <= \prod_(i < k) (1 - alphas i) ->
  false_assurance_hetero alphas <= 1 - p_joint.
Proof. by rewrite /false_assurance_hetero lerD2l lerN2. Qed.

(* --- Quantitative dependence theory ---

   The independent model gives false_assurance_hetero alphas =
   1 - prod(1 - alpha_i). Under arbitrary dependence, the joint
   pass probability p_joint is a free parameter satisfying the
   marginal constraints p_joint <= 1 - alpha_j and 0 <= p_joint.
   The dependent false assurance is 1 - p_joint.

   This section derives quantitative consequences by transferring
   the independent-model bounds through the dependence comparison
   lemmas. Under negative dependence (p_joint <= prod), every
   LOWER bound on independent FA transfers to the dependent FA.
   Under positive dependence (p_joint >= prod), every UPPER bound
   transfers. The full exponential sandwich, threshold crossing,
   union bound, and allocation optimality extend to the dependent
   setting without additional measure-theoretic machinery. *)

(** Dependence gap identity: [(1-p_joint) - F_hetero = prod(1-alpha_i) - p_joint]. *)
Lemma dependence_gap (k : nat) (alphas : 'I_k -> R) (p_joint : R) :
  (1 - p_joint) - false_assurance_hetero alphas =
  \prod_(i < k) (1 - alphas i) - p_joint.
Proof.
by rewrite /false_assurance_hetero opprD opprK addrACA subrr add0r addrC.
Qed.

(** Under negative dependence: [1 - exp(-sum alpha_i) <= 1 - p_joint]. *)
Lemma negative_dep_exp_bound (k : nat)
    (alphas : 'I_k -> R) (p_joint : R) :
  (forall i, 0 <= alphas i <= 1) ->
  p_joint <= \prod_(i < k) (1 - alphas i) ->
  1 - expR (- \sum_(i < k) alphas i) <= 1 - p_joint.
Proof.
move=> Ha Hle.
exact: le_trans (false_assurance_hetero_ge_exp Ha)
               (negative_dependence_worsens_fa Hle).
Qed.

(** Threshold crossing under negative dependence: sufficiently many contests push
    dependent false assurance above any target [delta]. *)
Lemma negative_dep_threshold (epsilon delta : R) :
  0 < epsilon -> epsilon < 1 -> 0 < delta -> delta < 1 ->
  exists k0 : nat, forall k (alphas : 'I_k -> R) (p_joint : R),
    (k0 <= k)%N ->
    (forall i, epsilon <= alphas i <= 1) ->
    p_joint <= \prod_(i < k) (1 - alphas i) ->
    delta <= 1 - p_joint.
Proof.
move=> He0 He1 Hd0 Hd1.
have [k0 Hk0] := false_assurance_hetero_threshold He0 He1 Hd0 Hd1.
exists k0 => k alphas p_joint Hle Ha Hdep.
exact: le_trans (Hk0 k alphas Hle Ha)
               (negative_dependence_worsens_fa Hdep).
Qed.

(** Under positive dependence: [1-p_joint <= 1 - exp(-sum(alpha_i/(1-alpha_i)))]. *)
Lemma positive_dep_exp_bound (k : nat)
    (alphas : 'I_k -> R) (p_joint : R) :
  (forall i, 0 < alphas i) ->
  (forall i, alphas i < 1) ->
  \prod_(i < k) (1 - alphas i) <= p_joint ->
  1 - p_joint <=
    1 - expR (- \sum_(i < k) (alphas i / (1 - alphas i))).
Proof.
move=> Ha0 Ha1 Hle.
exact: le_trans (positive_dependence_reduces_fa Hle)
               (false_assurance_hetero_le_exp Ha0 Ha1).
Qed.

(** Union bound under positive dependence: [1-p_joint <= sum alpha_i]. *)
Lemma positive_dep_union_bound (k : nat)
    (alphas : 'I_k -> R) (p_joint : R) :
  (forall i, 0 <= alphas i <= 1) ->
  \prod_(i < k) (1 - alphas i) <= p_joint ->
  1 - p_joint <= \sum_(i < k) alphas i.
Proof.
move=> Ha Hle.
exact: le_trans (positive_dependence_reduces_fa Hle)
               (false_assurance_hetero_union_bound Ha).
Qed.

(** Negative dependence gap bound: the excess over [F_hetero] is at most [prod(1-alpha_i)]. *)
Lemma negative_dep_gap_bound (k : nat)
    (alphas : 'I_k -> R) (p_joint : R) :
  0 <= p_joint ->
  p_joint <= \prod_(i < k) (1 - alphas i) ->
  (1 - p_joint) - false_assurance_hetero alphas <=
    \prod_(i < k) (1 - alphas i).
Proof.
by move=> Hp0 _; rewrite dependence_gap lerBlDr lerDl.
Qed.

(** Algebraic achievability: setting [p_joint = 1-t] satisfies all marginals and gives [F_dep = t]. *)
Lemma dep_fa_achievable (k : nat) (alphas : 'I_k -> R) (t : R) :
  (forall j : 'I_k, alphas j <= t) -> t <= 1 ->
  let p := 1 - t in
  (forall j, p <= 1 - alphas j) /\ 0 <= p /\ 1 - p = t.
Proof.
move=> Hle Ht1 /=; repeat split.
- by move=> j; rewrite lerD2l lerN2; exact: Hle.
- by r01.
- by rewrite opprB addrCA subrr addr0.
Qed.

(* --- Measure-theoretic achievability ---
   The algebraic compatibility in dep_fa_achievable lifts to a
   finite discrete probability measure on {pass, fail}^k. The
   two-point distribution concentrates mass 1-t on the all-pass
   outcome and mass t on the all-fail outcome — the Frechet-
   Hoeffding extremal under maximal positive correlation. *)

(** Measure-theoretic achievability: a two-point distribution witnesses any target [t >= max alpha_j]. *)
Lemma dep_fa_achievable_measure (k : nat) (alphas : 'I_k -> R) (t : R) :
  (forall j : 'I_k, alphas j <= t) -> 0 <= t -> t <= 1 ->
  exists (p_pass p_fail : R),
    (* Non-negative weights summing to 1 *)
    0 <= p_pass /\ 0 <= p_fail /\ p_pass + p_fail = 1 /\
    (* Joint pass probability *)
    p_pass = 1 - t /\
    (* Marginal bounds: each contest's pass probability <= 1 - alpha_j.
       Under the two-point distribution, P(contest j passes) = p_pass
       since contests pass or fail together. *)
    (forall j, p_pass <= 1 - alphas j).
Proof.
move=> Hle Ht0 Ht1; exists (1 - t), t; repeat split.
- by r01.
- exact: Ht0.
- by rewrite subrK.
- by move=> j; rewrite lerD2l lerN2; exact: Hle.
Qed.

(** Concrete dependent sampling bridge: the two-point distribution from
    [probability_4.v] realizes any dependent false assurance level [t]
    above the maximum risk limit. The joint pass probability equals [1-t]
    and each marginal is bounded by [1 - alpha_j]. *)
Lemma dep_concrete_bridge (k : nat) (alphas : 'I_k -> R) (t : R) :
  (0 < k)%N ->
  (forall j : 'I_k, alphas j <= t) -> 0 <= t -> t <= 1 ->
  exists (p_joint : R),
    (forall j, p_joint <= 1 - alphas j) /\
    0 <= p_joint /\
    1 - p_joint = t /\
    (forall j, alphas j <= 1 - p_joint).
Proof.
move=> Hk Hle Ht0 Ht1.
exists (1 - t); repeat split.
- by move=> j; rewrite lerD2l lerN2.
- by r01.
- by rewrite opprB addrCA subrr addr0.
- by move=> j; rewrite opprB addrCA subrr addr0.
Qed.

(** ** MACRO audit model *)

(** MACRO eliminates multiplicity: the no-escalation probability is at most [F_hetero]. *)
Lemma macro_no_multiplicity (k : nat) (alphas : 'I_k -> R)
    (p : R) :
  (0 < k)%N ->
  (forall i : 'I_k, p <= alphas i) ->
  (forall i, 0 <= alphas i <= 1) ->
  p <= false_assurance_hetero alphas.
Proof.
move=> Hk Hp Ha.
apply: (le_trans (Hp (Ordinal Hk))).
exact: (independence_worsens_assurance (Ordinal Hk) Ha).
Qed.

(** Uniform MACRO: false assurance is at most [alpha] regardless of [k]. *)
Lemma macro_uniform (alpha p : R) (k : nat) :
  0 <= alpha -> alpha <= 1 -> (0 < k)%N ->
  p <= alpha ->
  p <= false_assurance alpha k.
Proof.
move=> Ha0 Ha1 Hk Hp.
have H1 : alpha = false_assurance alpha 1 by rewrite false_assurance_1.
rewrite H1 in Hp.
exact: (le_trans Hp (false_assurance_mono Ha0 Ha1 Hk)).
Qed.

(** MACRO false assurance is at most the independent heterogeneous false assurance.
    Under all-or-nothing escalation, the no-escalation probability for any
    single contest [j] is at most [F_hetero]. *)
Lemma macro_fa_le_hetero (k : nat) (alphas : 'I_k -> R) (j : 'I_k) :
  (forall i, 0 <= alphas i <= 1) ->
  alphas j <= false_assurance_hetero alphas.
Proof. exact: independence_worsens_assurance. Qed.

(** Strict MACRO bound: if the minimum risk limit is not the only value, MACRO gives strictly less. *)
Lemma macro_fa_strict_le_hetero (k : nat)
    (alphas : 'I_k -> R) (j j' : 'I_k) :
  (forall i, 0 <= alphas i) ->
  (forall i, alphas i < 1) ->
  (forall i, alphas j <= alphas i) ->
  alphas j < alphas j' ->
  alphas j < false_assurance_hetero alphas.
Proof.
move=> Ha0 Ha1 Hmin Hlt.
have Ha01 : forall i, 0 <= alphas i <= 1
  by move=> i; apply/andP; split; [exact: Ha0 | exact: ltW].
exact: lt_le_trans Hlt (independence_worsens_assurance j' Ha01).
Qed.

(** ** Negative dependence tightness witness *)

(** The Fréchet lower bound is strictly below the independence product
    when [k >= 2] and all risk limits are in (0,1).  The witness
    [p_joint = 0] satisfies 0 >= 0 (Fréchet lower bound) and
    [0 < prod(1-alpha_i)] (strict gap from independence).  This
    demonstrates that negative dependence is achievable and that the
    independence assumption cannot be dropped. *)
Lemma negative_dep_witness (k : nat) (alphas : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  0 < \prod_(i < k) (1 - alphas i).
Proof.
move=> Hk Ha0 Ha1.
by apply: prodr_gt0 => i _; rewrite subr_gt0.
Qed.

(** The strict Weierstrass inequality for two factors:
    [(1-a)(1-b) > 1 - a - b] when [a, b > 0] and [a, b < 1]. *)
Lemma weierstrass_strict_2 (a b : R) :
  0 < a -> a < 1 -> 0 < b -> b < 1 ->
  1 - (a + b) < (1 - a) * (1 - b).
Proof.
move=> Ha0 Ha1 Hb0 Hb1.
have H1a : 0 < 1 - a by rewrite subr_gt0.
have Hb1a : b * (1 - a) < b * 1.
  by rewrite ltr_pM2l // ltrBlDr ltrDl.
rewrite mulr1 in Hb1a.
(* (1-a)(1-b) = (1-a) - b(1-a) *)
have Hexp : (1 - a) * (1 - b) = (1 - a) - b * (1 - a).
  by rewrite mulrBr mulr1 mulrC.
rewrite Hexp.
(* Rewrite LHS: 1 - (a + b) = (1 - a) - b *)
have -> : 1 - (a + b) = (1 - a) - b by rewrite opprD addrA.
(* Goal: (1 - a) - b < (1 - a) - b * (1 - a) *)
by rewrite ltrD2l ltrN2.
Qed.

(** p_joint = 0 witnesses negative dependence for any [k >= 2]:
    the independence product is strictly above 0, so setting
    p_joint = 0 makes [F_dep = 1] strictly above [F_indep]. *)
Lemma negative_dep_achievable (k : nat) (alphas : 'I_k -> R) :
  (0 < k)%N ->
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  false_assurance_hetero alphas < 1 - (0 : R).
Proof.
move=> Hk Ha0 Ha1; rewrite subr0 /false_assurance_hetero.
rewrite ltrBlDr ltrDl.
by apply: prodr_gt0 => i _; rewrite subr_gt0.
Qed.

End Dependent.

(** The strict Weierstrass product inequality for general [k >= 2]:
    [1 - sum alpha_i < prod(1 - alpha_i)] when all [alpha_i] are in (0,1).
    Proved outside the section to avoid dependent-type issues with
    [big_ord_recr] on section variables. *)
Lemma frechet_lower_strict_general (R : realType) (k : nat)
    (alphas : 'I_k.+2 -> R) :
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  1 - \sum_(i < k.+2) alphas i < \prod_(i < k.+2) (1 - alphas i).
Proof.
move=> Ha0 Ha1.
have Ha01 : forall i, 0 <= alphas i <= 1
  by move=> i; apply/andP; split; [exact: ltW | exact: ltW].
(* Peel off the last factor *)
rewrite big_ord_recr [X in _ < X]big_ord_recr /=.
set P := \prod_(i < k.+1) (1 - alphas (widen_ord (leqnSn k.+1) i)).
set S := \sum_(i < k.+1) alphas (widen_ord (leqnSn k.+1) i).
set a := alphas ord_max.
have Ha_pos : 0 < a := Ha0 ord_max.
have Ha_lt1 : a < 1 := Ha1 ord_max.
have HS_pos : 0 < S.
  rewrite /S (bigD1 (ord0 : 'I_k.+1)) //=.
  apply: ltr_pwDl; first exact: Ha0.
  by apply: sumr_ge0 => i _; exact: ltW.
have HW : 1 - S <= P.
  exact: (@weierstrass_product R k.+1
    (fun i => alphas (widen_ord (leqnSn k.+1) i))
    (fun i => Ha01 _)).
(* Case split: if S >= 1, the LHS is <= 0 < RHS (trivial).
   If S < 1, use weierstrass_strict_2. *)
have HP_pos : 0 < P.
  by apply: prodr_gt0 => i _; rewrite subr_gt0; exact: Ha1.
have H1a : 0 < 1 - a by rewrite subr_gt0.
case: (lerP 1 S) => HS1.
  (* S >= 1: LHS = 1 - S - a <= -a < 0 < P*(1-a) *)
  apply: (lt_le_trans (y := 0)); last by rewrite mulr_ge0 // ltW.
  by rewrite subr_lt0 (le_lt_trans HS1) // ltrDl.
(* S < 1: use weierstrass_strict_2 *)
apply: (lt_le_trans (y := (1 - S) * (1 - a))).
  exact: (@weierstrass_strict_2 R S a HS_pos HS1 Ha_pos Ha_lt1).
by apply: ler_wpM2r; [rewrite subr_ge0; exact: ltW |].
Qed.

(** The strict Weierstrass inequality with a [2 <= k] hypothesis,
    avoiding the [k.+2]-indexed type in the statement. *)
Lemma frechet_lower_strict (R : realType) (k : nat)
    (alphas : 'I_k -> R) :
  (2 <= k)%N ->
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  1 - \sum_(i < k) alphas i < \prod_(i < k) (1 - alphas i).
Proof.
case: k alphas => [|[|k]] // alphas _ Ha0 Ha1.
exact: frechet_lower_strict_general.
Qed.

(* --- Bibliography ---

   frechet_upper_bound, frechet_lower_bound, frechet_sandwich,
   independent_between_frechet,
   frechet_lower_strict_general:
     M. Fréchet, "Généralisation du théorème des probabilités
     totales," Fundamenta Mathematicae, 25:379-387, 1935.
     DOI: 10.4064/fm-25-1-379-387

   weierstrass_product, weierstrass_strict_2:
     D. S. Mitrinović, Analytic Inequalities, Grundlehren der
     mathematischen Wissenschaften, Springer-Verlag, 1970,
     pp. 210-211.  DOI: 10.1007/978-3-642-99970-3

   macro_no_multiplicity, macro_uniform,
   macro_fa_le_hetero, macro_fa_strict_le_hetero:
     P. B. Stark, "Efficient post-election audits of multiple
     contests: 2009 California tests," SSRN, 2009.
     DOI: 10.2139/ssrn.1443314

   positive_dependence_reduces_fa,
   negative_dependence_worsens_fa, dependence_gap,
   dep_fa_achievable, dep_fa_achievable_measure:
     Algebraic consequences of the independence product model.
     Dependence comparison is standard; see P. B. Stark,
     "Risk-limiting postelection audits," IEEE Trans. Inform.
     Forensics Security, 4(4):1005-1014, 2009.
     DOI: 10.1109/TIFS.2009.2034190

   negative_dep_exp_bound, negative_dep_threshold,
   positive_dep_exp_bound, positive_dep_union_bound:
     Transfer of the exponential sandwich and threshold results
     from auditing_1.v through the dependence comparison lemmas.
*)

Print Assumptions dependent_fa_ge_alpha.
Print Assumptions independent_satisfies_marginals.
Print Assumptions independence_worsens_assurance.
Print Assumptions macro_no_multiplicity.
Print Assumptions macro_uniform.
Print Assumptions macro_fa_le_hetero.
