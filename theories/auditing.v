(******************************************************************************)
(*                                                                            *)
(*             Multiplicative Degradation of Risk-Limiting Audits             *)
(*                                                                            *)
(*     Per-contest assurance in risk-limiting audits degrades                 *)
(*     multiplicatively. For k contests, false assurance exceeds any          *)
(*     fixed threshold when k >= ln(1-delta)/ln(1-alpha).                     *)
(*     Formalized over MathComp realType.                                     *)
(*                                                                            *)
(*     "Thanks for your interest in RLAs."                                    *)
(*     – Philip B. Stark, 2026                                                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 20, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import sequences exp.
From mathcomp.zify Require Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

(** --- Proof automation for recurring risk-bound patterns ---
   r01 closes goals of the form 0 <= 1-x, 0 < 1-x, 1-x <= 1,
   or 1-x < 1 when the complementary hypothesis on x is in
   context. Replaces ad-hoc rewrite chains that recur throughout. *)
Ltac r01 :=
  first [ by rewrite subr_ge0    (* 0 <= 1 - x from x <= 1 *)
        | by rewrite subr_gt0    (* 0 < 1 - x from x < 1 *)
        | by rewrite lerBlDr lerDl (* 1 - x <= 1 from 0 <= x *)
        | by rewrite ltrBlDr ltrDl (* 1 - x < 1 from 0 < x *) ].

(** The exponential of a sum equals the product of exponentials. *)
Lemma expR_sum (R : realType) (k : nat) (f : 'I_k -> R) :
  expR (\sum_(i < k) f i) = \prod_(i < k) expR (f i).
Proof.
by rewrite (big_morph (@expR R) (@expRD R) (expR0 R)).
Qed.

(** The logarithm of a product equals the sum of logarithms (all factors positive). *)
Lemma ln_prod (R : realType) (k : nat) (f : 'I_k -> R) :
  (forall i, 0 < f i) ->
  ln (\prod_(i < k) f i) = \sum_(i < k) ln (f i).
Proof.
move=> Hpos.
have Hprod_pos : 0 < \prod_(i < k) f i by apply: prodr_gt0 => i _.
have Hstep : expR (\sum_(i < k) ln (f i)) = \prod_(i < k) f i.
  rewrite expR_sum; apply: eq_bigr => i _.
  by rewrite lnK // posrE.
by rewrite -Hstep expRK.
Qed.

(** [ln x <= x - 1] for positive [x] (tangent-line inequality for the logarithm). *)
Lemma ln_le_sub1 (R : realType) (x : R) :
  0 < x -> ln x <= x - 1.
Proof.
move=> Hx.
have Hpos : x \is Num.pos by rewrite posrE.
have H := expR_ge1Dx (ln x); rewrite (lnK Hpos) in H.
by rewrite -(lerD2l 1) addrCA subrr addr0.
Qed.

(** [expR(-y) * (1 + y) <= 1] for non-negative [y]. *)
Lemma expR_neg_mul_le1 (R : realType) (y : R) :
  0 <= y -> expR (- y) * (1 + y) <= 1.
Proof.
move=> Hy.
apply: (le_trans (ler_wpM2l (expR_ge0 _) (expR_ge1Dx y))).
by rewrite -expRD addNr expR0.
Qed.

(** Strict exponential bound: [expR x > 1 + x] when [x <> 0]. *)
Lemma expR_gt1Dx (R : realType) (x : R) :
  x != 0 -> 1 + x < expR x.
Proof.
move=> Hx0.
case: (lerP 0 (1 + x / 2)) => Hh0.
- have Hh := expR_ge1Dx (x / 2).
  have Hexp : expR x = expR (x / 2) * expR (x / 2).
    by rewrite -expRD -splitr.
  suff Hlt : 1 + x < (1 + x / 2) * (1 + x / 2).
    apply: (lt_le_trans Hlt); rewrite Hexp.
    have He0 : 0 <= expR (x / 2) := expR_ge0 _.
    by exact: (le_trans (ler_wpM2r Hh0 Hh) (ler_wpM2l He0 Hh)).
  suff : 0 < (1 + x / 2) * (1 + x / 2) - (1 + x) by rewrite subr_gt0.
  have -> : (1 + x / 2) * (1 + x / 2) - (1 + x) = (x / 2) ^+ 2.
    apply/eqP; rewrite subr_eq addrC -expr2 sqrrD expr1n mulr1.
    have -> : (x / 2) *+ 2 = x by rewrite mulr2n -(splitr x).
    by rewrite addrCA addrC.
  rewrite lt0r; apply/andP; split; last exact: sqr_ge0.
  by rewrite expf_neq0 // mulf_neq0 // invr_neq0 // pnatr_eq0.
- apply: (lt_trans _ (expR_gt0 x)).
  have Hlt2 : x / 2 < 0.
    by apply: (lt_trans _ Hh0); apply: ltr_pwDl.
  rewrite [x in 1 + x](splitr x) addrA.
  have := ltrD Hh0 Hlt2; by rewrite addr0.
Qed.

(** Strict tangent-line bound: [ln x < x - 1] when [x > 0] and [x <> 1]. *)
Lemma ln_lt_sub1 (R : realType) (x : R) :
  0 < x -> x != 1 -> ln x < x - 1.
Proof.
move=> Hx Hx1.
have Hpos : x \is Num.pos by rewrite posrE.
have Hln1 : ln x != 0.
  apply/eqP => H; move: Hx1.
  by rewrite -(lnK Hpos) H expR0 eqxx.
have H := expR_gt1Dx Hln1; rewrite (lnK Hpos) in H.
by rewrite -(ltrD2l 1) addrCA subrr addr0.
Qed.

(** ** Algebraic degradation theory *)

Section RiskLimitingAudit.

Variable R : realType.

(** [false_assurance alpha k = 1 - (1 - alpha)^k]: the probability
    that at least one incorrect outcome survives when [k] independent
    contests are audited at risk limit [alpha]. *)
Definition false_assurance (alpha : R) (k : nat) : R :=
  1 - (1 - alpha) ^+ k.

(** [joint_pass ps]: product of per-contest pass probabilities under independence. *)
Definition joint_pass (k : nat) (ps : 'I_k -> R) : R :=
  \prod_(i < k) ps i.

(** The joint pass probability is at most [(1 - alpha)^k] when each factor is bounded by [1 - alpha]. *)
Lemma joint_pass_le_uniform (alpha : R) (k : nat) (ps : 'I_k -> R) :
  0 <= alpha ->
  (forall i, 0 <= ps i <= 1 - alpha) ->
  joint_pass ps <= (1 - alpha) ^+ k.
Proof.
move=> Ha0 Hps; rewrite /joint_pass -iter_mulr_1 -big_const_ord.
by apply: ler_prod.
Qed.

(** Worst-case false assurance: [F(alpha, k) <= 1 - joint_pass ps] for bounded pass probabilities. *)
Lemma false_assurance_worst_case (alpha : R) (k : nat) (ps : 'I_k -> R) :
  0 <= alpha ->
  (forall i, 0 <= ps i <= 1 - alpha) ->
  false_assurance alpha k <= 1 - joint_pass ps.
Proof.
move=> Ha0 Hps; rewrite /false_assurance lerD2l lerN2.
exact: (joint_pass_le_uniform Ha0 Hps).
Qed.

(** Base case: no contests means no degradation. *)
Lemma false_assurance_0 (alpha : R) :
  false_assurance alpha 0 = 0.
Proof. by rewrite /false_assurance expr0 subrr. Qed.

(** A single contest incurs no multiplicity penalty: degradation equals [alpha] itself. *)
Lemma false_assurance_1 (alpha : R) :
  false_assurance alpha 1 = alpha.
Proof. by rewrite /false_assurance expr1 opprB addrCA subrr addr0. Qed.

(** The degradation quantity is well-defined as a probability: it cannot go negative. *)
Lemma false_assurance_ge0 (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 -> 0 <= false_assurance alpha k.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance subr_ge0.
by apply: exprn_ile1; r01.
Qed.

(** Upper probability bound: degradation never exceeds certainty. *)
Lemma false_assurance_le1 (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 -> false_assurance alpha k <= 1.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance lerBlDl lerDr.
by apply: exprn_ge0; r01.
Qed.

(** Strict sub-certainty: for any interior risk limit, some residual confidence remains. *)
Lemma false_assurance_lt1 (alpha : R) (k : nat) :
  0 < alpha -> alpha < 1 -> false_assurance alpha k < 1.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance ltrBlDl ltrDr.
by rewrite exprn_gt0 // subr_gt0.
Qed.

(** Boole/union bound: [F(alpha, k) <= k * alpha]. *)
Lemma union_bound (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 ->
  false_assurance alpha k <= k%:R * alpha.
Proof.
move=> Ha0 Ha1; elim: k => [|k IH].
  by rewrite /false_assurance expr0 subrr mul0r.
rewrite /false_assurance exprS.
(* Distribute: 1 - (1-α)(1-α)^k = [1-(1-α)^k] + α(1-α)^k. *)
have -> : 1 - (1 - alpha) * (1 - alpha) ^+ k =
          false_assurance alpha k + alpha * (1 - alpha) ^+ k.
  by rewrite mulrBl mul1r opprB addrA addrAC.
have Hpow_le1 : (1 - alpha) ^+ k <= 1 by apply: exprn_ile1; r01.
apply: (le_trans (lerD IH (ler_wpM2l Ha0 Hpow_le1))).
by rewrite mulr1 [k.+1%:R]mulrSr mulrDl mul1r.
Qed.

(** Lower exponential bound: [1 - exp(-k*alpha) <= F(alpha, k)]. *)
Lemma false_assurance_ge_exp (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 ->
  1 - expR (- (k%:R * alpha)) <= false_assurance alpha k.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance lerD2l lerN2 -mulrN expRM_natl.
have H1a : 0 <= 1 - alpha by rewrite subr_ge0.
have Hexp : 1 - alpha <= expR (- alpha) := expR_ge1Dx (- alpha).
elim: k => [|k IH]; first by rewrite !expr0.
rewrite !exprS.
apply: (le_trans (ler_wpM2r (exprn_ge0 k H1a) Hexp)).
by apply: ler_wpM2l; [exact: expR_ge0 | exact: IH].
Qed.

(** Upper exponential bound: [F(alpha, k) <= 1 - exp(-k*alpha/(1-alpha))]. *)
Lemma false_assurance_le_exp (alpha : R) (k : nat) :
  0 < alpha -> alpha < 1 ->
  false_assurance alpha k <= 1 - expR (- (k%:R * alpha / (1 - alpha))).
Proof.
move=> Ha0 Ha1.
have H1a : 0 < 1 - alpha by rewrite subr_gt0.
have H1a_ne : 1 - alpha != 0 by rewrite gt_eqF.
have H1a_unit : (1 - alpha) \is a GRing.unit by rewrite unitfE H1a_ne.
set y := alpha / (1 - alpha).
have Hy0 : 0 <= y by rewrite /y divr_ge0 // ltW.
have Hq := expR_ge1Dx y.
have Hprod : (1 + y) * (1 - alpha) = 1.
  by rewrite /y mulrDl mul1r mulrVK // subrK.
have Hsum_pos : 0 < 1 + y by apply: ltr_pwDl.
have Hkey : expR (- y) <= 1 - alpha.
  have : expR (- y) * (1 + y) * (1 - alpha) <= 1 * (1 - alpha).
    by apply: ler_wpM2r; [exact: ltW | exact: expR_neg_mul_le1].
  by rewrite mul1r -mulrA Hprod mulr1.
rewrite /false_assurance lerD2l lerN2.
rewrite /y -mulrA -mulrN expRM_natl.
have H0 : 0 <= expR (- y) by exact: expR_ge0.
elim: k => [|k IH]; first by rewrite !expr0.
rewrite !exprS; apply: (le_trans (ler_wpM2l H0 IH)).
by apply: ler_wpM2r; [apply: exprn_ge0; exact: ltW|].
Qed.

(** The gap between upper and lower exponential bounds is at most [k*alpha^2/(1-alpha)]. *)
Lemma exp_sandwich_gap (alpha : R) (k : nat) :
  0 < alpha -> alpha < 1 ->
  (1 - expR (- (k%:R * alpha / (1 - alpha)))) -
  (1 - expR (- (k%:R * alpha))) <=
  k%:R * alpha / (1 - alpha) - k%:R * alpha.
Proof.
move=> Ha0 Ha1.
have H1a : 0 < 1 - alpha by rewrite subr_gt0.
have H1a_ne : 1 - alpha != 0 by rewrite gt_eqF.
have H1a_unit : (1 - alpha) \is a GRing.unit by rewrite unitfE.
rewrite opprD opprK addrACA subrr add0r addrC.
set a := k%:R * alpha.
set b := a / (1 - alpha).
have Ha_ge0 : 0 <= a by rewrite /a mulr_ge0 // ?ler0n // ltW.
have Hab : a <= b.
  rewrite /b -{1}[a]mulr1 ler_wpM2l //.
  rewrite -[X in X <= _]invr1 lef_pV2 ?posrE ?ltr01 //.
  by rewrite lerBlDr lerDl ltW.
have Hfact : expR (- a) - expR (- b) =
             expR (- a) * (1 - expR (a - b)).
  by rewrite mulrBr mulr1 -expRD addrA addNr add0r.
rewrite Hfact.
have Hexpa_le1 : expR (- a) <= 1.
  rewrite -[X in _ <= X]expR0 ler_expR.
  by rewrite lerNl oppr0.
have Hexp_diff : 1 - expR (a - b) <= b - a.
  have H := expR_ge1Dx (a - b).
  have H2 : - expR (a - b) <= - (1 + (a - b)) by rewrite lerN2.
  have H3 : 1 - expR (a - b) <= 1 - (1 + (a - b)) by rewrite lerD2l.
  have H4 : 1 - (1 + (a - b)) = b - a.
    by rewrite opprD addrA subrr add0r opprB.
  by rewrite H4 in H3.
have Hdiff_ge0 : 0 <= b - a by rewrite subr_ge0.
apply: (le_trans (ler_wpM2l (expR_ge0 _) Hexp_diff)).
apply: (le_trans (ler_wpM2r Hdiff_ge0 Hexpa_le1)).
by rewrite mul1r /b /a.
Qed.

(** Powers of [x] in [0,1] are anti-monotone: [x^n <= x^m] when [m <= n]. *)
Lemma pow_le1_anti (x : R) (m n : nat) :
  0 <= x -> x <= 1 -> (m <= n)%N -> x ^+ n <= x ^+ m.
Proof.
move=> Hx0 Hx1; elim: n m => [|n IH] [|m] //.
- move=> _; rewrite expr0; exact: exprn_ile1.
- move=> /IH Hle; rewrite !exprS.
  exact: (ler_wpM2l Hx0 Hle).
Qed.

(** Strict anti-monotonicity: [x^n < x^m] for [x] in (0,1) and [m < n]. *)
Lemma pow_lt1_strict_anti (x : R) (m n : nat) :
  0 < x -> x < 1 -> (m < n)%N -> x ^+ n < x ^+ m.
Proof.
move=> Hx0 Hx1; elim: n m => [|n IH] [|m] //.
- move=> _; rewrite expr0 exprn_ilt1 //; exact: ltW.
- rewrite ltnS => Hmn; rewrite !exprS.
  by rewrite ltr_pM2l // IH.
Qed.

(** False assurance is strictly increasing in the number of contests. *)
Lemma false_assurance_strict_mono (alpha : R) (k1 k2 : nat) :
  0 < alpha -> alpha < 1 ->
  (k1 < k2)%N -> false_assurance alpha k1 < false_assurance alpha k2.
Proof.
move=> Ha0 Ha1 Hk; rewrite /false_assurance ltrD2l ltrN2.
by apply: pow_lt1_strict_anti => //; r01.
Qed.

(** False assurance is non-decreasing in the number of contests. *)
Lemma false_assurance_mono (alpha : R) (k1 k2 : nat) :
  0 <= alpha -> alpha <= 1 ->
  (k1 <= k2)%N -> false_assurance alpha k1 <= false_assurance alpha k2.
Proof.
move=> Ha0 Ha1 Hk; rewrite /false_assurance lerD2l lerN2.
by apply: pow_le1_anti => //; r01.
Qed.

(** False assurance is non-decreasing in the risk limit [alpha]. *)
Lemma false_assurance_alpha_mono (alpha1 alpha2 : R) (k : nat) :
  0 <= alpha1 -> alpha1 <= alpha2 -> alpha2 <= 1 ->
  false_assurance alpha1 k <= false_assurance alpha2 k.
Proof.
move=> Ha1 Hle Ha2; rewrite /false_assurance lerD2l lerN2.
have H0 : 0 <= 1 - alpha2 by rewrite subr_ge0.
have H1 : 0 <= 1 - alpha1 by rewrite subr_ge0 (le_trans Hle Ha2).
have Hle' : 1 - alpha2 <= 1 - alpha1 by rewrite lerD2l lerN2.
elim: k => [|k IH]; first by rewrite !expr0.
rewrite !exprS; apply: (le_trans (ler_wpM2l H0 IH)).
by apply: ler_wpM2r => //; exact: exprn_ge0.
Qed.

(** Strict monotonicity of [x^k] in [x] for [k > 0] and [0 <= x]. *)
Lemma exprn_strict_mono (x y : R) (k : nat) :
  0 <= x -> x < y -> (0 < k)%N -> x ^+ k < y ^+ k.
Proof.
move=> Hx Hlt; elim: k => [//|k IH] _.
rewrite !exprS; case: k IH => [_|k IH].
  by rewrite !expr0 !mulr1.
have IHk := IH (ltn0Sn k).
have Hy : 0 <= y := le_trans Hx (ltW Hlt).
apply: (le_lt_trans (ler_wpM2l Hx (ltW IHk))).
by rewrite ltr_pM2r // exprn_gt0 // (le_lt_trans Hx Hlt).
Qed.

(** Strict monotonicity in [alpha]: [F(alpha1, k) < F(alpha2, k)] when [alpha1 < alpha2] and [k > 0]. *)
Lemma false_assurance_strict_mono_alpha (alpha1 alpha2 : R) (k : nat) :
  0 <= alpha1 -> alpha1 < alpha2 -> alpha2 < 1 -> (0 < k)%N ->
  false_assurance alpha1 k < false_assurance alpha2 k.
Proof.
move=> Ha1 Hlt Ha2 Hk; rewrite /false_assurance ltrD2l ltrN2.
apply: exprn_strict_mono => //; [by rewrite subr_ge0; exact: ltW | by rewrite ltrD2l ltrN2].
Qed.

(** Joint strict monotonicity: false assurance increases when either [alpha] or [k] strictly increases. *)
Lemma false_assurance_bivariate_strict (alpha1 alpha2 : R) (k1 k2 : nat) :
  0 < alpha1 -> alpha1 <= alpha2 -> alpha2 < 1 ->
  (0 < k1)%N -> (k1 <= k2)%N ->
  (alpha1 < alpha2) || (k1 < k2)%N ->
  false_assurance alpha1 k1 < false_assurance alpha2 k2.
Proof.
move=> Ha1 Hle Ha2 Hk1 Hk /orP [Hlt|Hlt].
- apply: (lt_le_trans _ (false_assurance_mono (ltW (lt_le_trans Ha1 Hle))
                                              (ltW Ha2) Hk)).
  exact: false_assurance_strict_mono_alpha (ltW Ha1) Hlt Ha2 Hk1.
- have Ha1' : alpha1 < 1 := le_lt_trans Hle Ha2.
  apply: (lt_le_trans (false_assurance_strict_mono Ha1 Ha1' Hlt)).
  exact: false_assurance_alpha_mono (ltW Ha1) Hle (ltW Ha2).
Qed.

(** Threshold sensitivity: any [delta] below [F(alpha1, k)] remains below [F(alpha2, k)] for [alpha2 >= alpha1]. *)
Lemma threshold_sensitivity (alpha1 alpha2 : R) (k : nat) :
  0 <= alpha1 -> alpha1 <= alpha2 -> alpha2 <= 1 ->
  forall delta, delta <= false_assurance alpha1 k ->
  delta <= false_assurance alpha2 k.
Proof.
move=> Ha1 Hle Ha2 delta Hd.
apply: (le_trans Hd).
exact: false_assurance_alpha_mono.
Qed.

(** Power difference bound: [y^k - x^k <= k*(y - x)] for [0 <= x <= y <= 1]. *)
Lemma pow_diff_bound (x y : R) (k : nat) :
  0 <= x -> x <= y -> y <= 1 ->
  y ^+ k - x ^+ k <= k%:R * (y - x).
Proof.
move=> Hx0 Hxy Hy1.
have Hy0 := le_trans Hx0 Hxy.
have Hdiff : 0 <= y - x by rewrite subr_ge0.
elim: k => [|k IH]; first by rewrite !expr0 subrr mul0r.
rewrite !exprS.
(* y * y^k - x * x^k
   = y * y^k - y * x^k + y * x^k - x * x^k
   = y*(y^k - x^k) + (y - x)*x^k *)
have Hx1 : x <= 1 := le_trans Hxy Hy1.
suff Hdecomp : y * y ^+ k - x * x ^+ k =
               y * (y ^+ k - x ^+ k) + (y - x) * x ^+ k.
  rewrite Hdecomp.
  have Hxk_le1 : x ^+ k <= 1.
    by apply: exprn_ile1.
  have Hterm1 : y * (y ^+ k - x ^+ k) <= k%:R * (y - x).
    apply: (le_trans (ler_wpM2l Hy0 IH)).
    by rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r;
       [apply: mulr_ge0; [exact: ler0n|]|].
  have Hterm2 : (y - x) * x ^+ k <= y - x.
    by rewrite -{2}(mulr1 (y - x)); apply: ler_wpM2l.
  apply: (le_trans (lerD Hterm1 Hterm2)).
  by rewrite [k.+1%:R]mulrSr mulrDl mul1r.
(* Prove the decomposition identity *)
by rewrite mulrBr [in RHS]mulrBl addrA addrNK.
Qed.

(** [(c + p) * (1 - p) <= c] for [c >= 1] and [0 <= p]. *)
Lemma mul_sub1_le (c p : R) :
  1 <= c -> 0 <= p ->
  (c + p) * (1 - p) <= c.
Proof.
move=> Hc1 Hp0.
have Hkey : p * (1 - p) <= c * p.
  rewrite [p * _]mulrC; apply: ler_wpM2r => //.
  by rewrite lerBlDr; apply: (le_trans Hc1); rewrite lerDl.
have Heq : c = c * (1 - p) + c * p by rewrite -mulrDr subrK mulr1.
rewrite mulrDl [X in _ <= X]Heq; apply: lerD; [exact: lexx | exact: Hkey].
Qed.

(** Lipschitz continuity: [F(alpha2, k) - F(alpha1, k) <= k * (alpha2 - alpha1)]. *)
Lemma false_assurance_lipschitz (alpha1 alpha2 : R) (k : nat) :
  0 <= alpha1 -> alpha1 <= alpha2 -> alpha2 <= 1 ->
  false_assurance alpha2 k - false_assurance alpha1 k <= k%:R * (alpha2 - alpha1).
Proof.
move=> Ha1 Hle Ha2.
rewrite /false_assurance.
have -> : (1 - (1 - alpha2) ^+ k) - (1 - (1 - alpha1) ^+ k) =
          (1 - alpha1) ^+ k - (1 - alpha2) ^+ k.
  by rewrite opprD opprK addrACA subrr add0r addrC.
have -> : alpha2 - alpha1 = (1 - alpha1) - (1 - alpha2).
  by rewrite opprD opprK addrACA subrr add0r addrC.
apply: pow_diff_bound.
- by rewrite subr_ge0.
- by rewrite lerD2l lerN2.
- by rewrite lerBlDr lerDl.
Qed.

(** If [k * ln x <= ln y] then [x^k <= y] (exponentiating preserves the inequality). *)
Lemma pow_le_of_ln_le (x y : R) (k : nat) :
  0 < x -> 0 < y ->
  k%:R * ln x <= ln y -> x ^+ k <= y.
Proof.
move=> Hx Hy Hln.
have Hxk_pos : (x ^+ k) \is Num.pos by rewrite posrE exprn_gt0.
have Hy_pos : y \is Num.pos by rewrite posrE.
rewrite -(lnK Hxk_pos) -(lnK Hy_pos) ler_expR lnXn // -mulr_natl.
exact: Hln.
Qed.

(** Per-contest degradation: if [delta <= F(alpha, k)], then [alpha >= 1 - (1-delta)^(1/k)]. *)
Lemma per_contest_degradation (alpha delta : R) (k : nat) :
  0 < alpha -> alpha < 1 -> 0 < delta -> delta < 1 -> (0 < k)%N ->
  delta <= false_assurance alpha k ->
  alpha >= 1 - (1 - delta) `^ (k%:R)^-1.
Proof.
move=> Ha0 Ha1 Hd0 Hd1 Hk Hfa.
rewrite /false_assurance in Hfa.
have H1a_pos : 0 < 1 - alpha by rewrite subr_gt0.
have H1d_pos : 0 < 1 - delta by rewrite subr_gt0.
have H1a_ge0 := ltW H1a_pos.
have H1d_ge0 := ltW H1d_pos.
have Hpow : (1 - alpha) ^+ k <= 1 - delta.
  by move: Hfa; rewrite lerBrDr => Hfa; rewrite lerBrDl.
have HpowR : (1 - alpha) `^ k%:R <= 1 - delta.
  by rewrite powR_mulrn.
have Hkne0 : k%:R != (0 : R) by rewrite pnatr_eq0 -lt0n.
have Hkinv_ge0 : 0 <= (k%:R : R)^-1 by rewrite invr_ge0 ler0n.
have Hnn1 : (1 - alpha) `^ k%:R \in Num.nneg by rewrite nnegrE powR_ge0.
have Hnn2 : (1 - delta) \in Num.nneg by rewrite nnegrE.
have Hstep : ((1 - alpha) `^ k%:R) `^ (k%:R)^-1 <= (1 - delta) `^ (k%:R)^-1.
  exact: (ge0_ler_powR Hkinv_ge0 Hnn1 Hnn2 HpowR).
rewrite -powRrM mulfV // powRr1 // in Hstep.
by move: Hstep; rewrite lerBlDl => Hstep; rewrite lerBlDr.
Qed.

(** No positive [delta] is achievable at [k = 0]. *)
Lemma false_assurance_k0_vacuous (alpha delta : R) :
  0 < delta -> ~~ (delta <= false_assurance alpha 0).
Proof. by move=> Hd; rewrite false_assurance_0 -ltNge. Qed.

(** Forward logarithmic bound: [ln(1-delta)/ln(1-alpha) <= k] implies [delta <= F(alpha, k)]. *)
Lemma ln_threshold_bound (alpha delta : R) (k : nat) :
  0 < alpha -> alpha < 1 -> 0 < delta -> delta < 1 ->
  ln (1 - delta) / ln (1 - alpha) <= k%:R ->
  delta <= false_assurance alpha k.
Proof.
move=> Ha0 Ha1 Hd0 Hd1 Hk.
have H1a_pos : 0 < 1 - alpha by rewrite subr_gt0.
have H1d_pos : 0 < 1 - delta by rewrite subr_gt0.
have Hln_neg : ln (1 - alpha) < 0.
  by apply: ln_lt0; rewrite H1a_pos /= ltrBlDr ltrDl.
have Hln_neq : ln (1 - alpha) != 0 by exact: ltr0_neq0.
rewrite /false_assurance.
suff Hpow : (1 - alpha) ^+ k <= 1 - delta.
  by rewrite lerBrDl (addrC _ delta) -lerBrDl.
apply: pow_le_of_ln_le H1a_pos H1d_pos _.
rewrite -[X in _ <= X](divfK Hln_neq).
by rewrite ler_wnM2r // ltW.
Qed.

(** Threshold crossing: for any target [delta], sufficiently many contests exceed it. *)
Lemma threshold_crossing (alpha delta : R) :
  0 < alpha -> alpha < 1 -> 0 < delta -> delta < 1 ->
  exists k0 : nat, forall k, (k0 <= k)%N -> delta <= false_assurance alpha k.
Proof.
move=> Ha0 Ha1 Hd0 Hd1.
have H1a_pos : 0 < 1 - alpha by rewrite subr_gt0.
have H1d_pos : 0 < 1 - delta by rewrite subr_gt0.
have Hln_neg : ln (1 - alpha) < 0.
  by apply: ln_lt0; rewrite H1a_pos /= ltrBlDr ltrDl.
set bound := ln (1 - delta) / ln (1 - alpha).
have Hbound_ge0 : 0 <= bound.
  rewrite /bound -(divrNN (ln (1 - delta))).
  apply: divr_ge0; rewrite oppr_ge0.
  - by apply: ln_le0; rewrite lerBlDr lerDl ltW.
  - by apply: ln_le0; rewrite lerBlDr lerDl ltW.
have Hn := archi_boundP Hbound_ge0.
exists (Num.Def.archi_bound bound) => k Hle.
apply: (le_trans _ (false_assurance_mono (ltW Ha0) (ltW Ha1) Hle)).
apply: ln_threshold_bound => //.
exact: ltW.
Qed.

(** No fixed bound: for any [k], there exists [delta] exceeding [F(alpha, k)]. *)
Lemma no_fixed_bound (alpha : R) :
  0 < alpha -> alpha < 1 ->
  forall k, exists delta, 0 < delta /\ delta < 1 /\
    delta > false_assurance alpha k.
Proof.
move=> Ha0 Ha1 k.
exists ((false_assurance alpha k + 1) / 2).
have Hge0 : 0 <= false_assurance alpha k by apply: false_assurance_ge0; exact: ltW.
have Hlt1 : false_assurance alpha k < 1 by exact: false_assurance_lt1.
have [Hfa_lt_mid Hmid_lt_1] := midf_lt Hlt1.
repeat split.
- exact: le_lt_trans Hge0 Hfa_lt_mid.
- exact: Hmid_lt_1.
- exact: Hfa_lt_mid.
Qed.

(** Converse logarithmic bound: [delta <= F(alpha, k)] implies [ln(1-delta)/ln(1-alpha) <= k]. *)
Lemma converse_ln_bound (alpha delta : R) (k : nat) :
  0 < alpha -> alpha < 1 -> 0 < delta -> delta < 1 ->
  delta <= false_assurance alpha k ->
  ln (1 - delta) / ln (1 - alpha) <= k%:R.
Proof.
move=> Ha0 Ha1 Hd0 Hd1 Hfa.
have H1a_pos : 0 < 1 - alpha by rewrite subr_gt0.
have H1d_pos : 0 < 1 - delta by rewrite subr_gt0.
have Hln_neg : ln (1 - alpha) < 0.
  by apply: ln_lt0; rewrite H1a_pos /= ltrBlDr ltrDl.
have Hln_neq : ln (1 - alpha) != 0 by exact: ltr0_neq0.
have Hpow : (1 - alpha) ^+ k <= 1 - delta.
  by move: Hfa; rewrite /false_assurance lerBrDr => Hfa; rewrite lerBrDl.
have Hxk_pos : ((1 - alpha) ^+ k) \is Num.pos by rewrite posrE exprn_gt0.
have Hd_pos : (1 - delta) \is Num.pos by rewrite posrE.
have Hln_ineq : ln ((1 - alpha) ^+ k) <= ln (1 - delta).
  by rewrite ler_ln.
rewrite lnXn // -mulr_natl in Hln_ineq.
by rewrite ler_ndivrMr.
Qed.

(** Threshold equivalence: [delta <= F(alpha, k)] iff [ln(1-delta)/ln(1-alpha) <= k]. *)
Lemma threshold_iff (alpha delta : R) (k : nat) :
  0 < alpha -> alpha < 1 -> 0 < delta -> delta < 1 ->
  (delta <= false_assurance alpha k) =
  (ln (1 - delta) / ln (1 - alpha) <= k%:R).
Proof.
move=> Ha0 Ha1 Hd0 Hd1; apply/idP/idP.
- exact: converse_ln_bound Ha0 Ha1 Hd0 Hd1.
- exact: ln_threshold_bound Ha0 Ha1 Hd0 Hd1.
Qed.

(** Equality in the joint pass bound holds only when every [ps i = 1 - alpha]. *)
Lemma joint_pass_eq_uniform (alpha : R) (k : nat) (ps : 'I_k -> R) :
  0 < alpha -> alpha < 1 ->
  (forall i, 0 <= ps i <= 1 - alpha) ->
  joint_pass ps = (1 - alpha) ^+ k ->
  forall i : 'I_k, ps i = 1 - alpha.
Proof.
move=> Ha0 Ha1 Hps Heq j.
have H1a : 0 < 1 - alpha by rewrite subr_gt0.
apply/eqP; move: (Hps j) => /andP [Hj0 Hj1].
rewrite eq_le Hj1 andTb.
apply/negPn/negP; rewrite -ltNge => Hlt.
suff : joint_pass ps < (1 - alpha) ^+ k by rewrite Heq ltxx.
rewrite /joint_pass -iter_mulr_1 -big_const_ord.
rewrite (bigD1 j) //= [X in _ < X](bigD1 j) //=.
have Hrest : \prod_(i < k | i != j) ps i <= \prod_(i < k | i != j) (1 - alpha).
  by apply: ler_prod => i _; exact: Hps i.
have Hrest_pos : 0 < \prod_(i < k | i != j) (1 - alpha).
  by apply: prodr_gt0 => i _.
apply: (le_lt_trans (ler_wpM2l Hj0 Hrest)).
by rewrite ltr_pM2r.
Qed.

(** Uniqueness: the worst-case false assurance is attained only by the uniform pass vector. *)
Lemma false_assurance_worst_case_unique
    (alpha : R) (k : nat) (ps : 'I_k -> R) :
  0 < alpha -> alpha < 1 ->
  (forall i, 0 <= ps i <= 1 - alpha) ->
  false_assurance alpha k = 1 - joint_pass ps ->
  forall i : 'I_k, ps i = 1 - alpha.
Proof.
move=> Ha0 Ha1 Hps Heq.
apply: joint_pass_eq_uniform Ha0 Ha1 Hps _.
by move: Heq; rewrite /false_assurance /joint_pass => /addrI /oppr_inj ->.
Qed.

(** ** Heterogeneous per-contest risk limits *)

(** [false_assurance_hetero alphas]: false assurance with per-contest risk limits [alphas]. *)
Definition false_assurance_hetero (k : nat) (alphas : 'I_k -> R) : R :=
  1 - \prod_(i < k) (1 - alphas i).

(** Unfold [false_assurance] and reduce to a power inequality
    via [lerD2l] and [lerN2]. *)
Ltac fa_unfold :=
  rewrite /false_assurance lerD2l lerN2.

(** Unfold [false_assurance_hetero] and reduce to a product inequality. *)
Ltac fah_unfold :=
  rewrite /false_assurance_hetero lerD2l lerN2.

(** Heterogeneous false assurance reduces to the uniform formula when all limits are equal. *)
Lemma false_assurance_hetero_uniform (alpha : R) (k : nat) :
  false_assurance_hetero (fun _ : 'I_k => alpha) =
  false_assurance alpha k.
Proof.
by rewrite /false_assurance_hetero /false_assurance big_const_ord iter_mulr_1.
Qed.

(** Monotonicity: increasing any risk limit increases heterogeneous false assurance. *)
Lemma false_assurance_hetero_mono (k : nat)
    (alphas1 alphas2 : 'I_k -> R) :
  (forall i, 0 <= alphas1 i <= alphas2 i) ->
  (forall i, alphas2 i <= 1) ->
  false_assurance_hetero alphas1 <= false_assurance_hetero alphas2.
Proof.
move=> Hle Ha2; rewrite /false_assurance_hetero lerD2l lerN2.
apply: ler_prod => i _.
move: (Hle i) => /andP [H0 Hle_i].
by rewrite subr_ge0 (Ha2 i) andTb lerD2l lerN2.
Qed.

(** Heterogeneous false assurance is non-negative when all limits are in [0,1]. *)
Lemma false_assurance_hetero_ge0 (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  0 <= false_assurance_hetero alphas.
Proof.
move=> Ha; rewrite /false_assurance_hetero subr_ge0.
rewrite -[X in _ <= X](@expr1n R k) -iter_mulr_1 -big_const_ord.
apply: ler_prod => i _.
by move: (Ha i) => /andP [H0 H1]; rewrite subr_ge0 H1 lerBlDr lerDl.
Qed.

(** Probability ceiling: heterogeneous degradation is a valid probability. *)
Lemma false_assurance_hetero_le1 (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero alphas <= 1.
Proof.
move=> Ha; rewrite /false_assurance_hetero lerBlDl lerDr.
by apply: prodr_ge0 => i _; move: (Ha i) => /andP [H0 H1]; rewrite subr_ge0.
Qed.

(** Union bound for heterogeneous limits: [F_hetero <= sum alpha_i]. *)
Lemma false_assurance_hetero_union_bound (k : nat)
    (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero alphas <= \sum_(i < k) alphas i.
Proof.
elim: k alphas => [|n IH] alphas Ha.
  by rewrite /false_assurance_hetero !big_ord0 subrr.
pose alphas' := fun i : 'I_n => alphas (widen_ord (leqnSn n) i).
have Ha' : forall i, 0 <= alphas' i <= 1 by move=> i; exact: Ha _.
have /andP [Ha0 Ha1] := Ha ord_max.
have HIH := IH alphas' Ha'.
have HFA_ge0 := false_assurance_hetero_ge0 Ha'.
rewrite /false_assurance_hetero /= in HIH HFA_ge0 *.
rewrite big_ord_recr [X in _ <= X]big_ord_recr /=.
have Hdist : forall (P a : R), 1 - P * (1 - a) = (1 - P) + P * a.
  by move=> P' a'; rewrite mulrBr mulr1 opprD opprK addrA.
rewrite Hdist.
apply: lerD.
- exact: HIH.
- move: HFA_ge0; rewrite subr_ge0 => HP1.
  by apply: (le_trans (ler_wpM2r Ha0 HP1)); rewrite mul1r.
Qed.

(** Lower exponential bound: [1 - exp(-sum alpha_i) <= F_hetero]. *)
Lemma false_assurance_hetero_ge_exp (k : nat)
    (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  1 - expR (- \sum_(i < k) alphas i) <= false_assurance_hetero alphas.
Proof.
move=> Ha; rewrite /false_assurance_hetero lerD2l lerN2.
rewrite -sumrN expR_sum.
apply: ler_prod => i _.
move: (Ha i) => /andP [H0 H1].
by rewrite subr_ge0 H1 andTb; exact: expR_ge1Dx.
Qed.

(** Upper exponential bound: [F_hetero <= 1 - exp(-sum(alpha_i / (1-alpha_i)))]. *)
Lemma false_assurance_hetero_le_exp (k : nat)
    (alphas : 'I_k -> R) :
  (forall i, 0 < alphas i) ->
  (forall i, alphas i < 1) ->
  false_assurance_hetero alphas <=
    1 - expR (- \sum_(i < k) (alphas i / (1 - alphas i))).
Proof.
move=> Ha0 Ha1; rewrite /false_assurance_hetero lerD2l lerN2.
rewrite -sumrN expR_sum.
apply: ler_prod => i _.
have Hi0 := Ha0 i. have Hi1 := Ha1 i.
have H1a : 0 < 1 - alphas i by rewrite subr_gt0.
have H1a_ne : 1 - alphas i != 0 by rewrite gt_eqF.
have H1a_unit : (1 - alphas i) \is a GRing.unit by rewrite unitfE.
set y := alphas i / (1 - alphas i).
have Hy0 : 0 <= y by rewrite /y divr_ge0 // ltW.
have Hq := expR_ge1Dx y.
have Hprod : (1 + y) * (1 - alphas i) = 1.
  by rewrite /y mulrDl mul1r mulrVK // subrK.
apply/andP; split; first exact: expR_ge0.
have : expR (- y) * (1 + y) * (1 - alphas i) <= 1 * (1 - alphas i).
  by apply: ler_wpM2r; [exact: ltW | exact: expR_neg_mul_le1].
by rewrite mul1r -mulrA Hprod mulr1.
Qed.

(** Strict monotonicity: increasing any single risk limit strictly increases [F_hetero]. *)
Lemma false_assurance_hetero_strict_mono (k : nat)
    (alphas1 alphas2 : 'I_k -> R) (j : 'I_k) :
  (forall i, 0 <= alphas1 i) ->
  (forall i, alphas2 i < 1) ->
  (forall i, alphas1 i <= alphas2 i) ->
  alphas1 j < alphas2 j ->
  false_assurance_hetero alphas1 < false_assurance_hetero alphas2.
Proof.
move=> Ha1_ge0 Ha2_lt1 Hle Hlt.
rewrite /false_assurance_hetero ltrD2l ltrN2.
rewrite (bigD1 j) //= [X in _ < X](bigD1 j) //=.
have Hrest : \prod_(i < k | i != j) (1 - alphas2 i) <=
             \prod_(i < k | i != j) (1 - alphas1 i).
  apply: ler_prod => i _; apply/andP; split.
  - by rewrite subr_ge0; exact: ltW.
  - by rewrite lerD2l lerN2.
have Hrest_pos : 0 < \prod_(i < k | i != j) (1 - alphas1 i).
  apply: prodr_gt0 => i _.
  by rewrite subr_gt0; apply: le_lt_trans (Hle i) _.
have Hj_lt : 1 - alphas2 j < 1 - alphas1 j by rewrite ltrD2l ltrN2.
have Hj_ge0 : 0 <= 1 - alphas2 j by rewrite subr_ge0; exact: ltW.
apply: (le_lt_trans (ler_wpM2l Hj_ge0 Hrest)).
by rewrite ltr_pM2r.
Qed.

(** No fixed bound (heterogeneous): [F_hetero < 1] implies a strictly larger achievable level exists. *)
Lemma no_fixed_bound_hetero (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero alphas < 1 ->
  exists delta, 0 < delta /\ delta < 1 /\
    delta > false_assurance_hetero alphas.
Proof.
move=> Ha Hlt1.
have Hge0 := false_assurance_hetero_ge0 Ha.
exists ((false_assurance_hetero alphas + 1) / 2).
have [Hfa_lt_mid Hmid_lt_1] := midf_lt Hlt1.
repeat split.
- exact: le_lt_trans Hge0 Hfa_lt_mid.
- exact: Hmid_lt_1.
- exact: Hfa_lt_mid.
Qed.

(** Per-contest degradation (heterogeneous): the geometric mean of pass probabilities
    is at most [(1-delta)^(1/k)] when false assurance exceeds [delta]. *)
Lemma per_contest_degradation_hetero (k : nat)
    (alphas : 'I_k -> R) (delta : R) :
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  0 < delta -> delta < 1 -> (0 < k)%N ->
  delta <= false_assurance_hetero alphas ->
  (\prod_(i < k) (1 - alphas i)) `^ (k%:R)^-1 <= (1 - delta) `^ (k%:R)^-1.
Proof.
move=> Ha0 Ha1 Hd0 Hd1 Hk Hfa.
have Hprod_le : \prod_(i < k) (1 - alphas i) <= 1 - delta.
  by move: Hfa; rewrite /false_assurance_hetero lerBrDr => H; rewrite lerBrDl.
have Hkinv_ge0 : 0 <= (k%:R : R)^-1 by rewrite invr_ge0 ler0n.
have Hnn1 : (\prod_(i < k) (1 - alphas i)) \in Num.nneg.
  by rewrite nnegrE; apply: prodr_ge0 => i _; rewrite subr_ge0; exact: (ltW (Ha1 i)).
have Hnn2 : (1 - delta) \in Num.nneg.
  by rewrite nnegrE subr_ge0; exact: (ltW Hd1).
exact: (ge0_ler_powR Hkinv_ge0 Hnn1 Hnn2 Hprod_le).
Qed.

(** Forward logarithmic bound (heterogeneous): [sum ln(1 - alpha_i) <= ln(1-delta)]
    implies [delta <= F_hetero]. *)
Lemma ln_threshold_bound_hetero (k : nat)
    (alphas : 'I_k -> R) (delta : R) :
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  0 < delta -> delta < 1 ->
  \sum_(i < k) ln (1 - alphas i) <= ln (1 - delta) ->
  delta <= false_assurance_hetero alphas.
Proof.
move=> Ha0 Ha1 Hd0 Hd1 Hln.
have Hfact_pos : forall i : 'I_k, 0 < 1 - alphas i by move=> i; rewrite subr_gt0.
have Hprod_pos : (\prod_(i < k) (1 - alphas i)) \is Num.pos.
  by rewrite posrE; apply: prodr_gt0 => i _.
have H1d_pos : (1 - delta) \is Num.pos by rewrite posrE subr_gt0.
rewrite -(ln_prod Hfact_pos) ler_ln // in Hln.
rewrite /false_assurance_hetero.
by rewrite lerBrDl (addrC _ delta) -lerBrDl.
Qed.

(** Converse logarithmic bound (heterogeneous): [delta <= F_hetero] implies
    [sum ln(1 - alpha_i) <= ln(1-delta)]. *)
Lemma converse_ln_bound_hetero (k : nat)
    (alphas : 'I_k -> R) (delta : R) :
  (forall i, 0 < alphas i) -> (forall i, alphas i < 1) ->
  0 < delta -> delta < 1 ->
  delta <= false_assurance_hetero alphas ->
  \sum_(i < k) ln (1 - alphas i) <= ln (1 - delta).
Proof.
move=> Ha0 Ha1 Hd0 Hd1 Hfa.
have Hfact_pos : forall i : 'I_k, 0 < 1 - alphas i by move=> i; rewrite subr_gt0.
have Hprod_le : \prod_(i < k) (1 - alphas i) <= 1 - delta.
  by move: Hfa; rewrite /false_assurance_hetero lerBrDr => H; rewrite lerBrDl.
have Hprod_pos : (\prod_(i < k) (1 - alphas i)) \is Num.pos.
  by rewrite posrE; apply: prodr_gt0 => i _.
have H1d_pos : (1 - delta) \is Num.pos by rewrite posrE subr_gt0.
rewrite -(ln_prod Hfact_pos).
by rewrite ler_ln.
Qed.

(** Sum bound: if [delta <= F_hetero], then [delta <= sum alpha_i]. *)
Lemma false_assurance_hetero_sum_bound (k : nat)
    (alphas : 'I_k -> R) (delta : R) :
  (forall i, 0 <= alphas i <= 1) ->
  delta <= false_assurance_hetero alphas ->
  delta <= \sum_(i < k) alphas i.
Proof.
move=> Ha Hd.
exact: le_trans Hd (false_assurance_hetero_union_bound Ha).
Qed.

(** Threshold crossing (heterogeneous): with a uniform floor [epsilon], sufficiently many
    contests push false assurance above any [delta]. *)
Lemma false_assurance_hetero_threshold (epsilon delta : R) :
  0 < epsilon -> epsilon < 1 -> 0 < delta -> delta < 1 ->
  exists k0 : nat, forall k (alphas : 'I_k -> R),
    (k0 <= k)%N ->
    (forall i, epsilon <= alphas i <= 1) ->
    delta <= false_assurance_hetero alphas.
Proof.
move=> He0 He1 Hd0 Hd1.
have [k0 Hk0] := threshold_crossing He0 He1 Hd0 Hd1.
exists k0 => k alphas Hle Ha.
apply: (le_trans (Hk0 _ Hle)).
rewrite -false_assurance_hetero_uniform.
apply: false_assurance_hetero_mono.
- move=> i; move: (Ha i) => /andP [Hei Hai].
  by apply/andP; split; [exact: ltW|].
- by move=> i; move: (Ha i) => /andP [_ ->].
Qed.

(** Constructive threshold: the Archimedean witness [archi_bound(ln(1-delta)/ln(1-epsilon))]
    is an explicit sufficient contest count. *)
Lemma false_assurance_hetero_threshold_ceil
    (epsilon delta : R) :
  0 < epsilon -> epsilon < 1 -> 0 < delta -> delta < 1 ->
  forall k (alphas : 'I_k -> R),
    (Num.Def.archi_bound (ln (1 - delta) / ln (1 - epsilon)) <= k)%N ->
    (forall i, epsilon <= alphas i <= 1) ->
    delta <= false_assurance_hetero alphas.
Proof.
move=> He0 He1 Hd0 Hd1 k alphas Hle Ha.
set bound := ln (1 - delta) / ln (1 - epsilon).
have Hbound_ge0 : 0 <= bound.
  rewrite /bound -(divrNN (ln (1 - delta))).
  apply: divr_ge0; rewrite oppr_ge0; apply: ln_le0;
    by rewrite lerBlDr lerDl ltW.
have Hk_bound : bound <= k%:R.
  apply: le_trans (ltW (archi_boundP Hbound_ge0)) _.
  by rewrite ler_nat.
have Hfa : delta <= false_assurance epsilon k
  by apply: ln_threshold_bound => //; exact: ltW.
apply: (le_trans Hfa); rewrite -false_assurance_hetero_uniform.
apply: false_assurance_hetero_mono.
- move=> i; move: (Ha i) => /andP [Hei Hai].
  by apply/andP; split; [exact: ltW|].
- by move=> i; move: (Ha i) => /andP [_ ->].
Qed.

(* Optimal risk allocation (AM-GM) is in allocation.v. *)

(* Dependent audit model is in dependent.v. *)

(* --- Sequential/martingale audit theory ---
   The degradation bound is mechanism-agnostic: it uses only the
   per-contest risk limit, not how the audit is conducted. This section
   makes the mechanism-independence explicit.

   In modern sequential RLAs (BRAVO, ALPHA), a non-negative supermartingale
   is updated after each ballot draw. Ville's inequality then guarantees
   P(false pass) <= alpha_i at any stopping time. This formalization does
   NOT prove Ville's inequality (which requires measure-theoretic
   machinery beyond MathComp's current scope). Instead, it ASSUMES the
   per-contest bound holds at each time step and proves that the
   multiplicative degradation follows. The assumed bound is the interface
   between the probabilistic mechanism (external) and the algebraic
   degradation theory (formalized here). *)

(** Worst-case bound (heterogeneous): [F_hetero <= 1 - joint_pass ps] for bounded pass probabilities. *)
Lemma false_assurance_hetero_worst_case (k : nat)
    (alphas : 'I_k -> R) (ps : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  (forall i, 0 <= ps i <= 1 - alphas i) ->
  false_assurance_hetero alphas <= 1 - joint_pass ps.
Proof.
move=> Ha Hps; rewrite /false_assurance_hetero /joint_pass lerD2l lerN2.
by apply: ler_prod.
Qed.

(** Anytime degradation: the bound holds at any collection of stopping times. *)
Lemma anytime_degradation (k : nat)
    (alphas : 'I_k -> R) (pass_prob : 'I_k -> nat -> R)
    (tau : 'I_k -> nat) :
  (forall i, 0 <= alphas i <= 1) ->
  (forall i n, 0 <= pass_prob i n <= 1 - alphas i) ->
  false_assurance_hetero alphas <=
    1 - joint_pass (fun i => pass_prob i (tau i)).
Proof.
move=> Ha Hvalid.
by apply: false_assurance_hetero_worst_case.
Qed.

(* --- Shared/simultaneous audits ---
   Grouping contests reduces the effective count. The grouped false
   assurance (g factors) is at most the individual (k factors). *)

(** Grouping contests reduces false assurance: [g] groups yield at most the full [k]-contest bound. *)
Lemma shared_audit_bound (k g : nat)
    (alphas : 'I_k -> R)
    (witness : 'I_g -> 'I_k) :
  injective witness ->
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero (fun j => alphas (witness j)) <=
    false_assurance_hetero alphas.
Proof.
move=> Hwit_inj Halpha.
rewrite /false_assurance_hetero lerD2l lerN2.
set f := fun i : 'I_k => 1 - alphas i.
have Hf01 : forall i, 0 <= f i <= 1.
  by move=> i; move: (Halpha i) => /andP [H0 H1];
    apply/andP; split; [rewrite subr_ge0|rewrite lerBlDr lerDl].
set S := map witness (index_enum 'I_g).
rewrite [X in X <= _](bigID (mem S)) /=.
have Heq : \prod_(i < k | i \in S) f i = \prod_(j < g) f (witness j).
  rewrite -big_filter.
  have Hperm : perm_eq [seq i <- index_enum 'I_k | i \in S] S.
    apply: uniq_perm.
    - by rewrite filter_uniq // index_enum_uniq.
    - by rewrite /S (map_inj_uniq (f := witness) Hwit_inj) index_enum_uniq.
    - by move=> x; rewrite mem_filter mem_index_enum andbT.
  rewrite (perm_big S Hperm).
  by rewrite /S -(big_map witness predT f (r := index_enum _)).
have Hle1 : \prod_(i < k | i \notin S) f i <= 1.
  elim/big_rec: _ => [//|j x _ Hx].
  move: (Hf01 j) => /andP [H0 H1].
  by apply: (le_trans (ler_wpM2l H0 Hx)); rewrite mulr1.
have Hge0 : 0 <= \prod_(i < k | i \in S) f i.
  by apply: prodr_ge0 => i _; move: (Hf01 i) => /andP [].
rewrite Heq -[X in _ <= X]mulr1.
have Hge0' : 0 <= \prod_(j < g) f (witness j) by rewrite -Heq.
by apply: ler_wpM2l.
Qed.

(** Surjective grouping: any surjective assignment to groups yields a representative
    with grouped false assurance at most the full. *)
Lemma shared_audit_bound_surj (k g : nat)
    (alphas : 'I_k -> R)
    (assign : 'I_k -> 'I_g) :
  (forall j : 'I_g, exists i : 'I_k, assign i = j) ->
  (forall i, 0 <= alphas i <= 1) ->
  exists witness : 'I_g -> 'I_k,
    injective witness /\
    false_assurance_hetero (fun j => alphas (witness j)) <=
      false_assurance_hetero alphas.
Proof.
move=> Hsurj Halpha.
(* Constructive witness via fintype pick (enumeration search). *)
have Hpick : forall j : 'I_g, {i : 'I_k | assign i = j}.
  move=> j; case: (pickP (fun i : 'I_k => assign i == j)) => [i /eqP Hi|Hnone].
  - by exists i.
  - exfalso; have [i Hi] := Hsurj j.
    by have := Hnone i; rewrite Hi eqxx.
pose witness j := sval (Hpick j).
have Hassign : forall j, assign (witness j) = j.
  by move=> j; exact: (svalP (Hpick j)).
have Hinj : injective witness.
  by move=> j1 j2 Heq; apply/eqP; rewrite -[j1]Hassign -[j2]Hassign Heq eqxx.
exists witness; split; first exact: Hinj.
exact: shared_audit_bound Hinj Halpha.
Qed.

(* --- Impossibility and tightness --- *)

(** The union bound is tight at [k = 1]: [F(alpha, 1) = 1 * alpha]. *)
Lemma union_bound_tight_1 (alpha : R) :
  false_assurance alpha 1 = 1%:R * alpha.
Proof. by rewrite false_assurance_1 mul1r. Qed.

(** The union bound is strict for [k >= 2]: [F(alpha, k) < k * alpha]. *)
Lemma union_bound_strict (alpha : R) (k : nat) :
  0 < alpha -> alpha < 1 -> (2 <= k)%N ->
  false_assurance alpha k < k%:R * alpha.
Proof.
move=> Ha0 Ha1; case: k => [//|[//|k]] _.
rewrite /false_assurance exprS mulrBl mul1r opprB addrA addrAC.
(* Goal: F(k+1) + alpha * (1-alpha)^{k+1} < (k+2) * alpha *)
(* Strategy: F(k+1) <= (k+1)*alpha, alpha*pow < alpha, sum < (k+2)*alpha *)
have HIH : false_assurance alpha k.+1 <= k.+1%:R * alpha :=
  union_bound k.+1 (ltW Ha0) (ltW Ha1).
have H1a_lt1 : 1 - alpha < 1 by rewrite ltrBlDr ltrDl.
have H1a_ge0 : 0 <= 1 - alpha by rewrite subr_ge0; exact: ltW.
have Hpow_lt1 : (1 - alpha) ^+ k.+1 < 1.
  apply: (le_lt_trans _ H1a_lt1).
  rewrite -[X in _ <= X]expr1.
  by apply: pow_le1_anti; [| exact: ltW |].
(* Split: F(k+1) <= (k+1)*alpha and alpha*pow < alpha *)
have -> : k.+2%:R * alpha = k.+1%:R * alpha + alpha.
  by rewrite -[X in _ + X]mul1r -mulrDl -natr1.
apply: (lt_le_trans _ (lerD HIH (lexx alpha))).
rewrite ltrD2l -subr_gt0.
have -> : alpha - alpha * (1 - alpha) ^+ k.+1 =
          alpha * (1 - (1 - alpha) ^+ k.+1).
  by rewrite mulrBr mulr1.
by rewrite mulr_gt0 // subr_gt0.
Qed.

(* --- Conservative risk limits ---
   In practice, the per-contest risk limit alpha_i is a conservative
   upper bound on the false-certification probability, not its exact
   value. The actual risk r_i for a specific wrong outcome is
   generally below alpha_i. The worst-case bound treats alpha_i as
   the exact risk. These results formalize the conservatism: the
   nominal bound overestimates whenever any contest's actual risk
   falls below its limit, and equality holds only when every contest
   achieves its limit exactly. *)

(** Conservative bound: actual risks below limits yield lower false assurance than the nominal bound. *)
Lemma conservative_bound (k : nat) (alphas risks : 'I_k -> R) :
  (forall i, 0 <= risks i <= alphas i) ->
  (forall i, alphas i <= 1) ->
  false_assurance_hetero risks <= false_assurance_hetero alphas.
Proof. exact: false_assurance_hetero_mono. Qed.

(** Strict conservatism: if any contest's actual risk is strictly below its limit, false assurance drops. *)
Lemma conservative_strict (k : nat)
    (alphas risks : 'I_k -> R) (j : 'I_k) :
  (forall i, 0 <= risks i) ->
  (forall i, alphas i < 1) ->
  (forall i, risks i <= alphas i) ->
  risks j < alphas j ->
  false_assurance_hetero risks < false_assurance_hetero alphas.
Proof. exact: false_assurance_hetero_strict_mono. Qed.

(** Tightness: equality between nominal and actual false assurance forces every risk to equal its limit. *)
Lemma conservative_tight (k : nat) (alphas risks : 'I_k -> R) :
  (forall i, 0 <= risks i) ->
  (forall i, alphas i < 1) ->
  (forall i, risks i <= alphas i) ->
  false_assurance_hetero risks = false_assurance_hetero alphas ->
  forall i, risks i = alphas i.
Proof.
move=> Hr0 Ha1 Hle Heq i.
case: (boolP (risks i == alphas i)) => [/eqP // | Hne].
have Hlt : risks i < alphas i by rewrite lt_neqAle Hne Hle.
suff : false_assurance_hetero risks < false_assurance_hetero alphas.
  by rewrite Heq ltxx.
exact: (false_assurance_hetero_strict_mono Hr0 Ha1 Hle Hlt).
Qed.

(** ** False certification rate (FCR) *)
(* ---
   The right/wrong partition splits contests into those with correct
   reported outcomes and those with wrong outcomes. Only wrong contests
   can produce false certifications. V counts the number of wrong
   contests that pass their audit (false certifications). FCR is the
   ratio V / ((k-m) + V), where m is the number of wrong contests
   and k-m is the number of correct contests. *)

Section FCR.

Variable k : nat.
Variable wrong : 'I_k -> bool.

(** [num_wrong]: the number of contests with wrong reported outcomes. *)
Definition num_wrong : nat := #|[pred i | wrong i]|.

(* Pass probabilities for each contest *)
Variable pass_prob : 'I_k -> R.

(** [false_cert_count]: sum of pass probabilities over wrong contests (expected false certifications). *)
Definition false_cert_count : R :=
  \sum_(i < k | wrong i) pass_prob i.

(* Each wrong contest's pass probability is bounded by its risk limit *)
Variable alphas : 'I_k -> R.

(** The false certification count is bounded by the sum of risk limits over wrong contests. *)
Lemma false_cert_count_bound :
  (forall i, wrong i -> pass_prob i <= alphas i) ->
  false_cert_count <= \sum_(i < k | wrong i) alphas i.
Proof.
move=> Hle; apply: ler_sum => i Hi.
exact: Hle.
Qed.

(** The FCR denominator [(k-m) + V >= 1] when there are more contests than wrong outcomes. *)
Lemma fcr_denom_ge1 :
  (num_wrong < k)%N ->
  (forall i, 0 <= pass_prob i) ->
  1 <= (k - num_wrong)%:R + false_cert_count.
Proof.
move=> Hlt Hge0.
have Hkm : (0 < k - num_wrong)%N by rewrite subn_gt0.
have H1 : 1 <= (k - num_wrong)%:R :> R by rewrite ler1n.
apply: (le_trans H1); rewrite lerDl.
by apply: sumr_ge0 => i _; exact: Hge0.
Qed.

(** [fcr]: false certification rate [V / ((k-m) + V)]. *)
Definition fcr : R :=
  false_cert_count / ((k - num_wrong)%:R + false_cert_count).

(** First FCR bound: [FCR <= (sum alpha_i over wrong) / (k - m)]. *)
Lemma fcr_first_bound :
  (num_wrong < k)%N ->
  (forall i, 0 <= pass_prob i) ->
  (forall i, wrong i -> pass_prob i <= alphas i) ->
  fcr <= (\sum_(i < k | wrong i) alphas i) / (k - num_wrong)%:R.
Proof.
move=> Hlt Hpp Hle.
have Hc : 0 < (k - num_wrong)%:R :> R by rewrite ltr0n subn_gt0.
have HV : 0 <= false_cert_count by apply: sumr_ge0 => i _; exact: Hpp.
have Hcv : 0 < (k - num_wrong)%:R + false_cert_count :> R.
  by apply: (lt_le_trans Hc); rewrite lerDl.
have HVS := false_cert_count_bound Hle.
(* Step 1: V/(c+V) <= V/c — larger denominator, smaller fraction *)
have H1 : fcr <= false_cert_count / (k - num_wrong)%:R.
  rewrite /fcr; apply: ler_wpM2l => //.
  rewrite lef_pV2 ?posrE //.
  by rewrite lerDl.
(* Step 2: V/c <= S/c *)
apply: (le_trans H1).
have Hcinv : 0 <= ((k - num_wrong)%:R)^-1 :> R by rewrite invr_ge0; exact: ltW.
exact: (ler_wpM2r Hcinv HVS).
Qed.

(** Tight FCR bound: [V/(c+V) <= S/(c+S)] by monotonicity of [x/(c+x)]. *)
Lemma fcr_tight_bound :
  (num_wrong < k)%N ->
  (forall i, 0 <= pass_prob i) ->
  (forall i, wrong i -> pass_prob i <= alphas i) ->
  fcr <= (\sum_(i < k | wrong i) alphas i) /
         ((k - num_wrong)%:R + \sum_(i < k | wrong i) alphas i).
Proof.
move=> Hlt Hpp Hle.
set c := (k - num_wrong)%:R.
set V := false_cert_count.
set S := \sum_(i < k | wrong i) alphas i.
have Hc : 0 < c :> R by rewrite /c ltr0n subn_gt0.
have HV : 0 <= V by apply: sumr_ge0 => i _; exact: Hpp.
have HVS := false_cert_count_bound Hle.
have Hcv : 0 < c + V :> R.
  by apply: (lt_le_trans Hc); rewrite lerDl.
have Hcs : 0 < c + S :> R.
  by apply: (lt_le_trans Hc); rewrite lerDl; exact: le_trans HV HVS.
rewrite /fcr ler_pdivrMr // mulrAC ler_pdivlMr // !mulrDr.
by rewrite [V * S]mulrC lerD2r ler_wpM2r // ltW.
Qed.

(** [fcr_tight_bound] is strictly tighter than [fcr_first_bound]
    when [V > 0] (at least one wrong contest passes with positive
    probability): [S/(c+S) < S/c]. *)
Lemma fcr_tight_lt_first :
  (num_wrong < k)%N ->
  (forall i, 0 <= pass_prob i) ->
  (forall i, wrong i -> pass_prob i <= alphas i) ->
  0 < false_cert_count ->
  (\sum_(i < k | wrong i) alphas i) /
    ((k - num_wrong)%:R + \sum_(i < k | wrong i) alphas i) <
  (\sum_(i < k | wrong i) alphas i) / (k - num_wrong)%:R.
Proof.
move=> Hlt Hpp Hle HVpos.
set c := (k - num_wrong)%:R.
set S := \sum_(i < k | wrong i) alphas i.
have Hc : 0 < c by rewrite /c ltr0n subn_gt0.
have HV0 : 0 <= false_cert_count by exact: ltW.
have HVS := false_cert_count_bound Hle.
have HS : 0 < S by exact: lt_le_trans HVpos HVS.
have Hcs : 0 < c + S by rewrite addr_gt0.
rewrite ltr_pdivrMr // mulrAC ltr_pdivlMr // mulrDr ltrDl.
by exact: mulr_gt0.
Qed.

(** FWER dominates FCR: the family-wise error rate is at least the false certification rate. *)
Lemma fwer_ge_fcr :
  (num_wrong < k)%N ->
  (forall i, 0 <= pass_prob i) ->
  (forall i, wrong i -> pass_prob i <= 1) ->
  fcr <= 1 - \prod_(i < k | wrong i) (1 - pass_prob i).
Proof.
move=> Hlt Hpp Hp1.
set c := (k - num_wrong)%:R : R.
set V := false_cert_count.
set P := \prod_(i < k | wrong i) (1 - pass_prob i).
have Hc : 0 < c by rewrite /c ltr0n subn_gt0.
have Hc1 : 1 <= c :> R by rewrite /c ler1n subn_gt0.
have HV : 0 <= V by apply: sumr_ge0 => i _; exact: Hpp.
have Hcv : 0 < c + V by apply: (lt_le_trans Hc); rewrite lerDl.
(* Key: (c + V) * P <= c, then derive fcr <= 1 - P *)
suff Hcross : (c + V) * P <= c.
  have Hle : V <= (1 - P) * (c + V).
    rewrite -subr_ge0 mulrBl mul1r [P * _]mulrC addrAC addrK subr_ge0.
    exact: Hcross.
  rewrite /fcr /V /c.
  have Hcv_inv : 0 <= (c + V)^-1 :> R by rewrite invr_ge0; exact: ltW.
  have H := ler_wpM2r Hcv_inv Hle.
  by rewrite /c /V mulfK ?gt_eqF // in H.
(* Prove (c + V) * P <= c by big_rec2 *)
rewrite /V /false_cert_count /P.
pose K v p := (c + v) * p <= c /\ 0 <= p /\ p <= 1.
suff HK : K (\sum_(i < k | wrong i) pass_prob i)
             (\prod_(i < k | wrong i) (1 - pass_prob i)) by exact: HK.1.
apply: big_rec2 => [|i vi pi Hwi [IH [HP0 HP1]]].
- by rewrite /K /= addr0 mulr1; split; [|split; [exact: ler01|]].
- set p := pass_prob i.
  have Hp0 : 0 <= p := Hpp i.
  have Hp1_ : p <= 1 := Hp1 i Hwi.
  have H1p : 0 <= 1 - p by r01.
  split; [|split].
  + (* (c + (p + vi)) * ((1-p) * pi) <= c *)
    have Ht1 : (c + vi) * (1 - p) * pi <= c * (1 - p).
      rewrite -mulrA [(1 - p) * pi]mulrC mulrA.
      by apply: ler_wpM2r; [exact: H1p | exact: IH].
    have Ht2 := ler_wpM2l (mulr_ge0 Hp0 H1p) HP1.
    rewrite mulr1 in Ht2.
    rewrite mulrA [c + _]addrCA addrC mulrDl mulrDl.
    apply: (le_trans (lerD Ht1 Ht2)).
    by rewrite -mulrDl; exact: mul_sub1_le Hc1 Hp0.
  + by apply: mulr_ge0.
  + apply: (le_trans (ler_wpM2l H1p HP1)).
    by rewrite mulr1; rewrite lerBlDr lerDl.
Qed.

End FCR.

(* MACRO audit model is in dependent.v. *)

End RiskLimitingAudit.

(* Two-point distribution is in probability.v. *)

Strategy 100 [false_assurance false_assurance_hetero joint_pass].

(* Ballot overlap theory is in overlap.v. *)

(* Finite probability space and independence are in probability.v. *)

(* Discrete supermartingale theory is in ville.v. *)

(* Continuity and differentiability results are in continuity.v,
   separated to isolate MathComp Analysis topology imports from
   Stdlib scope conflicts. See continuity.v for:
   - false_assurance_continuous_alpha
   - false_assurance_hetero_continuous_coord
   - false_assurance_hetero_derivable_coord (C-infinity) *)

(* Concrete validation, Maricopa instantiation, Q-to-R transfer,
   and the min_k extraction target are in concrete.v. *)


(* Axiom audit — compile this file and inspect the output to verify
   the axiom footprint is limited to the MathComp realType foundation. *)
Print Assumptions false_assurance_worst_case.
Print Assumptions threshold_crossing.
Print Assumptions per_contest_degradation.
Print Assumptions ln_threshold_bound.
Print Assumptions converse_ln_bound.
Print Assumptions union_bound.
Print Assumptions false_assurance_ge_exp.
Print Assumptions false_assurance_le_exp.
Print Assumptions false_assurance_alpha_mono.
Print Assumptions joint_pass_eq_uniform.
Print Assumptions false_assurance_worst_case_unique.
Print Assumptions false_assurance_hetero_mono.
Print Assumptions false_assurance_hetero_union_bound.
Print Assumptions false_assurance_hetero_le_exp.
Print Assumptions false_assurance_hetero_strict_mono.
Print Assumptions no_fixed_bound_hetero.
Print Assumptions per_contest_degradation_hetero.
Print Assumptions ln_threshold_bound_hetero.
Print Assumptions converse_ln_bound_hetero.
Print Assumptions false_assurance_lipschitz.
Print Assumptions false_assurance_hetero_worst_case.
Print Assumptions anytime_degradation.
Print Assumptions conservative_bound.
Print Assumptions conservative_strict.
Print Assumptions conservative_tight.
Print Assumptions fcr_first_bound.
Print Assumptions false_assurance_hetero_threshold_ceil.
Print Assumptions fcr_tight_bound.
Print Assumptions fwer_ge_fcr.

(* --- Bibliography ---

   Provenance of each key result, mapping lemma names to their
   published source. DOIs are provided where they exist.

   false_assurance, false_assurance_ge0, false_assurance_le1,
   false_assurance_mono, false_assurance_strict_mono,
   threshold_crossing, threshold_iff, per_contest_degradation,
   no_fixed_bound:
     Z. Sidak, "Rectangular confidence regions for the means of
     multivariate normal distributions," J. Amer. Statist. Assoc.,
     62(318):626-633, 1967.
     DOI: 10.1080/01621459.1967.10482935

   false_assurance_worst_case, joint_pass_le_uniform,
   false_assurance_worst_case_unique, joint_pass_eq_uniform,
   ln_threshold_bound, converse_ln_bound,
   false_assurance_hetero (all), conservative_bound,
   conservative_strict, conservative_tight:
     P. B. Stark, "Risk-limiting postelection audits: conservative
     P-values from common probability inequalities," IEEE Trans.
     Inform. Forensics Security, 4(4):1005-1014, 2009.
     DOI: 10.1109/TIFS.2009.2034190

   overlap_bound, overlap_improvement, overlap_strict_improvement,
   overlap_refinement_mono, full_overlap_bound:
     M. Lindeman and P. B. Stark, "A gentle introduction to
     risk-limiting audits," IEEE Security & Privacy, 10(5):42-49,
     2012.
     DOI: 10.1109/MSP.2012.56

   union_bound, union_bound_strict, union_bound_tight_1:
     G. Boole, An Investigation of the Laws of Thought, 1854.
     DOI (Cambridge reprint): 10.1017/CBO9780511693090

   false_assurance_ge_exp, false_assurance_le_exp,
   exp_sandwich_gap, false_assurance_hetero_ge_exp,
   false_assurance_hetero_le_exp:
     Standard calculus bound 1-x <= exp(-x) applied termwise to the
     Sidak product. Implicit in Stark (2009).

   am_gm, am_gm_ge0, uniform_allocation_optimal,
   uniform_allocation_strict, uniform_allocation_unique:
     AM-GM inequality (Cauchy, 1821). Application to optimal risk
     allocation is implicit in the Sidak/Bonferroni literature.

   macro_no_multiplicity, macro_uniform, macro_false_assurance,
   macro_fa_le_hetero, macro_fa_strict_le_hetero:
     P. B. Stark, "Efficient post-election audits of multiple
     contests: 2009 California tests," SSRN, 2009.
     DOI: 10.2139/ssrn.1443314

   frechet_upper_bound, frechet_lower_bound, frechet_sandwich,
   independent_between_frechet:
     M. Frechet, "Generalisation du theoreme des probabilites
     totales," Fundamenta Mathematicae, 25:379-387, 1935.
     DOI: 10.4064/fm-25-1-379-387

   weierstrass_product:
     Classical product inequality (Weierstrass). See D. S. Mitrinovic,
     Analytic Inequalities, Springer, 1970.
     DOI: 10.1007/978-3-642-99970-3

   anytime_degradation (hypothesis interface):
     J. Ville, Etude critique de la notion de collectif, Gauthier-
     Villars, 1939. (Pre-DOI monograph.)
     P. B. Stark, "ALPHA: audit that learns from previously hand-
     audited ballots," Ann. Appl. Stat., 17(1):641-679, 2023.
     DOI: 10.1214/22-AOAS1646

   dependence_gap, positive_dependence_reduces_fa,
   negative_dependence_worsens_fa, dep_fa_achievable:
     Algebraic consequences of the independence product model.
     Dependence comparison is standard; see Stark (2009).

   false_assurance_continuous_alpha,
   false_assurance_hetero_continuous_coord:
     Standard continuity of polynomial functions. No specific
     published source.

   false_assurance_lipschitz, pow_diff_bound:
     Quantitative sensitivity analysis. The k-Lipschitz bound is
     a direct consequence of the mean value theorem applied to
     x^k on [0,1].
*)

