(******************************************************************************)
(*                                                                            *)
(*             Multiplicative Degradation of Risk-Limiting Audits             *)
(*                                                                            *)
(*     Per-contest assurance in risk-limiting audits degrades                 *)
(*     multiplicatively. For k contests, false assurance exceeds any          *)
(*     fixed threshold when k > ln(1/delta)/ln(1/(1-alpha)).                  *)
(*     Formalized over MathComp probability distributions.                    *)
(*                                                                            *)
(*     "Not everything that can be counted counts, and not                    *)
(*     everything that counts can be counted."                                *)
(*     – William Bruce Cameron, 1963                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 20, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import exp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

Section RiskLimitingAudit.

Variable R : realType.

Definition false_assurance (alpha : R) (k : nat) : R :=
  1 - (1 - alpha) ^+ k.

(* Joint pass probability under independence: ps i is the probability
   that contest i passes its individual audit. The product encodes the
   assumption that contest outcomes are stochastically independent. *)
Definition joint_pass (k : nat) (ps : 'I_k -> R) : R :=
  \prod_(i < k) ps i.

Lemma joint_pass_le_uniform (alpha : R) (k : nat) (ps : 'I_k -> R) :
  0 <= alpha ->
  (forall i, 0 <= ps i <= 1 - alpha) ->
  joint_pass ps <= (1 - alpha) ^+ k.
Proof.
move=> Ha0 Hps; rewrite /joint_pass -iter_mulr_1 -big_const_ord.
by apply: ler_prod.
Qed.

Lemma false_assurance_worst_case (alpha : R) (k : nat) (ps : 'I_k -> R) :
  0 <= alpha ->
  (forall i, 0 <= ps i <= 1 - alpha) ->
  false_assurance alpha k <= 1 - joint_pass ps.
Proof.
move=> Ha0 Hps; rewrite /false_assurance lerD2l lerN2.
exact: (joint_pass_le_uniform Ha0 Hps).
Qed.

Lemma false_assurance_0 (alpha : R) :
  false_assurance alpha 0 = 0.
Proof. by rewrite /false_assurance expr0 subrr. Qed.

Lemma false_assurance_1 (alpha : R) :
  false_assurance alpha 1 = alpha.
Proof. by rewrite /false_assurance expr1 opprB addrCA subrr addr0. Qed.

Lemma false_assurance_ge0 (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 -> 0 <= false_assurance alpha k.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance subr_ge0.
apply: exprn_ile1.
- by rewrite subr_ge0.
- by rewrite lerBlDr lerDl.
Qed.

Lemma false_assurance_le1 (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 -> false_assurance alpha k <= 1.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance lerBlDl lerDr.
by apply: exprn_ge0; rewrite subr_ge0.
Qed.

Lemma false_assurance_lt1 (alpha : R) (k : nat) :
  0 < alpha -> alpha < 1 -> false_assurance alpha k < 1.
Proof.
move=> Ha0 Ha1; rewrite /false_assurance ltrBlDl ltrDr.
by rewrite exprn_gt0 // subr_gt0.
Qed.

Lemma union_bound (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 ->
  false_assurance alpha k <= k%:R * alpha.
Proof.
move=> Ha0 Ha1; elim: k => [|k IH].
  by rewrite /false_assurance expr0 subrr mul0r.
rewrite /false_assurance exprS.
have -> : 1 - (1 - alpha) * (1 - alpha) ^+ k =
          false_assurance alpha k + alpha * (1 - alpha) ^+ k.
  by rewrite mulrBl mul1r opprB addrA addrAC.
have Hpow_le1 : (1 - alpha) ^+ k <= 1.
  apply: exprn_ile1.
  - by rewrite subr_ge0.
  - by rewrite lerBlDr lerDl.
apply: (le_trans (lerD IH (ler_wpM2l Ha0 Hpow_le1))).
by rewrite mulr1 [k.+1%:R]mulrSr mulrDl mul1r.
Qed.

Lemma pow_le1_anti (x : R) (m n : nat) :
  0 <= x -> x <= 1 -> (m <= n)%N -> x ^+ n <= x ^+ m.
Proof.
move=> Hx0 Hx1; elim: n m => [|n IH] [|m] //.
- move=> _; rewrite expr0; exact: exprn_ile1.
- move=> /IH Hle; rewrite !exprS.
  exact: (ler_wpM2l Hx0 Hle).
Qed.

Lemma pow_lt1_strict_anti (x : R) (m n : nat) :
  0 < x -> x < 1 -> (m < n)%N -> x ^+ n < x ^+ m.
Proof.
move=> Hx0 Hx1; elim: n m => [|n IH] [|m] //.
- move=> _; rewrite expr0 exprn_ilt1 //; exact: ltW.
- rewrite ltnS => Hmn; rewrite !exprS.
  by rewrite ltr_pM2l // IH.
Qed.

Lemma false_assurance_strict_mono (alpha : R) (k1 k2 : nat) :
  0 < alpha -> alpha < 1 ->
  (k1 < k2)%N -> false_assurance alpha k1 < false_assurance alpha k2.
Proof.
move=> Ha0 Ha1 Hk; rewrite /false_assurance ltrD2l ltrN2.
apply: pow_lt1_strict_anti => //.
- by rewrite subr_gt0.
- by rewrite ltrBlDr ltrDl.
Qed.

Lemma false_assurance_mono (alpha : R) (k1 k2 : nat) :
  0 <= alpha -> alpha <= 1 ->
  (k1 <= k2)%N -> false_assurance alpha k1 <= false_assurance alpha k2.
Proof.
move=> Ha0 Ha1 Hk; rewrite /false_assurance lerD2l lerN2.
apply: pow_le1_anti => //.
- by rewrite subr_ge0.
- by rewrite lerBlDr lerDl.
Qed.

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

Lemma threshold_sensitivity (alpha1 alpha2 : R) (k : nat) :
  0 <= alpha1 -> alpha1 <= alpha2 -> alpha2 <= 1 ->
  forall delta, delta <= false_assurance alpha1 k ->
  delta <= false_assurance alpha2 k.
Proof.
move=> Ha1 Hle Ha2 delta Hd.
apply: (le_trans Hd).
exact: false_assurance_alpha_mono.
Qed.

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

Lemma false_assurance_k0_vacuous (alpha delta : R) :
  0 < delta -> ~~ (delta <= false_assurance alpha 0).
Proof. by move=> Hd; rewrite false_assurance_0 -ltNge. Qed.

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

End RiskLimitingAudit.

From Stdlib Require Import QArith Qpower.

Section ConcreteValidation.

Open Scope Q_scope.

(* alpha = 5%: standard per-contest risk limit (Stark, VLRA). *)
Definition alpha_concrete := Qmake 1 20.
(* delta = 99%: overall confidence target across all contests. *)
Definition delta_concrete := Qmake 99 100.

Lemma concrete_bound_90 :
  (Qpower (1 - alpha_concrete) 90 <= 1 - delta_concrete)%Q.
Proof. by vm_compute; discriminate. Qed.

Lemma concrete_sharp_89_bool :
  Qle_bool (Qpower (1 - alpha_concrete) 89) (1 - delta_concrete) = false.
Proof. by vm_compute. Qed.

Lemma concrete_sharp_89 :
  ~ (Qpower (1 - alpha_concrete) 89 <= 1 - delta_concrete)%Q.
Proof.
by move/Qle_bool_iff; rewrite concrete_sharp_89_bool.
Qed.

End ConcreteValidation.

Close Scope Q_scope.

(* Bridge: transfer concrete rational bounds to any realType via ratr. *)
Section Bridge.

Variable R : realType.

Lemma ratr_false_assurance (q : rat) (k : nat) :
  @false_assurance R (ratr q) k = ratr (1 - (1 - q) ^+ k).
Proof.
by rewrite /false_assurance rmorphB rmorph1 rmorphXn rmorphB rmorph1.
Qed.

Definition alpha_r : rat := 1 / 20%:R.
Definition delta_r : rat := 99%:R / 100%:R.

Lemma bridge_bound_90 :
  ratr delta_r <= @false_assurance R (ratr alpha_r) 90.
Proof.
by rewrite ratr_false_assurance ler_rat /delta_r /alpha_r; vm_compute.
Qed.

Lemma bridge_sharp_89 :
  ~~ (ratr delta_r <= @false_assurance R (ratr alpha_r) 89).
Proof.
by rewrite ratr_false_assurance ler_rat /delta_r /alpha_r; vm_compute.
Qed.

End Bridge.

(* Axiom audit — compile this file and inspect the output to verify
   the axiom footprint is limited to the MathComp realType foundation. *)
Print Assumptions false_assurance_worst_case.
Print Assumptions threshold_crossing.
Print Assumptions per_contest_degradation.
Print Assumptions ln_threshold_bound.
Print Assumptions converse_ln_bound.
Print Assumptions union_bound.
Print Assumptions false_assurance_alpha_mono.
Print Assumptions ratr_false_assurance.
Print Assumptions bridge_bound_90.
