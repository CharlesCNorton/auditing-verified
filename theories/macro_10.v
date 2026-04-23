(******************************************************************************)
(*                                                                            *)
(*     MACRO operational model                                                *)
(*                                                                            *)
(*     A MACRO audit drives certification by a single combined statistic      *)
(*     [M] — a non-negative supermartingale with [E[M_0] <= 1] — whose        *)
(*     acceptance event at horizon [n] is [M n < 1/alpha].  Under the         *)
(*     soundness hypothesis that any surviving wrong outcome forces           *)
(*     [M n >= 1/alpha], Ville's inequality gives                             *)
(*        Pr(accept /\ some contest wrong) <= alpha                          *)
(*     at any contest count [k].                                              *)
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

From Auditing Require Import auditing_1 probability_4 ville_6.

(** ** Operational bound *)

Section MACROOperational.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x, 0 <= mu x.
Hypothesis mu_sum1 : \sum_x mu x = 1.

Variable k : nat.

(** [wrong i x]: contest [i]'s reported outcome is wrong and survives
    the audit at sample [x]. *)
Variable wrong : 'I_k -> pred Omega.

(** [F]: filtration.  [M]: combined audit statistic.  [n]: horizon.
    [alpha]: overall risk limit. *)
Variable F : nat -> Omega -> Omega -> bool.
Variable M : nat -> Omega -> R.
Variable n : nat.
Variable alpha : R.

Hypothesis HF : @filtration Omega F.
Hypothesis Hcell : forall k' x, 0 < \sum_(y | F k' x y) mu y.
Hypothesis HM_sup : @supermartingale R Omega mu F M.
Hypothesis HM_ge0 : forall k' x, 0 <= M k' x.
Hypothesis HM_init : @Exp R Omega mu (M 0) <= 1.
Hypothesis Halpha0 : 0 < alpha.
Hypothesis Halpha1 : alpha < 1.

(** Soundness: any surviving wrong outcome forces [M n] above the
    Ville threshold [1/alpha]. *)
Hypothesis HM_sound :
  forall x, (exists i : 'I_k, wrong i x) -> alpha^-1 <= M n x.

(** Acceptance: [M n] is strictly below the threshold. *)
Definition macro_accept (x : Omega) : bool := M n x < alpha^-1.

(** False-certification event: audit accepts but some contest has a
    surviving wrong outcome. *)
Definition macro_false_cert : pred Omega :=
  fun x => macro_accept x && [exists i : 'I_k, wrong i x].

(** Joint false-certification probability is at most [alpha], with no
    [k] factor.  Acceptance and any surviving wrong outcome are
    incompatible by soundness; the bound then reduces to Ville's
    inequality on the threshold event. *)
Theorem macro_operational_bound :
  @Pr R Omega mu macro_false_cert <= alpha.
Proof.
apply: (@le_trans _ _ (@Pr R Omega mu (fun x => alpha^-1 <= M n x))).
  apply: (@Pr_mono R Omega mu mu_ge0) => x.
  rewrite /macro_false_cert => /andP [Hacc /existsP Hw].
  exfalso; move: Hacc; rewrite /macro_accept ltNge.
  by move/negP; apply; exact: HM_sound.
exact: (@ville_ineq R Omega mu mu_ge0 F M alpha n
          HF HM_sup Hcell HM_ge0 Halpha0 Halpha1 HM_init).
Qed.

(** The false-certification event is empty. *)
Theorem macro_false_cert_empty :
  @Pr R Omega mu macro_false_cert = 0.
Proof.
rewrite /Pr; apply: big1 => x /andP [Hacc /existsP Hw].
exfalso; move: Hacc; rewrite /macro_accept ltNge.
by move/negP; apply; exact: HM_sound.
Qed.

End MACROOperational.

(** ** k-independence *)

Section MACROKIndependence.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x, 0 <= mu x.
Hypothesis mu_sum1 : \sum_x mu x = 1.

Variable F : nat -> Omega -> Omega -> bool.
Variable M : nat -> Omega -> R.
Variable n : nat.
Variable alpha : R.

Hypothesis HF : @filtration Omega F.
Hypothesis Hcell : forall k' x, 0 < \sum_(y | F k' x y) mu y.
Hypothesis HM_sup : @supermartingale R Omega mu F M.
Hypothesis HM_ge0 : forall k' x, 0 <= M k' x.
Hypothesis HM_init : @Exp R Omega mu (M 0) <= 1.
Hypothesis Halpha0 : 0 < alpha.
Hypothesis Halpha1 : alpha < 1.

(** The operational bound is [alpha] at any contest count. *)
Lemma macro_k_independent
    (k1 k2 : nat)
    (wrong1 : 'I_k1 -> pred Omega) (wrong2 : 'I_k2 -> pred Omega) :
  (forall x, (exists i : 'I_k1, wrong1 i x) -> alpha^-1 <= M n x) ->
  (forall x, (exists i : 'I_k2, wrong2 i x) -> alpha^-1 <= M n x) ->
  @Pr R Omega mu
    (fun x => macro_accept M n alpha x && [exists i : 'I_k1, wrong1 i x])
  <= alpha /\
  @Pr R Omega mu
    (fun x => macro_accept M n alpha x && [exists i : 'I_k2, wrong2 i x])
  <= alpha.
Proof.
move=> Hsound1 Hsound2.
split.
- exact: (@macro_operational_bound R Omega mu mu_ge0 k1 wrong1
            F M n alpha HF Hcell HM_sup HM_ge0 HM_init Halpha0 Halpha1 Hsound1).
- exact: (@macro_operational_bound R Omega mu mu_ge0 k2 wrong2
            F M n alpha HF Hcell HM_sup HM_ge0 HM_init Halpha0 Halpha1 Hsound2).
Qed.

End MACROKIndependence.

(** ** Shared-statistic instantiation *)

(** A single supermartingale drives acceptance for all contests.
    Per-contest surviving-wrong is the Ville threshold event on [M],
    so soundness is immediate. *)

Section MACROShared.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x, 0 <= mu x.

Variable F : nat -> Omega -> Omega -> bool.
Variable M : nat -> Omega -> R.
Variable n : nat.
Variable alpha : R.

Hypothesis HF : @filtration Omega F.
Hypothesis Hcell : forall k' x, 0 < \sum_(y | F k' x y) mu y.
Hypothesis HM_sup : @supermartingale R Omega mu F M.
Hypothesis HM_ge0 : forall k' x, 0 <= M k' x.
Hypothesis HM_init : @Exp R Omega mu (M 0) <= 1.
Hypothesis Halpha0 : 0 < alpha.
Hypothesis Halpha1 : alpha < 1.

Variable k : nat.

(** Every contest's surviving-wrong predicate is the Ville threshold
    event on [M]. *)
Definition shared_wrong (_ : 'I_k) : pred Omega :=
  fun x => alpha^-1 <= M n x.

Lemma shared_macro_sound :
  forall x, (exists i : 'I_k, shared_wrong i x) -> alpha^-1 <= M n x.
Proof. by move=> x [i]. Qed.

(** Operational bound at [alpha] for any [k]. *)
Theorem macro_shared_bound :
  @Pr R Omega mu
    (fun x => macro_accept M n alpha x &&
              [exists i : 'I_k, shared_wrong i x])
  <= alpha.
Proof.
apply: (@macro_operational_bound R Omega mu mu_ge0 k shared_wrong
          F M n alpha HF Hcell HM_sup HM_ge0 HM_init Halpha0 Halpha1).
exact: shared_macro_sound.
Qed.

End MACROShared.

(** ** Comparison with multiplicative degradation *)

(** For [k >= 2] at uniform per-contest limit [alpha],
    [false_assurance_hetero = 1 - (1 - alpha)^k] strictly exceeds
    [alpha]. *)
Lemma macro_beats_hetero (R : realType) (k : nat) (alpha : R) :
  0 < alpha -> alpha < 1 -> (2 <= k)%N ->
  alpha < @false_assurance_hetero R k (fun _ : 'I_k => alpha).
Proof.
move=> Ha0 Ha1 Hk.
rewrite false_assurance_hetero_uniform.
have H1 : alpha = @false_assurance R alpha 1 by rewrite false_assurance_1.
rewrite {1}H1.
exact: (@false_assurance_strict_mono R alpha 1 k Ha0 Ha1 Hk).
Qed.

Print Assumptions macro_operational_bound.
Print Assumptions macro_false_cert_empty.
Print Assumptions macro_k_independent.
Print Assumptions macro_shared_bound.
Print Assumptions macro_beats_hetero.
