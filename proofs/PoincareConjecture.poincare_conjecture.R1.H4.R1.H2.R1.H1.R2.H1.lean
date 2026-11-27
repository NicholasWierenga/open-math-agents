import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Analysis.ODE.Gronwall

/-!
A comparison across a finite list of regular Ricci-flow intervals separated
by downward jumps in width. The scalar comparison and threshold formulas are
adapted from DifferentialGeometry v0.1.3, revision
7a48598d35109aa99d1cc678e2724c213cdf4ff3, under Apache-2.0.
-/

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

def extinctionThreshold (c A : ℝ) : ℝ :=
  (c ^ (1 / 4 : ℝ) + A / (8 * Real.pi * c ^ (3 / 4 : ℝ))) ^ 4 - c

private theorem fourth_root_pow {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  simpa using Real.rpow_inv_natCast_pow hx (by norm_num : (4 : ℕ) ≠ 0)

theorem extinctionThreshold_lt_iff {c A H : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hH : 0 ≤ H) :
    extinctionThreshold c A < H ↔
      A / c ^ (3 / 4 : ℝ) -
        8 * Real.pi * ((H + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ)) < 0 := by
  have hc34 : 0 < c ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hc _
  have hp : 0 < 8 * Real.pi := by positivity
  have hsum : 0 < H + c := add_pos_of_nonneg_of_pos hH hc
  have hz : 0 ≤ c ^ (1 / 4 : ℝ) + A / (8 * Real.pi * c ^ (3 / 4 : ℝ)) :=
    add_nonneg (Real.rpow_nonneg hc.le _) (div_nonneg hA (mul_pos hp hc34).le)
  have hroot : 0 ≤ (H + c) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hsum.le _
  have hpowers := pow_lt_pow_iff_left₀ hz hroot (by norm_num : (4 : ℕ) ≠ 0)
  rw [fourth_root_pow hsum.le] at hpowers
  have hdivide : A / (8 * Real.pi * c ^ (3 / 4 : ℝ)) =
      (A / c ^ (3 / 4 : ℝ)) / (8 * Real.pi) := by ring
  rw [extinctionThreshold, sub_lt_iff_lt_add, hpowers, hdivide]
  constructor
  · intro h
    have hm := (div_lt_iff₀ hp).mp (show A / c ^ (3 / 4 : ℝ) / (8 * Real.pi) <
        (H + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ) by linarith)
    nlinarith
  · intro h
    have hm : A / c ^ (3 / 4 : ℝ) / (8 * Real.pi) <
        (H + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ) :=
      (div_lt_iff₀ hp).mpr (by nlinarith)
    linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

def widthComparisonBound (T W : ℝ) (t : ℝ) : ℝ :=
  W * ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) +
    2 * Real.pi * (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) -
      2 * Real.pi * (4 * t + 1)

private theorem widthComparisonBound_factor {T W t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    widthComparisonBound T W t =
      (4 * t + 1) ^ (3 / 4 : ℝ) *
        (W * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ + 2 * Real.pi * (4 * T + 1) ^ (1 / 4 : ℝ) -
          2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)) := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  have hd14 : (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) = 4 * t + 1 := by
    rw [← Real.rpow_add hd]
    norm_num
  have hdiv : ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) =
      (4 * t + 1) ^ (3 / 4 : ℝ) * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [Real.div_rpow hd.le hc.le, div_eq_mul_inv]
  rw [widthComparisonBound, hdiv]
  set A := (4 * t + 1) ^ (3 / 4 : ℝ)
  set B := (4 * t + 1) ^ (1 / 4 : ℝ)
  set C := ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹
  set E := (4 * T + 1) ^ (1 / 4 : ℝ)
  have hAB : A * B = 4 * t + 1 := hd14
  rw [← hAB]
  ring

theorem widthComparisonBound_self {T W : ℝ} (hT : 0 ≤ T) :
    widthComparisonBound T W T = W := by
  have hc : 0 < 4 * T + 1 := by linarith
  have hdiv : (4 * T + 1) / (4 * T + 1) = (1 : ℝ) := by field_simp
  have h34 : (4 * T + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) = 4 * T + 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  rw [widthComparisonBound, hdiv, Real.one_rpow, mul_one]
  have hmid : 2 * Real.pi * (4 * T + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) =
      2 * Real.pi * (4 * T + 1) := by
    rw [mul_assoc, h34]
  rw [hmid]
  ring

theorem widthComparisonBound_mono_width {T t W W' : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (h : W ≤ W') : widthComparisonBound T W t ≤ widthComparisonBound T W' t := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  have hpow : 0 ≤ ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (div_nonneg hd.le hc.le) _
  have hmul := mul_le_mul_of_nonneg_right h hpow
  unfold widthComparisonBound
  linarith

theorem widthComparisonBound_neg_iff_extinctionThreshold_lt {T W t : ℝ} (hT : 0 ≤ T)
    (hW : 0 ≤ W) (hTt : T ≤ t) :
    widthComparisonBound T W t < 0 ↔
      extinctionThreshold (4 * T + 1) (4 * W) < 4 * (t - T) := by
  have hd : 0 < 4 * t + 1 := by linarith
  have hc : 0 < 4 * T + 1 := by linarith
  have hC : 0 ≤ 4 * W := by linarith
  have hH : 0 ≤ 4 * (t - T) := by linarith
  have hsum : 4 * (t - T) + (4 * T + 1) = 4 * t + 1 := by ring
  set A := (4 * t + 1) ^ (3 / 4 : ℝ) with hA
  set B := (4 * t + 1) ^ (1 / 4 : ℝ) with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos hd _
  set X := W * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ + 2 * Real.pi * (4 * T + 1) ^ (1 / 4 : ℝ) -
    2 * Real.pi * B with hX
  have hsplit : (4 * W) / (4 * T + 1) ^ (3 / 4 : ℝ) =
      4 * (W * ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹) := by
    rw [div_eq_mul_inv]
    ring
  have hright : (4 * W) / (4 * T + 1) ^ (3 / 4 : ℝ) -
      8 * Real.pi * (B - (4 * T + 1) ^ (1 / 4 : ℝ)) = 4 * X := by
    rw [hsplit, hX]
    ring
  have hleft : A * X < 0 ↔ X < 0 := by
    constructor
    · intro h
      by_contra hx
      have := mul_nonneg hApos.le (le_of_not_gt hx)
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hApos h
  have hright' : 4 * X < 0 ↔ X < 0 := by
    constructor
    · intro h
      by_contra hx
      have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_of_not_gt hx)
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg (by norm_num) h
  rw [show widthComparisonBound T W t = A * X from by
    rw [widthComparisonBound_factor hT (by linarith), hA, hX, hB]]
  rw [extinctionThreshold_lt_iff hc hC hH, hsum, hright, hleft, hright']

theorem le_of_le_widthComparisonBound {T W₁ W t : ℝ} (hT : 0 ≤ T) (hW₁ : 0 ≤ W₁)
    (hTt : T ≤ t) (h0 : 0 ≤ W) (hle : W ≤ widthComparisonBound T W₁ t) :
    t ≤ T + extinctionThreshold (4 * T + 1) (4 * W₁) / 4 := by
  by_contra hcon
  have hlt : extinctionThreshold (4 * T + 1) (4 * W₁) < 4 * (t - T) := by linarith
  have := (widthComparisonBound_neg_iff_extinctionThreshold_lt hT hW₁ hTt).mpr hlt
  linarith

def widthNormalized (T : ℝ) (W : ℝ → ℝ) (z : ℝ) : ℝ :=
  W z * (4 * z + 1) ^ (-(3 / 4) : ℝ) +
    2 * Real.pi * ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * T + 1) ^ (1 / 4 : ℝ))

theorem widthNormalized_self (T : ℝ) (W : ℝ → ℝ) :
    widthNormalized T W T = W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) := by
  rw [widthNormalized]
  ring

def HasNonincreasingWidthNormalizationOn (T t : ℝ) (W : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ico T t, ∀ r, 0 < r →
    ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ *
      (widthNormalized T W z - widthNormalized T W x) < r

theorem continuousOn_widthNormalized {T t : ℝ} (hT : 0 ≤ T) {W : ℝ → ℝ}
    (hcont : ContinuousOn W (Icc T t)) :
    ContinuousOn (widthNormalized T W) (Icc T t) := by
  have hpos : ∀ z ∈ Icc T t, (0 : ℝ) < 4 * z + 1 := by
    intro z hz
    have := hz.1
    linarith
  have hlin : ContinuousOn (fun z : ℝ => 4 * z + 1) (Icc T t) := by fun_prop
  have h34 : ContinuousOn (fun z : ℝ => (4 * z + 1) ^ (-(3 / 4) : ℝ)) (Icc T t) :=
    hlin.rpow_const fun z hz => Or.inl (hpos z hz).ne'
  have h14 : ContinuousOn (fun z : ℝ => (4 * z + 1) ^ (1 / 4 : ℝ)) (Icc T t) :=
    hlin.rpow_const fun z hz => Or.inr (by norm_num)
  have hc14 : ContinuousOn (fun _ : ℝ => (4 * T + 1) ^ (1 / 4 : ℝ)) (Icc T t) :=
    continuousOn_const
  have hG : ContinuousOn (fun z : ℝ => 2 * Real.pi *
      ((4 * z + 1) ^ (1 / 4 : ℝ) - (4 * T + 1) ^ (1 / 4 : ℝ))) (Icc T t) :=
    continuousOn_const.mul (h14.sub hc14)
  unfold widthNormalized
  exact (hcont.mul h34).add hG

theorem le_widthComparisonBound_of_nonincreasing_normalization {T t : ℝ} {W : ℝ → ℝ}
    (hT : 0 ≤ T) (hTt : T ≤ t) (hcont : ContinuousOn W (Icc T t))
    (h : HasNonincreasingWidthNormalizationOn T t W) :
    W t ≤ widthComparisonBound T (W T) t := by
  have hconty := continuousOn_widthNormalized hT hcont
  have hgrön : widthNormalized T W t ≤ widthNormalized T W T := by
    have hmain := le_gronwallBound_of_liminf_deriv_right_le (f := widthNormalized T W)
      (f' := fun _ : ℝ => 0) (δ := widthNormalized T W T) (K := 0) (ε := 0)
      (a := T) (b := t) hconty
      (fun x hx r hr => h x hx r hr) le_rfl (fun x hx => by simp)
    have ht := hmain t ⟨hTt, le_rfl⟩
    simpa only [gronwallBound_K0, zero_mul, add_zero] using ht
  have hdT : (0 : ℝ) < 4 * t + 1 := by linarith
  have hdt : (0 : ℝ) < (4 * t + 1) ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hdT _
  have hkey : W t * (4 * t + 1) ^ (-(3 / 4) : ℝ) ≤
      W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) +
        2 * Real.pi * ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ)) := by
    have := hgrön
    rw [widthNormalized, widthNormalized_self T W] at this
    linarith
  have hident : (W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) +
      2 * Real.pi * ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ))) /
        (4 * t + 1) ^ (-(3 / 4) : ℝ) = widthComparisonBound T (W T) t := by
    have hcT : (0 : ℝ) < 4 * T + 1 := by linarith
    have hDT : (4 * T + 1) ^ (-(3 / 4) : ℝ) = ((4 * T + 1) ^ (3 / 4 : ℝ))⁻¹ :=
      Real.rpow_neg hcT.le _
    have hDt : (4 * t + 1) ^ (-(3 / 4) : ℝ) = ((4 * t + 1) ^ (3 / 4 : ℝ))⁻¹ :=
      Real.rpow_neg hdT.le _
    have hprod : (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) = 4 * t + 1 := by
      rw [← Real.rpow_add hdT]
      norm_num
    have h1 : (4 * T + 1) ^ (-(3 / 4) : ℝ) / (4 * t + 1) ^ (-(3 / 4) : ℝ) =
        ((4 * t + 1) / (4 * T + 1)) ^ (3 / 4 : ℝ) := by
      rw [hDT, hDt, Real.div_rpow hdT.le hcT.le (3 / 4 : ℝ)]
      field_simp
    have h2 : ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ)) /
        (4 * t + 1) ^ (-(3 / 4) : ℝ) =
        (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) := by
      have key : ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ)) /
          ((4 * t + 1) ^ (3 / 4 : ℝ))⁻¹ =
          (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * T + 1) ^ (1 / 4 : ℝ) -
            (4 * t + 1) ^ (3 / 4 : ℝ) * (4 * t + 1) ^ (1 / 4 : ℝ) := by
        field_simp
      rw [hDt, key, hprod]
    rw [add_div, mul_div_assoc, mul_div_assoc, h1, h2, widthComparisonBound]
    ring
  calc W t ≤ (W T * (4 * T + 1) ^ (-(3 / 4) : ℝ) +
        2 * Real.pi * ((4 * T + 1) ^ (1 / 4 : ℝ) - (4 * t + 1) ^ (1 / 4 : ℝ))) /
          (4 * t + 1) ^ (-(3 / 4) : ℝ) := (le_div_iff₀ hdt).mpr hkey
    _ = widthComparisonBound T (W T) t := hident


end DifferentialGeometry.PDE.RicciFlow.Extinction.Families


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem widthComparisonBound_comp {a b c A : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    widthComparisonBound b (widthComparisonBound a A b) c =
      widthComparisonBound a A c := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have Bpos : 0 < (4 * b + 1) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  rw [widthComparisonBound_factor hb hc, widthComparisonBound_factor ha hb,
    widthComparisonBound_factor ha hc]
  have cancel (x : ℝ) : (4 * b + 1) ^ (3 / 4 : ℝ) * x *
      ((4 * b + 1) ^ (3 / 4 : ℝ))⁻¹ = x := by
    rw [mul_right_comm, mul_inv_cancel₀ Bpos.ne', one_mul]
  rw [cancel]
  ring

/-- A nonnegative width surviving a finite sequence of regular intervals and
downward jumps cannot survive beyond the scalar extinction threshold. -/
theorem finiteWidthTrace_time_le_extinctionThreshold
    {n : ℕ} {time : ℕ → ℝ} {width : ℕ → ℝ → ℝ}
    (hstart : 0 ≤ time 0) (htime : Monotone time)
    (hcont : ∀ i < n, ContinuousOn (width i) (Set.Icc (time i) (time (i + 1))))
    (hslope : ∀ i < n, HasNonincreasingWidthNormalizationOn
      (time i) (time (i + 1)) (width i))
    (hjump : ∀ i < n, width (i + 1) (time (i + 1)) ≤ width i (time (i + 1)))
    (hinit : 0 ≤ width 0 (time 0)) (hfinal : 0 ≤ width n (time n)) :
    time n ≤ time 0 + extinctionThreshold (4 * time 0 + 1) (4 * width 0 (time 0)) / 4 := by
  have tople : ∀ i ≤ n, width i (time i) ≤ widthComparisonBound (time 0) (width 0 (time 0)) (time i) := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [widthComparisonBound_self hstart]
    | succ i ih =>
        intro hi
        have hi' : i < n := by omega
        have h0i := htime (Nat.zero_le i)
        have hnext := htime (Nat.le_succ i)
        have hnneg := hstart.trans h0i
        calc
          width (i + 1) (time (i + 1)) ≤ width i (time (i + 1)) := hjump i hi'
          _ ≤ widthComparisonBound (time i) (width i (time i)) (time (i + 1)) :=
            le_widthComparisonBound_of_nonincreasing_normalization
              hnneg hnext (hcont i hi') (hslope i hi')
          _ ≤ widthComparisonBound (time i)
              (widthComparisonBound (time 0) (width 0 (time 0)) (time i)) (time (i + 1)) :=
            widthComparisonBound_mono_width hnneg hnext (ih hi'.le)
          _ = widthComparisonBound (time 0) (width 0 (time 0)) (time (i + 1)) :=
            widthComparisonBound_comp hstart h0i hnext
  exact le_of_le_widthComparisonBound hstart hinit (htime (Nat.zero_le n)) hfinal (tople n le_rfl)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families


end

/-
DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

The files under DifferentialGeometry/External/Schoenflies derive from
https://github.com/alonamaloh/schoenflies-lean
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License 2.0.
See that directory's LICENSE, MODIFICATIONS.md and provenance records.

The selected source under DifferentialGeometry/External/TauCeti derives from
https://github.com/TauCetiProject/TauCeti
revision 3358033ba2fd35f321356dceaf2372a0fd6c0bfd.
Copyright (c) 2026 Joseph Tooby-Smith and The Tau Ceti contributors.
Authors include Joseph Tooby-Smith, Codex and The Tau Ceti contributors,
as recorded in the preserved original source headers.
Released under the Apache License 2.0.
See that directory's LICENSE, SOURCE_MAP.json and MODIFICATIONS.md.
Native Sard, Morse, embedding and extension modules consume this external API.

The source under DifferentialGeometry/External/CanonicalTopology is restored
from the canonical-topology/Poincare project by Ayush Khaitan and its
contributors. See its pinned source archives, SOURCE_MAP.json, LICENSE
and MODIFICATIONS.md for exact revisions and declaration-level adaptations.
The derivative homotopy includes adapted source from plby/HopfProblem,
Solution.lean at 9ac8a456b526527837d7082ff775213ca8bc9809, lines 62156–62228,
under Apache-2.0; the nested attribution and license are preserved.

The source under DifferentialGeometry/External/ClassificationOfSurfaces
derives from https://github.com/mccorvie/classification-of-surfaces.
It includes work by the ClassificationOfSurfaces contributors, Steven Sivek
and Kai Lam, as recorded in the original source and nested provenance.
Released under the Apache License 2.0. See its LICENSE and MODIFICATIONS.md.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

open Filter Set
open scoped Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2.H1 := by
  dsimp only [OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2.H1]
  intro n t w h0 hm hc hs hj hinit hf
  have hnorm : ∀ i < n, HasNonincreasingWidthNormalizationOn (t i) (t (i + 1)) (w i) := by
    intro i hi x hx r hr
    refine (hs i hi x hx r hr).mono fun y hy => ?_
    have hcancel :
        widthNormalized (t i) (w i) y - widthNormalized (t i) (w i) x =
          (w i y * (4 * y + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * y + 1) ^ (1 / 4 : ℝ)) -
          (w i x * (4 * x + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * x + 1) ^ (1 / 4 : ℝ)) := by
      unfold widthNormalized
      ring
    rw [hcancel]
    exact hy
  have hbound := finiteWidthTrace_time_le_extinctionThreshold (time := t) (width := w) (le_of_eq h0.symm)
      hm hc hnorm hj (by simpa only [h0] using hinit) hf
  rw [h0] at hbound
  simp only [DifferentialGeometry.PDE.RicciFlow.Extinction.Families.extinctionThreshold,
    mul_zero, zero_add, Real.one_rpow, mul_one] at hbound
  have hratio : 4 * w 0 0 / (8 * Real.pi) = w 0 0 / (2 * Real.pi) := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  rwa [hratio] at hbound
