/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_ord_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Taylor
import AlgebraicCurves.Places.EvaluationAlgebra
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Places.Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
import AlgebraicCurves.Places.Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord

/-!
# Place taylor Coeff ord ne zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_ord_ne_zero

open AlgebraicCurve AlgebraicCurve.Place

namespace ProofAuxJetT2
open AlgebraicCurve AlgebraicCurve.Place IsLocalRing
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {g : F} (hg0 : g ≠ 0) (hpos : 0 < v.ord g) :
    v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hg0 hpos.le
  have hnu : ¬ IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    change v.ord g = 0 at this
    omega
  have hres : residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    (residue_eq_zero_iff _).mpr (by simpa [mem_nonunits_iff] using hnu)
  rw [v.evalAt_of_mem hmem, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem ord_mul_inv_pow (v : Place K F) {t f : F} (ht0 : t ≠ 0) (hf0 : f ≠ 0) (ht : v.ord t = 1)
    (q : ℕ) : v.ord (f * t⁻¹ ^ q) = v.ord f - q := by
  have hq0 : t⁻¹ ^ q ≠ 0 := pow_ne_zero _ (inv_ne_zero ht0)
  rw [v.ord_mul hf0 hq0, ← zpow_natCast, v.ord_zpow, v.ord_inv, ht]
  ring

end ProofAuxJetT2

open ProofAuxJetT2 in
theorem _root_.AlgebraicCurve.Place.taylorCoeff_ord_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    taylorCoeff v t (v.ord f).toNat f ≠ 0 := by
  have ht0 : t ≠ 0 := by rintro rfl; simp [Place.ord_zero] at ht
  have hford : 0 ≤ v.ord f :=
    ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0
  have hlow : ∀ q, q < (v.ord f).toNat → taylorCoeff v t q f = 0 :=
    (forall_lt_taylorCoeff_eq_zero_iff_le_ord v hv ht hf hf0 _).mpr
      (by rw [Int.toNat_of_nonneg hford])
  rw [taylorCoeff_eq, taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f hlow]
  apply v.evalAt_ne_zero_of_ord_eq_zero hv (mul_ne_zero hf0 (pow_ne_zero _ (inv_ne_zero ht0)))
  rw [ord_mul_inv_pow v ht0 hf0 ht, Int.toNat_of_nonneg hford, sub_self]
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_ord_ne_zero
end ProofImplementation
