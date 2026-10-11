/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorCoeff_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Taylor
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Places.Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one

/-!
# Place taylor Coeff algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorCoeff_algebraMap

open AlgebraicCurve AlgebraicCurve.Place Polynomial

namespace ProofAuxG2
open AlgebraicCurve AlgebraicCurve.Place Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem taylorRem_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorRem v t 0 r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [taylorRem_succ, ih, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq, map_zero,
      sub_self, zero_mul]

theorem taylorCoeff_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorCoeff v t r 0 = 0 := by
  rw [taylorCoeff_eq, taylorRem_zero_fun, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]

theorem taylorRem_algebraMap_one (v : Place K F) (t : F) (c : K) :
    taylorRem v t (algebraMap K F c) 1 = 0 := by
  change (taylorRem v t (algebraMap K F c) 0 - _) * t⁻¹ = 0
  rw [taylorRem_zero, v.evalAt_algebraMap_eq, sub_self, zero_mul]

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {g : F} (hg0 : g ≠ 0) (hpos : 0 < v.ord g) :
    v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hg0 hpos.le
  have hnu : ¬ IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    change v.ord g = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by simpa [mem_nonunits_iff] using hnu)
  rw [v.evalAt_of_mem hmem, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end ProofAuxG2

open ProofAuxG2 in
theorem _root_.AlgebraicCurve.Place.taylorCoeff_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t : F) (c : K) (n : ℕ) :
    taylorCoeff v t n (algebraMap K F c) = if n = 0 then c else 0 := by
  rcases n with _ | n
  · rw [ite_eq_left rfl, taylorCoeff_zero, v.evalAt_algebraMap_eq]
  · rw [ite_eq_right (Nat.succ_ne_zero n), taylorCoeff_succ_eq_taylorCoeff_taylorRem_one,
      taylorRem_algebraMap_one, taylorCoeff_zero_fun]
end AlgebraicCurves.Places.Proofs.Place_taylorCoeff_algebraMap
end ProofImplementation
