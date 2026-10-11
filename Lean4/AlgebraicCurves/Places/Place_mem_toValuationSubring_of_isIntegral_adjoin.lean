/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import Mathlib.RingTheory.Valuation.Integral

/-!
# Place mem to Valuation Subring of is Integral adjoin
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_mem_toValuationSubring_of_isIntegral_adjoin

open AlgebraicCurve

namespace ModularCurve

namespace QexpN

private def placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    Subalgebra K F :=
  { v.toValuationSubring.toSubring.toSubsemiring with algebraMap_mem' := v.algebraMap_mem' }

private theorem mem_placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {y : F} :
    y ∈ placeSubalgebra v ↔ y ∈ v.toValuationSubring := Iff.rfl

private theorem valuationSubring_integers {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) :
    (v.toValuationSubring.valuation).Integers v.toValuationSubring :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun a => v.toValuationSubring.valuation_le_one a
    exists_of_le_one := fun {r} hr =>
      ⟨⟨r, v.toValuationSubring.mem_of_valuation_le_one r hr⟩, rfl⟩ }

private theorem mem_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by
  have hle : Algebra.adjoin K {j} ≤ placeSubalgebra v :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_placeSubalgebra v).mpr hj))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(v.toValuationSubring) :=
    { toFun := fun a => ⟨(a : F), (mem_placeSubalgebra v).mp (hle a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hOx : IsIntegral (↥v.toValuationSubring) x :=
    IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
  exact v.toValuationSubring.mem_of_valuation_le_one x
    ((valuationSubring_integers v).isIntegral_iff_v_le_one.mp hOx)

end QexpN

end ModularCurve

theorem _root_.AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin {K F : Type*}
  [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx
  : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring :=
  ModularCurve.QexpN.mem_of_isIntegral_adjoin v hj hx
end AlgebraicCurves.Places.Proofs.Place_mem_toValuationSubring_of_isIntegral_adjoin
end ProofImplementation
