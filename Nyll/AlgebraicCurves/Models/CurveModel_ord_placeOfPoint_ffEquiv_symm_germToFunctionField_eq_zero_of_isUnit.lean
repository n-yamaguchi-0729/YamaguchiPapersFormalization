/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Places.Place_mem_iff_ord_nonneg

/-!
# Curve Model ord place Of Point ff Equiv symm germ To Function Field eq zero of is Unit
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit

open CategoryTheory AlgebraicGeometry AlgebraicCurve

end CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve.CurveModel



open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit in
open CategoryTheory AlgebraicGeometry AlgebraicCurve in
theorem ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (Mc : AlgebraicCurve.CurveModel K L)
    (U : Mc.C.Opens) (P : closedPoints Mc.C) (hP : P.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(Mc.C, U)) (hs : IsUnit s) :
    (Mc.placeOfPoint P).ord (Mc.ffEquiv.symm (Mc.C.germToFunctionField U s)) = 0 := by
  let φ : Mc.C.presheaf.stalk P.1 →+* L :=
    (Mc.ffEquiv.symm : Mc.C.functionField ≃+* L).toRingHom.comp (algebraMap (Mc.C.presheaf.stalk
      P.1) Mc.C.functionField)
  have hrange : φ.range = (Mc.placeOfPoint P).toValuationSubring.toSubring := Mc.range_stalk_eq P
  let g : Mc.C.presheaf.stalk P.1 := Mc.C.presheaf.germ U P.1 hP s
  have hg : IsUnit g := hs.map _
  have hgerm : Mc.C.germToFunctionField U s = algebraMap (Mc.C.presheaf.stalk P.1)
    Mc.C.functionField g := by
    change algebraMap Γ(Mc.C, U) Mc.C.functionField s = _
    exact IsScalarTower.algebraMap_apply Γ(Mc.C, U) (Mc.C.presheaf.stalk ((⟨P.1, hP⟩ : U) : Mc.C))
      Mc.C.functionField s
  have hx : Mc.ffEquiv.symm (Mc.C.germToFunctionField U s) = φ g := by
    rw [hgerm]
    rfl
  rw [hx]
  have hmem : ∀ t : Mc.C.presheaf.stalk P.1, φ t ∈ (Mc.placeOfPoint P).toValuationSubring := fun t
    => by
    have ht : φ t ∈ φ.range := ⟨t, rfl⟩
    rw [hrange] at ht
    exact ht
  have hinv : φ g * φ ((hg.unit⁻¹ : (Mc.C.presheaf.stalk P.1)ˣ) : Mc.C.presheaf.stalk P.1) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hne : φ g ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have h1 : 0 ≤ (Mc.placeOfPoint P).ord (φ g) :=
    ((Mc.placeOfPoint P).mem_iff_ord_nonneg hne).mp (hmem g)
  have hinv' : (φ g)⁻¹ = φ ((hg.unit⁻¹ : (Mc.C.presheaf.stalk P.1)ˣ) : Mc.C.presheaf.stalk P.1) :=
    (eq_inv_of_mul_eq_one_right hinv).symm ▸ rfl
  have h2 : 0 ≤ (Mc.placeOfPoint P).ord (φ g)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((Mc.placeOfPoint P).mem_iff_ord_nonneg (fun h0 => by
      rw [← inv_eq_of_mul_eq_one_right hinv] at h0
      exact (inv_ne_zero hne) h0)).mp (hmem _)
  rw [AlgebraicCurve.Place.ord_inv] at h2
  omega
end AlgebraicCurve.CurveModel
end ProofImplementation
