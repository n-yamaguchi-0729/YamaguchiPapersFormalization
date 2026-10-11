/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_essFiniteType_functionField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic

/-!
# EssFiniteType functionField

The function field of an integral scheme locally of finite type over a field is essentially of
finite type over that field.
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.EssFiniteType_functionField

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem _root_.AlgebraicCurve.essFiniteType_functionField
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [LocallyOfFiniteType c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField := by
  let algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have e : V ≤ c ⁻¹ᵁ ⊤ := le_top
  let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hft : ((c.appLE ⊤ V e).hom.comp eK.symm.toRingHom).FiniteType :=
    (c.finiteType_appLE (isAffineOpen_top _) hV e).comp
      (RingHom.FiniteType.of_surjective _ eK.symm.surjective)
  let algKA : Algebra K Γ(C, V) := ((c.appLE ⊤ V e).hom.comp eK.symm.toRingHom).toAlgebra
  have : Algebra.FiniteType K Γ(C, V) := hft
  have : IsFractionRing Γ(C, V) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C V hV
  have : IsScalarTower K Γ(C, V) C.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change baseToFunctionField c k =
      (C.germToFunctionField V).hom ((c.appLE ⊤ V e).hom (eK.symm k))
    simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE,
      Scheme.germToFunctionField, CommRingCat.hom_comp]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  have : Algebra.EssFiniteType Γ(C, V) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization C.functionField (nonZeroDivisors Γ(C, V))
  exact Algebra.EssFiniteType.comp K Γ(C, V) C.functionField
end AlgebraicCurves.FunctionFields.Proofs.EssFiniteType_functionField
end ProofImplementation
