/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_twoAffineOpenCover_of_section
import Nyll.AlgebraicCurves.Geometry.Nonempty_algEquiv_functionField_of_iso
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusFF_eq_of_algEquiv
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Algebra.Algebra.Tower

/-!
# Geometric genus after a finite field extension

A finite extension embeds in an algebraic closure of the original field. Actual
Cech cohomology and the function-field isomorphism of the two iterated pullbacks
then compare the genera. The auxiliary rational point is only used to construct
a two-affine cover of the extended curve.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open NeronModelInfra
open scoped TensorProduct

namespace AlgebraicGeometry.SmoothProperCurve

private theorem finrank_H1_eq_genusFF_baseChange
    (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (𝒱 : C.TwoAffineOpenCover) (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    let := (AlgebraicCurve.baseToFunctionField (baseChange K c Ω)).toAlgebra
    Module.finrank K (𝒱.structureSheafSections c).H1 =
      AlgebraicCurve.genusFF Ω (pullback c (specMap K Ω)).functionField := by
  intro a
  let d := (𝒱.structureSheafSections c).cechDiff
  have hex : Function.Exact d (LinearMap.range d).mkQ :=
    LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ :=
    Submodule.mkQ_surjective (LinearMap.range d)
  have hexΩ : Function.Exact (d.baseChange Ω)
      ((LinearMap.range d).mkQ.baseChange Ω) := by
    have ht := lTensor_exact Ω hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at ht
  let e := hexΩ.linearEquivOfSurjective (LinearMap.baseChange_surjective Ω hsurj)
  calc
    Module.finrank K (𝒱.structureSheafSections c).H1 =
        Module.finrank Ω (Ω ⊗[K] (𝒱.structureSheafSections c).H1) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank Ω ((Ω ⊗[K] (𝒱.cover c).A01) ⧸
        LinearMap.range (d.baseChange Ω)) := e.finrank_eq.symm
    _ = AlgebraicCurve.genusFF Ω (pullback c (specMap K Ω)).functionField :=
      (𝒱.finrank_cechDiff_baseChange_of_isAlgClosed c Ω).2.2

/-- A finite extension with a point does not change the point-independent genus.
No separability assumption is needed. -/
theorem geometricGenus_baseChange_of_finite_of_section
    (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K c L)) :
    geometricGenus L (baseChange K c L) = geometricGenus K c := by
  let Ω := AlgebraicClosure K
  let i : L →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra L Ω := i.toRingHom.toAlgebra
  have : IsScalarTower K L Ω := IsScalarTower.of_algHom i
  obtain ⟨𝒱, -, -⟩ := exists_twoAffineOpenCover_of_section L (baseChange K c L) ε
  have hs : specMap L Ω ≫ specMap K L = specMap K Ω := by
    rw [specMap, specMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq K L Ω).symm
  let e : pullback (baseChange K c L) (specMap L Ω) ≅
      pullback c (specMap K Ω) :=
    pullbackLeftPullbackSndIso c (specMap K L) (specMap L Ω) ≪≫
      pullback.congrHom rfl hs
  have he : e.hom ≫ baseChange K c Ω = baseChange L (baseChange K c L) Ω := by
    simp only [e, Iso.trans_hom, Category.assoc, baseChange, pullback.congrHom_hom,
      pullback.map, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  let a₁ := (AlgebraicCurve.baseToFunctionField (baseChange L (baseChange K c L) Ω)).toAlgebra
  let a₂ := (AlgebraicCurve.baseToFunctionField (baseChange K c Ω)).toAlgebra
  obtain ⟨φ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
    (baseChange L (baseChange K c L) Ω) (baseChange K c Ω) e he
  calc
    geometricGenus L (baseChange K c L) =
        Module.finrank L (𝒱.structureSheafSections (baseChange K c L)).H1 :=
      (finrank_H1_eq_geometricGenus L (baseChange K c L) 𝒱).symm
    _ = AlgebraicCurve.genusFF Ω
        (pullback (baseChange K c L) (specMap L Ω)).functionField :=
      finrank_H1_eq_genusFF_baseChange L (baseChange K c L) 𝒱 Ω
    _ = geometricGenus K c := AlgebraicCurve.genusFF_eq_of_algEquiv φ

end AlgebraicGeometry.SmoothProperCurve
