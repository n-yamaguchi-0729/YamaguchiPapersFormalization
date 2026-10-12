/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroFundamentalGroup
import Nyll.AlgebraicCurves.Cohomology.Finite_H0_H1_structureSheaf_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over

/-!
# The proper genus-zero case from structure-sheaf cohomology

The genus is the dimension of the actual structure-sheaf H¹ on a two-affine cover.
Its proved comparison with function-field cohomology, followed by the actual curve-model
construction and pullback equivalence, proves triviality of the original étale fundamental group.
No presentation theorem, rational coordinate, or comparison assumption is used.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A smooth proper integral genus-zero curve over an algebraically closed field of
characteristic zero has trivial étale fundamental group. The genus is computed from the actual
structure sheaf on a two-affine cover, and the geometric point is arbitrary. -/
theorem subsingleton_fundamentalGroup_of_finrank_H1_eq_zero
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (X : Scheme.{0}) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.structureSheafSections c).H1 = 0)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    Subsingleton π₁ᵉᵗ(ξ) := by
  let fieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  have comparison : Module.finrank K (𝒱.structureSheafSections c).H1 =
      genusFF K X.functionField := (finite_H0_H1_structureSheaf_of_isAlgClosed 𝒱 c).2.2.2
  have genusZero : genusFF K X.functionField = 0 := comparison.symm.trans hg
  obtain ⟨fieldCurve, fieldFiniteType, M, i, _, _⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K X c
  let E : FiniteEtale M.C ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i
  have pullbackEquivalence : (pullback i.inv).IsEquivalence := E.isEquivalence_functor
  let eπ : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ i.inv) :=
    fundamentalGroupEquivOfPullbackEquivalence i.inv ξ
  have singleton : Subsingleton π₁ᵉᵗ(ξ ≫ i.inv) :=
    subsingleton_fundamentalGroup_of_genus_zero M genusZero (ξ ≫ i.inv)
  exact ⟨fun σ τ => eπ.injective (Subsingleton.elim (eπ σ) (eπ τ))⟩

end AnabelianGeometry.GeometricFundamentalGroup
