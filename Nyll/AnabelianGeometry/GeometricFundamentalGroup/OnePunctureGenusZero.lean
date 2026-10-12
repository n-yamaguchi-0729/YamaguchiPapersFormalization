/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroPunctured
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.AffineLineFundamentalGroup
import Nyll.AlgebraicCurves.Cohomology.Finite_H0_H1_structureSheaf_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over

/-!
# The genus-zero one-puncture case from coherent cohomology

The input genus is the dimension of the actual structure-sheaf H¹. We construct the curve model,
transport the specified closed point and its open complement, and obtain an actual affine-line
isomorphism. This proves the fundamental-group structure for the general case `(g,r) = (0,1)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A smooth proper integral curve of coherent genus zero, minus any one closed point, is the
affine line over an algebraically closed field of characteristic zero. -/
theorem nonempty_affineLine_iso_of_finrank_H1_eq_zero_complement
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (X : Scheme.{0}) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.structureSheafSections c).H1 = 0)
    (x : closedPoints X) (U : X.Opens) (hU : (U : Set X) = {x.1}ᶜ) :
    Nonempty (U.toScheme ≅ Spec (.of K[X])) := by
  let fieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  have comparison : Module.finrank K (𝒱.structureSheafSections c).H1 =
      genusFF K X.functionField := (finite_H0_H1_structureSheaf_of_isAlgClosed 𝒱 c).2.2.2
  have genusZero : genusFF K X.functionField = 0 := comparison.symm.trans hg
  obtain ⟨fieldCurve, fieldFiniteType, M, i, _, _⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K X c
  let y : closedPoints M.C := ⟨i.inv.base x.1, by
    change IsClosed ({i.inv.base x.1} : Set M.C)
    rw [← Set.image_singleton]
    exact (Scheme.homeoOfIso i.symm).isClosedMap _ x.2⟩
  let V : M.C.Opens := i.hom ⁻¹ᵁ U
  have hV : (V : Set M.C) = {y.1}ᶜ := by
    apply Set.ext
    intro z
    change i.hom.base z ∈ (U : Set X) ↔ z ∉ {y.1}
    rw [hU, Set.mem_compl_singleton_iff, Set.mem_singleton_iff]
    apply not_congr
    constructor
    · intro heq
      exact (Scheme.homeoOfIso i).injective
        (heq.trans ((Scheme.homeoOfIso i).apply_symm_apply x.1).symm)
    · intro heq
      rw [heq]
      exact (Scheme.homeoOfIso i).apply_symm_apply x.1
  obtain ⟨j⟩ := nonempty_affineLine_iso_of_genus_zero_complement M genusZero y V hV
  exact ⟨(i.hom.preimageIso U).symm ≪≫ j⟩

/-- For `(g,r) = (0,1)` in characteristic zero, the actual étale fundamental group is trivial.
The genus uses coherent H¹; the single puncture is the actual complement of the given open. -/
theorem subsingleton_fundamentalGroup_of_finrank_H1_eq_zero_complement
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (X : Scheme.{0}) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.structureSheafSections c).H1 = 0)
    (x : closedPoints X) (U : X.Opens) (hU : (U : Set X) = {x.1}ᶜ)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.toScheme) :
    Subsingleton π₁ᵉᵗ(ξ) := by
  obtain ⟨i⟩ := nonempty_affineLine_iso_of_finrank_H1_eq_zero_complement X c 𝒱 hg x U hU
  have connected : ConnectedSpace U.toScheme :=
    (Scheme.homeoOfIso i).connectedSpace_iff.mpr inferInstance
  let E : FiniteEtale (Spec (.of K[X])) ≌ FiniteEtale U.toScheme :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i.symm
  have pullbackEquivalence : (pullback i.hom).IsEquivalence := E.isEquivalence_functor
  let eπ : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ i.hom) :=
    fundamentalGroupEquivOfPullbackEquivalence i.hom ξ
  have singleton : Subsingleton π₁ᵉᵗ(ξ ≫ i.hom) :=
    subsingleton_fundamentalGroup_affineLine (ξ ≫ i.hom)
  exact ⟨fun σ τ => eπ.injective (Subsingleton.elim (eπ σ) (eπ τ))⟩

end AnabelianGeometry.GeometricFundamentalGroup
