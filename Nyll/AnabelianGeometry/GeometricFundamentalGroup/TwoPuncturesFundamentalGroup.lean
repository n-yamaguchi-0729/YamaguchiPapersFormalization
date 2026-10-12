/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.TwoPuncturesGenusZero
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentProfiniteIntegers
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over
import Nyll.ProCGroups.Completion.ProCInteger
import Nyll.ProCGroups.Generation.Basic

/-!
# The fundamental group of a genus-zero curve with two punctures

Genus is measured by the dimension of actual coherent H¹. The constructed Laurent-chart
isomorphism and the actual finite-etale pullback equivalence transport the full profinite
integer comparison to the original open curve and its given geometric point.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

open ProCGroups ProCGroups.Completion

/-- The actual etale fundamental group of a smooth proper genus-zero curve minus two distinct
closed points is topologically isomorphic to the full profinite integers in characteristic
zero. No rational model, affine coordinates, or comparison morphism is part of the input. -/
theorem exists_fundamentalGroup_profiniteInteger_equiv_of_finrank_H1_eq_zero_complement_pair
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (X : Scheme.{0}) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.structureSheafSections c).H1 = 0)
    (x y : closedPoints X) (hne : x ≠ y)
    (U : X.Opens) (hU : (U : Set X) = {x.1, y.1}ᶜ)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.toScheme) :
    ∃ (g : π₁ᵉᵗ(ξ))
      (e : π₁ᵉᵗ(ξ) ≃ₜ* Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))),
      Generation.TopologicallyGenerates ({g} : Set π₁ᵉᵗ(ξ)) ∧
      e g = proCIntegerOne (C := FiniteGroupClass.allFinite) := by
  obtain ⟨i⟩ := nonempty_laurent_iso_of_finrank_H1_eq_zero_complement_pair
    X c 𝒱 hg x y hne U hU
  have connected : ConnectedSpace U.toScheme :=
    (Scheme.homeoOfIso i).connectedSpace_iff.mpr inferInstance
  let E : FiniteEtale (Spec (.of (LaurentPolynomial K))) ≌ FiniteEtale U.toScheme :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i.symm
  have pullbackEquivalence : (pullback i.hom).IsEquivalence := E.isEquivalence_functor
  let eπ : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ i.hom) :=
    fundamentalGroupEquivOfPullbackEquivalence i.hom ξ
  obtain ⟨g, e, hgen, he⟩ :=
    exists_fundamentalGroup_laurent_profiniteInteger_equiv (ξ ≫ i.hom)
  refine ⟨eπ.symm g, eπ.trans e, ?_, ?_⟩
  · have h := Generation.topologicallyGenerates_continuousMulEquiv_image eπ.symm hgen
    rw [Set.image_singleton] at h
    exact h
  · change e (eπ (eπ.symm g)) = proCIntegerOne (C := FiniteGroupClass.allFinite)
    rw [eπ.apply_symm_apply]
    exact he

end AnabelianGeometry.GeometricFundamentalGroup
