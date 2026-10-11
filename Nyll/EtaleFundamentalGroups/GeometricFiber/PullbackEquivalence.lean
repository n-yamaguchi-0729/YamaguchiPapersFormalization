/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.Injectivity
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Fundamental groups under an equivalence of finite étale covers

An equivalence on finite étale covers makes the canonical map on fundamental
groups bijective. Its inverse is continuous because these automorphism
groups are compact Hausdorff. This gives the fundamental-group conclusion
of Stacks Project, Tag `0BQA`, for connected schemes.
-/

section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- An equivalence on finite étale covers makes the induced group map bijective. -/
theorem fundamentalGroupHom_bijective_of_pullback_isEquivalence
    (f : X ⟶ Y) [(pullback f).IsEquivalence] (ξ : Spec (.of Ω) ⟶ X) :
    Function.Bijective (fundamentalGroupHom f ξ) := by
  refine ⟨fundamentalGroupHom_injective_of_pullback_essSurj f ξ, ?_⟩
  have hff : Nonempty (pullback f).FullyFaithful :=
    ⟨Functor.FullyFaithful.ofFullyFaithful (pullback f)⟩
  exact ((autHomOfCompIso_surjective_tfae
    (fiber (ξ ≫ f)) (fiber ξ) (pullback f) (pullbackFiberIso f ξ)).out 1 2).mpr
      hff

/-- The canonical map on fundamental groups is an isomorphism of topological
groups whenever pullback is an equivalence on finite étale covers. -/
@[stacks 0BQA "The fundamental-group conclusion for connected schemes."]
def fundamentalGroupEquivOfPullbackEquivalence
    (f : X ⟶ Y) [(pullback f).IsEquivalence] (ξ : Spec (.of Ω) ⟶ X) :
    π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ f) where
  toMulEquiv := MulEquiv.ofBijective (fundamentalGroupHom f ξ)
    (fundamentalGroupHom_bijective_of_pullback_isEquivalence f ξ)
  continuous_toFun := (fundamentalGroupHom f ξ).continuous_toFun
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective (fundamentalGroupHom f ξ)
        (fundamentalGroupHom_bijective_of_pullback_isEquivalence f ξ)).toEquiv)
      (fundamentalGroupHom f ξ).continuous_toFun

/-- The isomorphism has the original canonical homomorphism as its forward map. -/
@[simp]
lemma fundamentalGroupEquivOfPullbackEquivalence_apply
    (f : X ⟶ Y) [(pullback f).IsEquivalence] (ξ : Spec (.of Ω) ⟶ X)
    (a : π₁ᵉᵗ(ξ)) :
    fundamentalGroupEquivOfPullbackEquivalence f ξ a = fundamentalGroupHom f ξ a :=
  rfl

end AlgebraicGeometry.FiniteEtale

end

end
