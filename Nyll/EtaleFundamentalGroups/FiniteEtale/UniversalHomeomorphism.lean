/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.SchemeTheory.FiniteEtale.AffineUniversalHomeomorphismEquivalence
import Nyll.SchemeTheory.FiniteEtale.UniversalHomeomorphismFullyFaithful
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PurelyInseparableGluing
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Universal homeomorphisms preserve finite étale covers

Every affine chart of the lower scheme has an actual finite étale model of
the upper cover. The models and their recovery isomorphisms supply the
transition maps, whose equations are detected by fully faithful radicial
pullback. Gluing gives essential surjectivity without a flatness condition.

Together with the previously established full faithfulness, this proves
the finite étale equivalence for arbitrary schemes. For connected schemes,
the induced map on fundamental groups is the forward map of a topological
group isomorphism.

Source: Stacks Project, Proposition 58.8.4, Tag 0BQN:
https://stacks.math.columbia.edu/tag/0BQN
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] finiteEtaleInfStableUnderBaseChangeUniversalHomeomorphism

/-- Actual affine models glue to a finite étale model along an arbitrary
integral, universally injective, surjective scheme morphism. -/
theorem pullback_essSurj_of_integral_universallyInjective_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (MorphismProperty.Over.pullback
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ f).EssSurj := by
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  constructor
  intro V
  let 𝒰 : Y.OpenCover := Y.directedAffineCover
  let F (i : 𝒰.I₀) : P.Over ⊤ (𝒰.X i) ⥤ P.Over ⊤ (Limits.pullback (𝒰.f i) f) :=
    MorphismProperty.Over.pullback P ⊤ (Limits.pullback.fst (𝒰.f i) f)
  let A (i : 𝒰.I₀) : P.Over ⊤ (Limits.pullback (𝒰.f i) f) :=
    (MorphismProperty.Over.pullback P ⊤ (Limits.pullback.snd (𝒰.f i) f)).obj V
  let hF : ∀ i : 𝒰.I₀, (F i).IsEquivalence := by
    intro i
    let : IsAffine (𝒰.X i) := i.2
    let : UniversallyInjective (Limits.pullback.fst (𝒰.f i) f) :=
      UniversallyInjective.isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (𝒰.f i) f).flip inferInstance
    exact pullback_isEquivalence_of_isAffine_of_universalHomeomorphism
      (Limits.pullback.fst (𝒰.f i) f)
  let W (i : 𝒰.I₀) : P.Over ⊤ (𝒰.X i) := (F i).objPreimage (A i)
  let M (i : 𝒰.I₀) : Over (𝒰.X i) := (W i).toComma
  let hM : ∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom := by
    intro i
    let : IsFinite (M i).hom := (W i).prop.1
    let : Etale (M i).hom := (W i).prop.2
    exact ⟨⟩
  let e (i : 𝒰.I₀) :
      (Over.pullback (Limits.pullback.fst (𝒰.f i) f)).obj (M i) ≅
        (Over.pullback (Limits.pullback.snd (𝒰.f i) f)).obj V.toComma :=
    (MorphismProperty.Over.forget P ⊤ (Limits.pullback (𝒰.f i) f)).mapIso
      ((F i).objObjPreimageIso (A i))
  obtain ⟨N, ⟨eN⟩⟩ := EtaleFundamentalGroups.exists_finiteEtale_model_of_local_models
    f 𝒰 M V.toComma e
  let : IsFiniteEtale N.hom := N.prop
  let B : P.Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ N.hom ⟨inferInstance, inferInstance⟩
  refine ⟨B, ⟨?_⟩⟩
  exact (MorphismProperty.Comma.forgetFullyFaithful
    (Functor.id Scheme.{u}) (Functor.fromPUnit X) P).preimageIso eN

/-- Pullback along a universal homeomorphism is an equivalence on finite
étale covers, with no finiteness assumptions on the schemes. -/
@[stacks 0BQN]
theorem pullback_isEquivalence_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (FiniteEtale.pullback f).IsEquivalence := by
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  have hP : (MorphismProperty.Over.pullback P ⊤ f).IsEquivalence := {
    faithful := pullback_faithful_of_integral_universallyInjective_surjective f
    full := pullback_full_of_integral_universallyInjective_surjective f
    essSurj := pullback_essSurj_of_integral_universallyInjective_surjective f
  }
  have htransport (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
      (hQ : Q = (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (h : (MorphismProperty.Over.pullback Q ⊤ f).IsEquivalence) :
      (FiniteEtale.pullback f).IsEquivalence := by
    subst Q
    exact h
  exact htransport P IsFiniteEtale.eq_inf.symm hP

/-- For connected schemes, the actual induced homomorphism of fundamental
groups along a universal homeomorphism is a topological group isomorphism. -/
theorem universalHomeomorphism_fundamentalGroup_invariance
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    ∃ e : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ f),
      ∀ a : π₁ᵉᵗ(ξ), e a = fundamentalGroupHom f ξ a := by
  let : (FiniteEtale.pullback f).IsEquivalence :=
    pullback_isEquivalence_of_universalHomeomorphism f
  exact ⟨fundamentalGroupEquivOfPullbackEquivalence f ξ,
    fundamentalGroupEquivOfPullbackEquivalence_apply f ξ⟩

end AlgebraicGeometry.FiniteEtale
