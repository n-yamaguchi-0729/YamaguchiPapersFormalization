/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory

/-!
# Functoriality of the étale fundamental group

Pullback along a morphism of schemes commutes with taking the fiber at a
field-valued point, in particular at a geometric point.  The resulting
comparison isomorphism induces the continuous homomorphism on automorphism
groups of fiber functors.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryFunctoriality (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
  instCategory X

local instance finiteEtaleHasPullbacksAlongFunctoriality
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongFunctoriality
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- Pulling a finite étale cover back along `f` and then taking its fiber at
`ξ` is naturally isomorphic to taking the fiber at the composite point. -/
noncomputable def pullbackFiberIso (f : X ⟶ Y) (ξ : Spec (.of Ω) ⟶ X) :
    pullback f ⋙ fiber ξ ≅ fiber (ξ ≫ f) :=
  (Functor.associator (pullback f) (pullback ξ) (forgetScheme Ω)).symm ≪≫
    (Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) ξ f)
      (forgetScheme Ω)).symm

/-- A morphism of schemes induces a continuous homomorphism from the
automorphism group of the fiber functor at a field-valued point to that at the
composite point.  For a geometric point these are the étale fundamental
groups. -/
noncomputable def fundamentalGroupHom (f : X ⟶ Y) (ξ : Spec (.of Ω) ⟶ X) :
    π₁ᵉᵗ(ξ) →ₜ* π₁ᵉᵗ(ξ ≫ f) :=
  CategoryTheory.PreGaloisCategory.autHomOfCompIso
    (pullback f) (pullbackFiberIso f ξ)

/-- Replacing the canonical fiber comparison by another one changes the
induced homomorphism by the corresponding inner conjugation. -/
theorem fundamentalGroupHom_eq_conj_of_comparison
    (f : X ⟶ Y) (ξ : Spec (.of Ω) ⟶ X)
    (t : pullback f ⋙ fiber ξ ≅ fiber (ξ ≫ f))
    (σ : π₁ᵉᵗ(ξ)) :
    CategoryTheory.PreGaloisCategory.autHomOfCompIso (pullback f) t σ =
      MulAut.conj (G := π₁ᵉᵗ(ξ ≫ f))
        ((pullbackFiberIso f ξ).symm ≪≫ t)
        (fundamentalGroupHom f ξ σ) := by
  exact CategoryTheory.PreGaloisCategory.autHomOfCompIso_eq_conj
    (pullback f) (pullbackFiberIso f ξ) t σ

end AlgebraicGeometry.FiniteEtale

end
