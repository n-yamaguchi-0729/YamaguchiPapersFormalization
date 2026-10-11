/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.TrivialBaseChangeAlgebra
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import EtaleFundamentalGroups.StrictHenselian.StrictGenericSplittingNormal
import EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
import Mathlib.AlgebraicGeometry.Morphisms.Finite


/-!
# Strict generic actions and finite normalization

Triviality of the actual strict generic image action produces a split tensor
algebra and hence an etale normalization. In the other direction an actual
finite etale cover of the local base becomes trivial over the strict generic
field because it pulls back through the actual geometric stalk.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem finiteEtale_spec_of_finite_etale_algebra
    (K B : Type u) [CommRing K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [Algebra.Etale K B] :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
  apply IsFiniteEtale.SpecMap_iff.mpr
  exact RingHom.finiteEtale_algebraMap_iff.mpr ⟨⟩

local instance (X : Scheme.{u}) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
  AlgebraicGeometry.FiniteEtale.instCategory X

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback (P := @IsFiniteEtale) h hf⟩

/-- The actual strict generic image fixing a finite etale algebra's fiber
implies that its normalization over the original normal local domain is etale. -/
theorem integralClosure_etale_of_strictGeneric_image_fixed
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (B : Type u) [CommRing B] [Algebra R B] [Algebra (FractionRing R) B]
    [IsScalarTower R (FractionRing R) B]
    [Module.Finite (FractionRing R) B] [Algebra.Etale (FractionRing R) B]
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))) :
    let : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) B))) :=
      finiteEtale_spec_of_finite_etale_algebra (FractionRing R) B
    (∀ (g : Aut (fiber point))
      (w : (fiber (point ≫ Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))).obj
        (mk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) B))))),
      fundamentalGroupHom (Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))
        point g • w = w) →
    Algebra.Etale R (integralClosure R B) := by
  intro finiteEtaleInstance hfixed
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra (FractionRing R) (FractionRing A) :=
    (geometricStalkFractionFieldMap φ).toAlgebra
  obtain ⟨ι, hι, e⟩ := exists_tensor_algEquiv_pi_of_image_fixed
    (FractionRing R) (FractionRing A) B point hfixed
  have : Finite ι := hι
  exact integralClosure_etale_of_normal_strictGeneric_tensor_split (B := B) φ ι e

/-- A finite etale cover of the original local ring has trivial fiber action
after pullback to the actual strict generic field. -/
theorem geometricStalkFractionPullback_fiber_fixed
    {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (Z : FiniteEtale (Spec (.of R)))
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))) :
    let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    ∀ (g : Aut (fiber point))
      (w : (fiber point).obj ((pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫
          Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))).obj Z)),
      g • w = w := by
  intro A g w
  let f := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  let r := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let E : (pullback (f ≫ r)).obj Z ≅ (pullback f).obj ((pullback r).obj Z) :=
    (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f r).app Z
  apply (ConcreteCategory.bijective_of_isIso ((fiber point).map E.hom)).injective
  rw [← CategoryTheory.PreGaloisCategory.mulAction_naturality]
  apply pullback_fiber_fixed_of_image_fixed f point ((pullback r).obj Z)
  intro a z
  have : Subsingleton π₁ᵉᵗ(point ≫ f) :=
    subsingleton_fundamentalGroup_geometricStalk (Spec.map (CommRingCat.ofHom φ)) (point ≫ f)
  rw [Subsingleton.elim (fundamentalGroupHom f point a) 1, one_smul]

end EtaleFundamentalGroups.StrictHenselian
