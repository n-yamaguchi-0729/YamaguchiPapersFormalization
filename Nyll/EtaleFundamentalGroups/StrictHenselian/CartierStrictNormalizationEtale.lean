/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.StrictGenericNormalizationEtale
import Nyll.EtaleFundamentalGroups.StrictHenselian.CartierStrictFractionMap
import Nyll.EtaleFundamentalGroups.Inertia.CartierLocalFractionFieldPullback
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization

/-!
# Strict generic triviality and the original normalization at a Cartier point

The actual strict generic pullback is compared to the iterated pullback via
the local fraction field. Etaleness of its normalization is then transported
through the actual Cartier square and the normalization-stalk comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.StrictHenselian

local instance (X : Scheme.{0}) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme.{0}) ⊤ X) :=
  AlgebraicGeometry.FiniteEtale.instCategory X

local instance {X Y : Scheme.{0}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme.{0}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance {X Y : Scheme.{0}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{0}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback (P := @IsFiniteEtale) h hf⟩

/-- Triviality of the actual strict generic action at a boundary DVR makes
the base change of the original cover's normalization etale at that stalk. -/
theorem normalization_stalk_etale_of_strictGeneric_image_fixed
    {X : Scheme.{0}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (x : X) (hx : x ∈ D.1.support)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ]
    (W : FiniteEtale D.1.supportComplement)
    {Ω' : Type} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶ Spec (.of
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))))
    (hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber (point ≫ geometricStalkFractionFieldToComplement D x φ)).obj W),
      fundamentalGroupHom (geometricStalkFractionFieldToComplement D x φ) point g • w = w) :
    Etale (Limits.pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (X.fromSpecStalk x)) := by
  let R := X.presheaf.stalk x
  let K := FractionRing R
  let c := D.2.fractionStalkToSupportComplement x
  let a := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let j := geometricStalkFractionFieldToComplement D x φ
  let l := Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ))
  let V := (FiniteEtale.pullback c).obj W
  have hcomp : l ≫ c = j :=
    geometricStalkFractionFieldMap_comp_fractionStalkToSupportComplement D x φ
  let E : (FiniteEtale.pullback l).obj V ≅ (FiniteEtale.pullback j).obj W :=
    ((MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) l c).app W).symm ≪≫
      eqToIso (congrArg (fun k => (FiniteEtale.pullback k).obj W) hcomp)
  have hV : ∀ (g : Aut (fiber point)) (v : (fiber (point ≫ l)).obj V),
      fundamentalGroupHom l point g • v = v := by
    apply image_fixed_of_pullback_fiber_fixed l point V
    intro g v
    apply (ConcreteCategory.bijective_of_isIso ((fiber point).map E.hom)).injective
    exact (CategoryTheory.PreGaloisCategory.mulAction_naturality (fiber point)
      g E.hom v).symm.trans
        (pullback_fiber_fixed_of_image_fixed j point W hfixed g ((fiber point).map E.hom v))
  let f : V.left ⟶ Spec (.of R) := (show V.left ⟶ Spec (.of K) from V.hom) ≫ a
  have hf : Etale f.fromNormalization :=
    etale_fractionCover_normalization_of_strictGeneric_image_fixed φ V point hV
  let F : W.left ⟶ X := W.hom ≫ D.1.supportComplement.ι
  let b : Spec (.of R) ⟶ X := X.fromSpecStalk x
  have H : IsPullback (Limits.pullback.fst W.hom c) f F b :=
    (IsPullback.of_hasPullback W.hom c).paste_vert
      (D.2.isPullback_fractionStalkToSupportComplement x hx)
  let e : Limits.pullback F b ≅ V.left :=
    (IsPullback.of_hasPullback F b).isoIsPullback _ _ H
  have he : e.hom ≫ f = Limits.pullback.snd F b :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec (.of R))
      (IsPullback.of_hasPullback F b) H
  let en := normalizationSourceIso (Limits.pullback.snd F b) f e he
  have hPB : Etale (Limits.pullback.snd F b).fromNormalization := by
    have ht : Etale (en.hom ≫ f.fromNormalization) := inferInstance
    rw [normalizationSourceIso_hom_fromNormalization] at ht
    exact ht
  let : IsIso (F.normalizationPullback b) := isIso_normalizationPullback_fromSpecStalk F x
  have heq : Limits.pullback.snd F.fromNormalization b =
      inv (F.normalizationPullback b) ≫ (Limits.pullback.snd F b).fromNormalization := by
    exact (IsIso.inv_hom_id_assoc (F.normalizationPullback b)
      (Limits.pullback.snd F.fromNormalization b)).symm.trans
        (congrArg (fun k => inv (F.normalizationPullback b) ≫ k)
          (Scheme.Hom.normalizationPullback_snd F b))
  change Etale (Limits.pullback.snd F.fromNormalization b)
  rw [heq]
  infer_instance

end EtaleFundamentalGroups.StrictHenselian
