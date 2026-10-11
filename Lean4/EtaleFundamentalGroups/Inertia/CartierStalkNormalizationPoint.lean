/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CartierLocalFractionFieldPullback
import EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso

/-!
# Normalization points above a Cartier component's discrete valuation stalk

The actual fraction-stalk square identifies the finite-etale pullback over
the local fraction field with the pullback over the stalk. The canonical
normalization comparison is an isomorphism and therefore transports every
specified point, preserving its fixing condition for all deck transformations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem pullbackSquare_iso_intertwines
    {C : Type*} [Category C] {A B X Y S : C}
    {p₁ : A ⟶ X} {q₁ : A ⟶ Y} {p₂ : B ⟶ X} {q₂ : B ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S}
    (H₁ : IsPullback p₁ q₁ f g) (H₂ : IsPullback p₂ q₂ f g)
    (τ₁ : A ⟶ A) (τ₂ : B ⟶ B) (σ : X ⟶ X)
    (hp₁ : τ₁ ≫ p₁ = p₁ ≫ σ) (hq₁ : τ₁ ≫ q₁ = q₁)
    (hp₂ : τ₂ ≫ p₂ = p₂ ≫ σ) (hq₂ : τ₂ ≫ q₂ = q₂) :
    τ₁ ≫ (H₁.isoIsPullback X Y H₂).hom =
      (H₁.isoIsPullback X Y H₂).hom ≫ τ₂ := by
  apply H₂.hom_ext
  · simp only [Category.assoc, IsPullback.isoIsPullback_hom_fst, hp₁, hp₂,
      IsPullback.isoIsPullback_hom_fst_assoc]
  · simp only [Category.assoc, IsPullback.isoIsPullback_hom_snd, hq₁, hq₂]

/-- A specified normalization point lifts to the actual fraction-stalk cover
and has exactly the same fixing deck transformations there. -/
theorem exists_fractionStalk_normalizationPoint
    {X T : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.IsEffectiveCartier) (x : X) (hx : x ∈ I.support)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (W : FiniteEtale I.supportComplement)
    (z : T ⟶ ((show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫
      I.supportComplement.ι).normalization)
    (y : T ⟶ Spec (X.presheaf.stalk x))
    (_hzy : z ≫ ((show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫
      I.supportComplement.ι).fromNormalization = y ≫ X.fromSpecStalk x) :
    let c := hI.fractionStalkToSupportComplement x
    let A := (FiniteEtale.pullback c).obj W
    let a := Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))))
    let g : A.left ⟶ Spec (X.presheaf.stalk x) :=
      (show A.left ⟶ Spec (.of (FractionRing (X.presheaf.stalk x))) from A.hom) ≫ a
    ∃ q : T ⟶ g.normalization,
      q ≫ g.fromNormalization = y ∧
      ∀ σ : Aut W,
        q ≫ normalizationEndomorphism g ((FiniteEtale.pullback c).map σ.hom).left
          (by
            rw [← Category.assoc]
            exact congrArg (fun k => k ≫ a) (((FiniteEtale.pullback c).map σ.hom).w)) = q ↔
        z ≫ normalizationEndomorphism
          ((show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫ I.supportComplement.ι)
          σ.hom.left (by
            rw [← Category.assoc]
            exact congrArg (fun k => k ≫ I.supportComplement.ι) σ.hom.w) = z := by
  intro c A a g
  let F : W.left ⟶ X :=
    (show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫ I.supportComplement.ι
  let b := X.fromSpecStalk x
  let F₁ := pullback.snd F b
  have : IsIso (F.normalizationPullback b) :=
    isIso_normalizationPullback_fromSpecStalk F x
  have Hcover : IsPullback
      (pullback.fst (show W.left ⟶ I.supportComplement.toScheme from W.hom) c)
      g F b :=
    (IsPullback.of_hasPullback
      (show W.left ⟶ I.supportComplement.toScheme from W.hom) c).paste_vert
      (hI.isPullback_fractionStalkToSupportComplement x hx)
  have H₁ : IsPullback (pullback.fst F b) F₁ F b := IsPullback.of_hasPullback F b
  let e : pullback F b ≅ A.left := H₁.isoIsPullback _ _ Hcover
  have he : e.hom ≫ g = F₁ :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec (X.presheaf.stalk x)) H₁ Hcover
  let q₀ : T ⟶ F₁.normalization :=
    pullback.lift z y _hzy ≫ inv (F.normalizationPullback b)
  have hq₀ : q₀ ≫ F₁.fromNormalization = y := by
    rw [← Scheme.Hom.normalizationPullback_snd F b]
    simp only [q₀, Category.assoc, IsIso.inv_hom_id_assoc]
    exact pullback.lift_snd z y _hzy
  let E : F₁.normalization ≅ g.normalization := normalizationSourceIso F₁ g e he
  refine ⟨q₀ ≫ E.hom, ?_, ?_⟩
  · exact (Category.assoc q₀ E.hom g.fromNormalization).trans
      ((congrArg (fun k : F₁.normalization ⟶ Spec (X.presheaf.stalk x) => q₀ ≫ k)
        (normalizationSourceIso_hom_fromNormalization F₁ g e he)).trans hq₀)
  · intro σ
    have hσ : σ.hom.left ≫ F = F := by
      dsimp only [F]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ I.supportComplement.ι) σ.hom.w
    let τ₁ := pullbackEndomorphism F b σ.hom.left hσ
    have hτ₁ : τ₁ ≫ F₁ = F₁ := pullbackEndomorphism_snd F b σ.hom.left hσ
    let τ := ((FiniteEtale.pullback c).map σ.hom).left
    have hτ : τ ≫ g = g := by
      dsimp only [g]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ a) (((FiniteEtale.pullback c).map σ.hom).w)
    have hτfst : τ ≫
        pullback.fst (show W.left ⟶ I.supportComplement.toScheme from W.hom) c =
        pullback.fst (show W.left ⟶ I.supportComplement.toScheme from W.hom) c ≫
          σ.hom.left := by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      exact pullback.lift_fst _ _ _
    have hcommute : τ₁ ≫ e.hom = e.hom ≫ τ :=
      pullbackSquare_iso_intertwines H₁ Hcover τ₁ τ σ.hom.left
        (pullbackEndomorphism_fst F b σ.hom.left hσ) hτ₁ hτfst hτ
    exact (normalizationSourceIso_fixes_iff F₁ g e he q₀ τ₁ hτ₁ τ hτ hcommute).trans
      (normalizationPullback_fixes_point_iff F b z y _hzy σ.hom.left hσ)

end EtaleFundamentalGroups.Inertia
