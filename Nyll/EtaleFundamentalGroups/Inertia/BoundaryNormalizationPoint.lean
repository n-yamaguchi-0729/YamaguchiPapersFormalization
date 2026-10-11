/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.BoundaryAwayPullback
import Nyll.EtaleFundamentalGroups.Inertia.EtaleChartNormalizationPoint
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso

/-!
# A normalization point on the actual local finite-etale cover

The boundary-away square identifies the actual finite-etale pullback with the
successive pullbacks through the etale chart and its localized stalk. This
source isomorphism intertwines all pulled-back deck transformations. Extending
it to normalization transports the specified point and preserves its stabilizer.
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

/-- Transport the specified normalization point to the actual boundary-away
finite-etale pullback, with the exact fixing condition for every deck map. -/
theorem exists_boundaryAway_normalizationPoint
    {X U T : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (f : U ⟶ X) [Etale f] (u : U)
    (P : Spec (U.presheaf.stalk u)) :
    let : P.asIdeal.IsPrime := P.isPrime
    ∀ {r : ℕ} (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hb : ((I.comap f).stalkIdeal u).map
      (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P.asIdeal)) =
        Ideal.span {EtaleFundamentalGroups.boundaryProduct t r})
    (W : FiniteEtale I.supportComplement)
    (z : T ⟶ ((show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫
      I.supportComplement.ι).normalization)
    (y : T ⟶ Spec (.of (Localization.AtPrime P.asIdeal)))
    (_hzy : z ≫ ((show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫
      I.supportComplement.ι).fromNormalization =
        y ≫ Scheme.localizationAtPrimeTo U u P.asIdeal ≫ f),
    let c := I.boundaryAwayToSupportComplement f u P t hb
    let A := (FiniteEtale.pullback c).obj W
    let a := Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime P.asIdeal)
        (Localization.Away (EtaleFundamentalGroups.boundaryProduct t r))))
    let g : A.left ⟶ Spec (.of (Localization.AtPrime P.asIdeal)) :=
      (show A.left ⟶ Spec (.of (Localization.Away
        (EtaleFundamentalGroups.boundaryProduct t r))) from A.hom) ≫ a
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
  intro hP r t hb W z y hzy c A a g
  let h : Spec (.of (Localization.AtPrime P.asIdeal)) ⟶ U :=
    Scheme.localizationAtPrimeTo U u P.asIdeal
  let F : W.left ⟶ X :=
    (show W.left ⟶ I.supportComplement.toScheme from W.hom) ≫ I.supportComplement.ι
  let F₁ := pullback.snd F f
  let F₂ := pullback.snd F₁ h
  have Hcover : IsPullback
      (pullback.fst (show W.left ⟶ I.supportComplement.toScheme from W.hom) c)
      g F (h ≫ f) :=
    (IsPullback.of_hasPullback
      (show W.left ⟶ I.supportComplement.toScheme from W.hom) c).paste_vert
      (I.isPullback_boundaryAwayToSupportComplement f u P t hb)
  have Htwo : IsPullback (pullback.fst F₁ h ≫ pullback.fst F f) F₂ F (h ≫ f) :=
    (IsPullback.of_hasPullback F₁ h).paste_horiz (IsPullback.of_hasPullback F f)
  let e : pullback F₁ h ≅ A.left := Htwo.isoIsPullback _ _ Hcover
  have he : e.hom ≫ g = F₂ := IsPullback.isoIsPullback_hom_snd W.left
    (Spec (.of (Localization.AtPrime P.asIdeal))) Htwo Hcover
  have hzy' : z ≫ F.fromNormalization = y ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P.asIdeal))) ≫
        U.fromSpecStalk u ≫ f := by
    simpa only [Scheme.localizationAtPrimeTo, Category.assoc] using hzy
  obtain ⟨q₀, hq₀, hfix₀⟩ := exists_normalizationPoint_etaleChart_localizedStalk
    F f u P.asIdeal z y hzy'
  let E : F₂.normalization ≅ g.normalization := normalizationSourceIso F₂ g e he
  refine ⟨q₀ ≫ E.hom, ?_, ?_⟩
  · exact (Category.assoc q₀ E.hom g.fromNormalization).trans
      ((congrArg (fun k : F₂.normalization ⟶ Spec (.of (Localization.AtPrime P.asIdeal)) =>
        q₀ ≫ k) (normalizationSourceIso_hom_fromNormalization F₂ g e he)).trans hq₀)
  · intro σ
    have hσ : σ.hom.left ≫ F = F := by
      dsimp only [F]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ I.supportComplement.ι) σ.hom.w
    let τ₁ := pullbackEndomorphism F f σ.hom.left hσ
    have hτ₁ : τ₁ ≫ F₁ = F₁ := pullbackEndomorphism_snd F f σ.hom.left hσ
    let τ₂ := pullbackEndomorphism F₁ h τ₁ hτ₁
    have hτ₂ : τ₂ ≫ F₂ = F₂ := pullbackEndomorphism_snd F₁ h τ₁ hτ₁
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
    have hτ₂fst : τ₂ ≫ (pullback.fst F₁ h ≫ pullback.fst F f) =
        (pullback.fst F₁ h ≫ pullback.fst F f) ≫ σ.hom.left := by
      calc
        τ₂ ≫ (pullback.fst F₁ h ≫ pullback.fst F f) =
            (τ₂ ≫ pullback.fst F₁ h) ≫ pullback.fst F f :=
          (Category.assoc τ₂ (pullback.fst F₁ h) (pullback.fst F f)).symm
        _ = (pullback.fst F₁ h ≫ τ₁) ≫ pullback.fst F f :=
          congrArg (fun k => k ≫ pullback.fst F f)
            (pullbackEndomorphism_fst F₁ h τ₁ hτ₁)
        _ = pullback.fst F₁ h ≫ (τ₁ ≫ pullback.fst F f) := Category.assoc _ _ _
        _ = pullback.fst F₁ h ≫ (pullback.fst F f ≫ σ.hom.left) :=
          congrArg (fun k => pullback.fst F₁ h ≫ k)
            (pullbackEndomorphism_fst F f σ.hom.left hσ)
        _ = (pullback.fst F₁ h ≫ pullback.fst F f) ≫ σ.hom.left :=
          (Category.assoc (pullback.fst F₁ h) (pullback.fst F f) σ.hom.left).symm
    have hcommute : τ₂ ≫ e.hom = e.hom ≫ τ :=
      pullbackSquare_iso_intertwines Htwo Hcover τ₂ τ σ.hom.left hτ₂fst hτ₂ hτfst hτ
    exact (normalizationSourceIso_fixes_iff F₂ g e he q₀ τ₂ hτ₂ τ hτ hcommute).trans
      (hfix₀ σ.hom.left hσ)

end EtaleFundamentalGroups.Inertia
