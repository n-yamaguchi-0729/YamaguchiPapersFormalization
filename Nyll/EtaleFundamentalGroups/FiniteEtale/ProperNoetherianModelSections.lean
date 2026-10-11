/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ClosedFiberEtaleDescent
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalSectionAlgebra
import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Section comparisons for an actual Noetherian model

The closed-fibre comparison yields a pushout of the actual section maps.
This form retains the maps needed to compare a Noetherian model with an
arbitrary base and its localizations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

private theorem bijective_of_tensor_atMaximal
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (F : M →ₗ[R] N)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (F.baseChange (Localization.AtPrime P))) :
    Function.Bijective F := by
  apply bijective_of_isLocalized_maximal
    (fun P _ => Localization.AtPrime P ⊗[R] M)
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) M 1)
    (fun P _ => Localization.AtPrime P ⊗[R] N)
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) N 1) F
  intro P hP
  let iM := TensorProduct.mk R (Localization.AtPrime P) M 1
  let iN := TensorProduct.mk R (Localization.AtPrime P) N 1
  have hMap : IsLocalizedModule.map P.primeCompl iM iN F =
      (F.baseChange (Localization.AtPrime P)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl iM iN
    ext m
    exact IsLocalizedModule.map_apply P.primeCompl iM iN F m
  rw [hMap]
  exact h P

/-- Arbitrary base change is a pushout of actual section maps for a proper
flat Noetherian local family whose closed-fibre section algebra is étale. -/
theorem isPushout_sections_of_proper_flat_of_etale_closedFiber
    {S A : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [CommRing A] [Algebra S A] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of S)) [IsProper g] [Flat g]
    (hEtaleFiber : (pullback.snd g
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)))).appTop.hom.Etale) :
    IsPushout (CommRingCat.ofHom (algebraMap S A))
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S A)))).appTop)
      (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S A)))).appTop := by
  let b := Scheme.TwoAffineOpenCover.specMap S A
  let gA := pullback.snd g b
  let hSΓ : Algebra S Γ(Y, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom g ⊤
  let hAΓ : Algebra A Γ(pullback g b, ⊤) :=
    Scheme.TwoAffineOpenCover.algebraOfHom gA ⊤
  obtain ⟨e, he⟩ :=
    (finite_projective_sectionAlgebra_and_baseChange_of_etale_closedFiber g hEtaleFiber).2 A
  have hg : g.appTop = g.appLE ⊤ ⊤ le_top := g.app_eq_appLE
  have hgA : gA.appTop = gA.appLE ⊤ ⊤ le_top := gA.app_eq_appLE
  refine (CommRingCat.isPushout_tensorProduct S A Γ(Y, ⊤)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [hg]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    ext a
    change e (algebraMap A (A ⊗[S] Γ(Y, ⊤)) a) = _
    rw [e.commutes]
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gA.appLE ⊤ ⊤ le_top) a = _
    rw [← hgA]
  · rw [Iso.refl_hom, Category.id_comp]
    ext s
    change e (1 ⊗ₜ[S] s) = _
    rw [he, map_one, one_mul]

/-- A geometrically reduced family over a local ring gives canonical section
base change for any of its actual proper flat Noetherian local models. -/
theorem isPushout_sections_of_proper_flat_noetherian_local_model
    {S R : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [CommRing R] [IsLocalRing R] [Algebra S R] [IsLocalHom (algebraMap S R)]
    {Y X : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S)) [IsProper g] [Flat g]
    (f : X ⟶ Spec (CommRingCat.of R)) [GeometricallyReduced f] (p : X ⟶ Y)
    (hModel : IsPullback p f g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) :
    IsPushout (CommRingCat.ofHom (algebraMap S R))
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) p.appTop := by
  have hEtaleFiber : (pullback.snd g
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)))).appTop.hom.Etale :=
    (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).inv _).mp
      (etale_closedFiber_sections_of_isPullback_of_geometricallyReduced g f p hModel)
  refine (isPushout_sections_of_proper_flat_of_etale_closedFiber (A := R) g hEtaleFiber).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Scheme.Γ.mapIso hModel.isoPullback.op)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))).appTop) ≫
        hModel.isoPullback.hom.appTop = 𝟙 _ ≫ _
    rw [Category.id_comp, Category.assoc, ← Scheme.Hom.comp_appTop,
      hModel.isoPullback_hom_snd]
  · change (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S R)))).appTop ≫
        hModel.isoPullback.hom.appTop = 𝟙 _ ≫ _
    rw [Category.id_comp, ← Scheme.Hom.comp_appTop, hModel.isoPullback_hom_fst]

/-- Localizing the original base of an actual Noetherian model gives
canonical section base change. Only the original family after localization
is required to have geometrically reduced fibres. -/
theorem isPushout_sections_of_proper_flat_noetherian_model_atPrime
    {S R : Type u} [CommRing S] [IsNoetherianRing S] [CommRing R] [Algebra S R]
    (P : Ideal R) [P.IsPrime] {Y X : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of S)) [IsProper g] [Flat g]
    (f : X ⟶ Spec (CommRingCat.of (Localization.AtPrime P))) [GeometricallyReduced f]
    (p : X ⟶ Y)
    (hModel : IsPullback p f g
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime P))))) :
    IsPushout (CommRingCat.ofHom (algebraMap S (Localization.AtPrime P)))
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime P))).inv ≫ f.appTop)
      p.appTop := by
  let Q : Ideal S := P.under S
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  have : IsScalarTower S A B := inferInstance
  have : IsLocalHom (algebraMap A B) :=
    Localization.isLocalHom_localRingHom Q P (algebraMap S R) Ideal.LiesOver.over
  let a := Spec.map (CommRingCat.ofHom (algebraMap S A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have hab : b ≫ a = Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    dsimp only [a, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq S A B]
  have hOuter : IsPullback p f g (b ≫ a) := by
    rw [hab]
    exact hModel
  let hRight := IsPullback.of_hasPullback g a
  let pA := hRight.lift p (f ≫ b) (by rw [hOuter.w, Category.assoc])
  have hLocal : IsPullback pA f (pullback.snd g a) b := hOuter.of_right' hRight
  have hSectionsLocal := isPushout_sections_of_proper_flat_noetherian_local_model
    (pullback.snd g a) f pA hLocal
  have hSections := (isPushout_specPullbackSections (A := A) g).paste_horiz hSectionsLocal
  have hpA : pA ≫ pullback.fst g a = p := hRight.lift_fst _ _ _
  have hScalar : CommRingCat.ofHom (algebraMap S A) ≫ CommRingCat.ofHom (algebraMap A B) =
      CommRingCat.ofHom (algebraMap S B) := by
    rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq S A B]
  rw [hScalar, ← Scheme.Hom.comp_appTop, hpA] at hSections
  exact hSections

/-- The section algebra of a geometrically reduced family is the actual
base change of the section algebra of any proper flat Noetherian model.
The canonical comparison is checked at maximal ideals of the original base. -/
theorem isPushout_sections_of_proper_flat_noetherian_model
    {S R : Type u} [CommRing S] [IsNoetherianRing S] [CommRing R] [Algebra S R]
    {Y X : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S)) [IsProper g] [Flat g]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [GeometricallyReduced f]
    (p : X ⟶ Y)
    (hModel : IsPullback p f g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) :
    IsPushout (CommRingCat.ofHom (algebraMap S R))
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) p.appTop := by
  let hSΓ : Algebra S Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop).hom.toAlgebra
  let hRΓ : Algebra R Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  let hTensor := CommRingCat.isPushout_tensorProduct S R Γ(Y, ⊤)
  have hComm : CommRingCat.ofHom (algebraMap S R) ≫
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) =
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop) ≫ p.appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, ← hModel.w, Scheme.Hom.comp_appTop, Category.assoc]
  let d := hTensor.desc ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop)
    p.appTop hComm
  let β : R ⊗[S] Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤) := {
    toRingHom := d.hom
    commutes' := fun r => congrArg (fun k : CommRingCat.of R ⟶ Γ(X, ⊤) => k r)
      (hTensor.inl_desc _ _ hComm) }
  have hβ (s : Γ(Y, ⊤)) : β (1 ⊗ₜ[S] s) = p.appTop s :=
    congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => k s) (hTensor.inr_desc _ _ hComm)
  have hBijective : Function.Bijective β := by
    apply bijective_of_tensor_atMaximal β.toLinearMap
    intro P hP
    let A := Localization.AtPrime P
    let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let fA := pullback.snd f a
    let pA := pullback.fst f a
    let hAΓ : Algebra A Γ(pullback f a, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ fA.appTop).hom.toAlgebra
    have hBaseMaps : a ≫ Spec.map (CommRingCat.ofHom (algebraMap S R)) =
        Spec.map (CommRingCat.ofHom (algebraMap S A)) := by
      dsimp only [a]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq S R A]
    have hModelA : IsPullback (pA ≫ p) fA g
        (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
      rw [← hBaseMaps]
      exact (IsPullback.of_hasPullback f a).paste_horiz hModel
    have hSections := isPushout_sections_of_proper_flat_noetherian_model_atPrime
      P g fA (pA ≫ p) hModelA
    let eRing := (CommRingCat.isPushout_tensorProduct S A Γ(Y, ⊤)).isoPushout ≪≫
      hSections.isoPushout.symm
    let eModel : A ⊗[S] Γ(Y, ⊤) ≃ₐ[A] Γ(pullback f a, ⊤) := {
      toRingEquiv := eRing.commRingCatIsoToRingEquiv
      commutes' := fun r => by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ eRing.hom) r =
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ fA.appTop) r
        congr 2
        simp only [eRing, Iso.trans_hom, Iso.symm_hom,
          IsPushout.inl_isoPushout_hom_assoc, IsPushout.inl_isoPushout_inv]
        rfl }
    have heModel (s : Γ(Y, ⊤)) : eModel (1 ⊗ₜ[S] s) = (pA ≫ p).appTop s := by
      change (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ eRing.hom) s = _
      congr 2
      simp only [eRing, Iso.trans_hom, Iso.symm_hom,
        IsPushout.inr_isoPushout_hom_assoc, IsPushout.inr_isoPushout_inv]
    let eFlat : A ⊗[R] Γ(X, ⊤) ≃ₐ[A] Γ(pullback f a, ⊤) :=
      specPullbackSectionsTensorEquiv (A := A) f
    have heFlat (s : Γ(X, ⊤)) : eFlat (1 ⊗ₜ[R] s) = pA.appTop s :=
      specPullbackSectionsTensorEquiv_one_tmul (A := A) f s
    let eCancel := Algebra.TensorProduct.cancelBaseChange S R A A Γ(Y, ⊤)
    let e := eCancel.trans (eModel.trans eFlat.symm)
    have hComparison : β.toLinearMap.baseChange A = e.toLinearMap := by
      ext s
      apply eFlat.injective
      change eFlat ((β.toLinearMap.baseChange A) (1 ⊗ₜ[R] (1 ⊗ₜ[S] s))) =
        eFlat (eFlat.symm (eModel (eCancel (1 ⊗ₜ[R] (1 ⊗ₜ[S] s)))))
      rw [eFlat.apply_symm_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
      change eFlat (1 ⊗ₜ[R] β (1 ⊗ₜ[S] s)) = eModel (1 ⊗ₜ[S] s)
      rw [hβ, heFlat, heModel, Scheme.Hom.comp_appTop]
      rfl
    rw [hComparison]
    exact e.bijective
  let e := AlgEquiv.ofBijective β hBijective
  refine hTensor.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    exact hTensor.inl_desc _ _ hComm
  · rw [Iso.refl_hom, Category.id_comp]
    exact hTensor.inr_desc _ _ hComm

end AlgebraicGeometry
