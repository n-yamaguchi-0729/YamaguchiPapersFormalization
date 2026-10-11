/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.Choose

/-!
# Finite type from finitely generated factorizations

A scheme over an affine base is locally of finite type if every affine test map
factors through a finitely generated subalgebra over the base. Basic-open
localizations transport these factorizations around a point.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.AffineLimit.locallyOfFiniteType_of_forall_exists_fg_factor {R :
    Type u} [CommRing R] {X : Scheme.{u}}
    (ξ : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) :
    LocallyOfFiniteType ξ := by
  classical
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) := by
    have : HasAffineProperty (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
        (sourceAffineLocally RingHom.FiniteType) :=
      HasRingHomProperty.HasAffineProperty (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (Q
          := RingHom.FiniteType)
    apply HasAffineProperty.isZariskiLocalAtSource (Q := sourceAffineLocally RingHom.FiniteType)
    intro X Y f _ C
    have (i : C.affineRefinement.openCover.I₀) : IsAffine (C.affineRefinement.openCover.X i) :=
      Scheme.isAffine_affineOpenCover X C.affineRefinement i
    have e {X' : Scheme.{u}} (k : X' ⟶ Y) :
        (sourceAffineLocally RingHom.FiniteType) k ↔ LocallyOfFiniteType k :=
      (HasAffineProperty.iff_of_isAffine (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
        (Q := sourceAffineLocally RingHom.FiniteType) (f := k)).symm
    refine (e f).trans ?_
    refine (HasRingHomProperty.iff_of_source_openCover
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u})) (Q := RingHom.FiniteType)
      (f := f) C.affineRefinement.openCover).trans ?_
    rw [show (∀ i, (sourceAffineLocally RingHom.FiniteType) (C.f i ≫ f)) ↔
        (∀ i, LocallyOfFiniteType (C.f i ≫ f)) from forall_congr' (fun i => e (C.f i ≫ f))]
    simp_rw [
      fun i => HasRingHomProperty.iff_of_source_openCover
        (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
        (f := C.f i ≫ f) (C.X i).affineCover]
    change (∀ i : Σ j : C.I₀, (C.X j).affineCover.I₀,
      RingHom.FiniteType ((((C.X i.1).affineCover.f i.2 ≫ C.f i.1) ≫ f).appTop).hom) ↔
        ∀ i : C.I₀, ∀ j : (C.X i).affineCover.I₀,
          RingHom.FiniteType (((C.X i).affineCover.f j ≫ C.f i ≫ f).appTop).hom
    simp only [Sigma.forall, Category.assoc]
  suffices key : ∀ p : X, ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      p ∈ Set.range ⇑j ∧ LocallyOfFiniteType (j ≫ ξ) by
    choose Y j hj hmem hlft using key
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
      (Scheme.Cover.mkOfCovers X Y j (fun x => ⟨x, hmem x⟩) (fun x => hj x)) hlft
  intro p
  obtain ⟨B, ι, hι, y, hy⟩ : ∃ (B : CommRingCat.{u}) (ι : Spec B ⟶ X) (_ : IsOpenImmersion ι) (y :
      Spec B), ι y = p := by
    obtain ⟨V, hV, hpV, -⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ p ∈ V ∧ V ≤ ⊤ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) (show p ∈ (⊤ :
          X.Opens) from trivial)
    refine ⟨Γ(X, V), hV.isoSpec.inv ≫ V.ι, inferInstance, hV.isoSpec.hom ⟨p, hpV⟩, ?_⟩
    let p' : (V : Scheme.{u}) := ⟨p, hpV⟩
    have hp : hV.isoSpec.inv (hV.isoSpec.hom p') = p' :=
      (Scheme.Hom.comp_apply hV.isoSpec.hom hV.isoSpec.inv p').symm.trans
        (congrArg (fun k : (V : Scheme.{u}) ⟶ (V : Scheme.{u}) => k p') hV.isoSpec.hom_inv_id)
    exact (Scheme.Hom.comp_apply hV.isoSpec.inv V.ι (hV.isoSpec.hom p')).trans
      (congrArg (fun z : (V : Scheme.{u}) => V.ι z) hp)
  let : Algebra R B := (Spec.preimage (ι ≫ ξ)).hom.toAlgebra
  have hιξ : ι ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨B₀, hB₀, φ₀, hφ₀, hfac⟩ := h B ι hιξ
  have : Algebra.FiniteType R ↥B₀ := (Subalgebra.fg_iff_finiteType B₀).mp hB₀
  have hq : (Spec.map (CommRingCat.ofHom B₀.val.toRingHom)) y ∈ φ₀ ⁻¹ᵁ ι.opensRange := by
    change φ₀ (Spec.map (CommRingCat.ofHom B₀.val.toRingHom) y) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hfac]
    exact ⟨y, rfl⟩
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hfU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hq
  let f : B := (f₀ : B)
  let j₀ : Spec (CommRingCat.of (Localization.Away f₀)) ⟶ Spec (CommRingCat.of ↥B₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥B₀ (Localization.Away f₀)))
  let jB : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec B :=
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f)))
  have hpow : Submonoid.powers f₀ ≤ (Submonoid.powers f).comap B₀.val.toRingHom := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [f]⟩
  let g : Localization.Away f₀ →+* Localization.Away f :=
    IsLocalization.map (Localization.Away f) B₀.val.toRingHom hpow
  have hsq : jB ≫ Spec.map (CommRingCat.ofHom B₀.val.toRingHom) = Spec.map (CommRingCat.ofHom g) ≫
      j₀ := by
    simp only [jB, j₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp hpow).symm
  have hrange : Set.range ⇑(j₀ ≫ φ₀) ⊆ Set.range ⇑ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hz : j₀ z ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum ↥B₀)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f₀) f₀]
      exact ⟨z, rfl⟩
    have := hfU hz
    rwa [← Scheme.Hom.coe_opensRange]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* Localization.Away f₀, Spec.map (CommRingCat.ofHom ρ) ≫ ι = j₀ ≫ φ₀ :=
    ⟨(Spec.preimage (IsOpenImmersion.lift ι (j₀ ≫ φ₀) hrange)).hom, by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  have hcomp : g.comp ρ = algebraMap B (Localization.Away f) := by
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ρ) = jB := by
      rw [← cancel_mono ι, Category.assoc, hρ, ← Category.assoc, ← hsq, Category.assoc, hfac]
    have h2 := Spec.map_injective ((Spec.map_comp _ _).trans h1)
    exact congrArg CommRingCat.Hom.hom h2
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    refine ⟨ρ b * IsLocalization.mk' (Localization.Away f₀) 1 (⟨f₀ ^ n, n, rfl⟩ : Submonoid.powers
        f₀), ?_⟩
    have e1 : g (ρ b) = algebraMap B (Localization.Away f) b := by rw [← RingHom.comp_apply, hcomp]
    have e2 : g (IsLocalization.mk' (Localization.Away f₀) 1 (⟨f₀ ^ n, n, rfl⟩ : Submonoid.powers
        f₀)) =
        IsLocalization.mk' (Localization.Away f) 1 (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
      rw [IsLocalization.map_mk']
      rfl
    change g (_ * _) = IsLocalization.mk' (Localization.Away f) b (⟨f ^ n, n, rfl⟩ :
        Submonoid.powers f)
    rw [map_mul, e1, e2, ← IsLocalization.mk'_eq_mul_mk'_one]
  let : Algebra R (Localization.Away f₀) := inferInstance
  have hgR : ∀ r : R, g (algebraMap R (Localization.Away f₀) r) = algebraMap R (Localization.Away f)
      r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R ↥B₀ (Localization.Away f₀), IsScalarTower.algebraMap_apply
        R B (Localization.Away f)]
    change (g.comp (algebraMap ↥B₀ (Localization.Away f₀))) _ = _
    rw [IsLocalization.map_comp hpow]
    rfl
  let gₐ : Localization.Away f₀ →ₐ[R] Localization.Away f := { g with commutes' := hgR }
  have : Algebra.FiniteType R (Localization.Away f) := Algebra.FiniteType.of_surjective gₐ hsurj
  refine ⟨Spec (CommRingCat.of (Localization.Away f)), jB ≫ ι, inferInstance, ?_, ?_⟩
  · have hyf : y ∈ Set.range ⇑jB := by
      change y ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f)))
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact hqf
    obtain ⟨z, hz⟩ := hyf
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
  · rw [Category.assoc, hιξ, show jB ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R (↑B)
          (Localization.Away f)]]
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
end AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
