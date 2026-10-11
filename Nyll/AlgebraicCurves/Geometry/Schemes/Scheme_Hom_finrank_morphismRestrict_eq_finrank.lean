/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.Set
import Batteries.Tactic.OpenPrivate

/-!
# Scheme Hom finrank morphism Restrict eq finrank
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_Hom_finrank_morphismRestrict_eq_finrank

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (IsOpenImmersion.lift Scheme.Opens.range_ι
  isPushout_appTop_of_isPullback Scheme.Hom IsFinite isAffine_of_isAffineHom IsAffine
  isPullback_morphismRestrict Spec Spec.map Scheme Scheme.Hom.finrank_SpecMap_eq_finrank
  IsOpenImmersion Flat Γ_restrict_isLocalization Scheme.Hom.finrank_of_isPullback
  HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.isoSpec_hom_naturality IsFinite.SpecMap_iff
  HasRingHomProperty.appTop Scheme.Opens HasRingHomProperty IsOpenImmersion.lift_fac
  Scheme.Hom.comp_apply Scheme.Hom.finrank)

namespace FinrankLocal

open _root_.AlgebraicGeometry


private theorem finrank_tensorProduct_eq_of_algEquiv {A : Type*} [CommRing A] {R R' : Type*}
  [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] (e : R ≃ₐ[A] R') (M : Type*) [AddCommGroup M] [Module A M] :
    Module.finrank R (R ⊗[A] M) = Module.finrank R' (R' ⊗[A] M) := by
  let j : R ⊗[A] M ≃ₗ[A] R' ⊗[A] M := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)
  have hc : ∀ (r : R) (x : R ⊗[A] M), j (r • x) = e r • j x := by
    intro r x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
        simp only [j, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.congr_tmul,
          LinearEquiv.refl_apply,
          AlgEquiv.toLinearEquiv_apply, map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have h := lift_rank_eq_of_equiv_equiv e j.toAddEquiv e.bijective hc
  have h' := congrArg Cardinal.toNat h
  simpa [Module.finrank, Cardinal.toNat_lift] using h'

private theorem rankAtStalk_eq_of_isLocalizedModule {A A' : Type*} [CommRing A] [CommRing A']
  [Algebra A A']
    (S : Submonoid A) [IsLocalization S A'] {M M' : Type*} [AddCommGroup M] [Module A M]
      [AddCommGroup M']
    [Module A M'] [Module A' M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') [IsLocalizedModule S f]
    (p : PrimeSpectrum A') :
    Module.rankAtStalk (R := A') M' p = Module.rankAtStalk (R := A) M (p.comap (algebraMap A A'))
      := by
  rw [Module.rankAtStalk_eq_finrank_tensorProduct, Module.rankAtStalk_eq_finrank_tensorProduct]
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) (p.comap (algebraMap A
    A')).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (M := S)
      (Localization.AtPrime p.asIdeal) p.asIdeal
  let e : Localization.AtPrime (p.comap (algebraMap A A')).asIdeal ≃ₐ[A] Localization.AtPrime
    p.asIdeal :=
    IsLocalization.algEquiv (p.comap (algebraMap A A')).asIdeal.primeCompl _ _
  rw [finrank_tensorProduct_eq_of_algEquiv e M]
  have hb : IsBaseChange A' f := (isLocalizedModule_iff_isBaseChange S A' f).mp inferInstance
  let e₁ : Localization.AtPrime p.asIdeal ⊗[A'] M' ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[A'] (A' ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) hb.equiv.symm
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A A' (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime p.asIdeal) M
  exact (e₁.trans e₂).finrank_eq

private theorem finrank_eq_of_isPushout_of_away {R B T P : CommRingCat.{u}} {φ : R ⟶ B} {ψ : R ⟶ T}
    {inl : B ⟶ P} {inr : T ⟶ P} (h : IsPushout φ ψ inl inr) (r : R)
    (hT : letI := ψ.hom.toAlgebra; IsLocalization.Away r T) (x : PrimeSpectrum T) :
    inr.hom.finrank x = φ.hom.finrank (PrimeSpectrum.comap ψ.hom x) := by
  algebraize [φ.hom, ψ.hom, inl.hom, inr.hom, inl.hom.comp φ.hom]
  have : IsScalarTower R T P := .of_algebraMap_eq' <| congr($(h.1.1).hom)
  have : Algebra.IsPushout R B T P := CommRingCat.isPushout_iff_isPushout.mp h
  have : Algebra.IsPushout R T B P := Algebra.IsPushout.symm inferInstance
  have hbc : IsBaseChange T (IsScalarTower.toAlgHom R B P).toLinearMap := Algebra.IsPushout.out
  have : IsLocalization.Away r T := hT
  have : IsLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom R B P).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) T _).mpr hbc
  change Module.rankAtStalk (R := T) P x = Module.rankAtStalk (R := R) B _
  exact rankAtStalk_eq_of_isLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom R B
    P).toLinearMap x

end AlgebraicGeometry.FinrankLocal

open AlgebraicGeometry.FinrankLocal in
open private IsAffine.finrank in Scheme.Hom.finrank in
theorem _root_.AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (W : S.Opens) [Flat (f ∣_ W)] (s : S) (hs : s ∈ W) :
    (f ∣_ W).finrank ⟨s, hs⟩ = f.finrank s := by
  classical
  set i₀ := S.affineOpenCover.idx s with hi₀
  set T : Scheme.{u} := Spec (S.affineOpenCover.X i₀) with hT
  set ι : T ⟶ S := S.affineOpenCover.f i₀ with hι
  set t₀ : T := (S.affineOpenCover.covers s).choose with ht₀def
  have ht₀ : ι t₀ = s := (S.affineOpenCover.covers s).choose_spec
  set g : pullback f ι ⟶ T := pullback.snd f ι with hg
  have hdef : f.finrank s = g.appTop.hom.finrank (T.isoSpec.hom t₀) := rfl
  have ht₀W : t₀ ∈ ι ⁻¹ᵁ W := by change ι t₀ ∈ W; rw [ht₀]; exact hs
  obtain ⟨r, hr, ht₀r⟩ := (isAffineOpen_top T).exists_basicOpen_le ⟨t₀, ht₀W⟩ (Set.mem_univ _)
  set T' : Scheme.{u} := ↑(T.basicOpen r) with hT'
  set j : T' ⟶ T := (T.basicOpen r).ι with hj
  have : IsAffine T' := (isAffineOpen_top T).basicOpen r
  set t' : T' := ⟨t₀, ht₀r⟩ with ht'
  have hjt' : j t' = t₀ := rfl
  set g' : pullback g j ⟶ T' := pullback.snd g j with hg'
  have : IsAffine (pullback f ι) := isAffine_of_isAffineHom g
  have : IsAffine (pullback g j) := isAffine_of_isAffineHom g'
  have hrange : Set.range (j ≫ ι).base ⊆ Set.range W.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hr x.2
  set k : T' ⟶ ↑W := IsOpenImmersion.lift W.ι (j ≫ ι) hrange with hk
  have hkfac : k ≫ W.ι = j ≫ ι := IsOpenImmersion.lift_fac _ _ _
  have hkt' : k t' = ⟨s, hs⟩ := by
    apply W.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hkfac, Scheme.Hom.comp_apply, hjt', ht₀]
    rfl
  have big : IsPullback (pullback.fst g j ≫ pullback.fst f ι) g' f (k ≫ W.ι) := by
    rw [hkfac]; exact (IsPullback.of_hasPullback g j).paste_horiz (IsPullback.of_hasPullback f ι)
  have hP := IsPullback.of_right' big (isPullback_morphismRestrict f W).flip
  have : Flat g' := MorphismProperty.of_isPullback (P := @Flat) hP inferInstance
  have : IsFinite g' := MorphismProperty.of_isPullback (P := @IsFinite) hP inferInstance
  have h1 : (f ∣_ W).finrank ⟨s, hs⟩ = g'.finrank t' := by
    rw [← hkt']; exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hP t').symm
  have h2 : g'.finrank t' = g'.appTop.hom.finrank (T'.isoSpec.hom t') := by
    have sq : IsPullback (pullback g j).isoSpec.hom g' (Spec.map g'.appTop) T'.isoSpec.hom :=
      IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g'⟩
    have hfin : g'.appTop.hom.Finite := g'.finite_appTop
    have hflat : g'.appTop.hom.Flat := HasRingHomProperty.appTop (P := @Flat) (f := g')
      inferInstance
    have : IsFinite (Spec.map g'.appTop) := (IsFinite.SpecMap_iff _).mpr hfin
    have : Flat (Spec.map g'.appTop) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t', Scheme.Hom.finrank_SpecMap_eq_finrank hfin
      hflat]
  have h3 : g'.appTop.hom.finrank (T'.isoSpec.hom t') = g.appTop.hom.finrank (T.isoSpec.hom t₀) :=
    by
    have hpo : IsPushout g.appTop j.appTop (pullback.fst g j).appTop g'.appTop :=
      isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g j)
    have hloc : letI := j.appTop.hom.toAlgebra; IsLocalization.Away r Γ(T', ⊤) :=
      AlgebraicGeometry.Γ_restrict_isLocalization T r
    change g'.appTop.hom.finrank
        (OrderDual.ofDual (specOrderIsoPrimeSpectrum Γ(T', ⊤) (T'.isoSpec.hom t'))) =
      g.appTop.hom.finrank
        (OrderDual.ofDual (specOrderIsoPrimeSpectrum Γ(T, ⊤) (T.isoSpec.hom t₀)))
    rw [finrank_eq_of_isPushout_of_away hpo r hloc]
    congr 1
    change (Spec.map j.appTop) (T'.isoSpec.hom t') = T.isoSpec.hom t₀
    rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply, hjt']
  rw [h1, h2, h3, hdef]
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_Hom_finrank_morphismRestrict_eq_finrank
end ProofImplementation
