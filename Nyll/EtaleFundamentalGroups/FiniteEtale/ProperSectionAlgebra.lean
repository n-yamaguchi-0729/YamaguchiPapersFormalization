/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperNoetherianModelSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalFiniteEtaleSections
import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections
import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleFromLocalizations
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
import Nyll.AlgebraicCurves.Geometry.Schemes.finite_appTop_of_isProper_of_isNoetherianRing
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite étale sections over an arbitrary affine base

An actual Noetherian model supplies finite presentation of global sections
through canonical base change. Localizations then detect projectivity and
étaleness. No finiteness is inferred merely from finiteness at stalks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Global sections are finitely presented over the original affine base,
by descent to a proper flat Noetherian model and actual section base change. -/
theorem finitePresentation_sectionAlgebra_of_proper_flat_geometricallyReduced
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    Module.FinitePresentation R Γ(X, ⊤) := by
  intro hRΓ
  let : Algebra (ULift.{u} ℤ) R :=
    ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  have hIntegers : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  obtain ⟨S, hS, _, Y, g, p, hProper, hFlat, hModel⟩ :=
    ProperFlatFinitePresentationDescent (A₀ := ULift.{u} ℤ) f ∅
  have hFiniteTypeS : Algebra.FiniteType (ULift.{u} ℤ) S :=
    (Subalgebra.fg_iff_finiteType S).mp hS
  have hNoetherianS : IsNoetherianRing S :=
    Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) S
  let hSΓ : Algebra S Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appTop).hom.toAlgebra
  have hfin : Module.Finite S Γ(Y, ⊤) :=
    (finite_appTop_of_isProper_of_isNoetherianRing g).comp
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective)
  have hfp : Module.FinitePresentation S Γ(Y, ⊤) :=
    Module.finitePresentation_of_finite S Γ(Y, ⊤)
  have hSections := isPushout_sections_of_proper_flat_noetherian_model g f p hModel
  let eRing := (CommRingCat.isPushout_tensorProduct S R Γ(Y, ⊤)).isoPushout ≪≫
    hSections.isoPushout.symm
  let e : R ⊗[S] Γ(Y, ⊤) ≃ₐ[R] Γ(X, ⊤) := {
    toRingEquiv := eRing.commRingCatIsoToRingEquiv
    commutes' := fun r => by
      change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ eRing.hom) r =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) r
      congr 2
      simp only [eRing, Iso.trans_hom, Iso.symm_hom,
        IsPushout.inl_isoPushout_hom_assoc, IsPushout.inl_isoPushout_inv] }
  exact Module.FinitePresentation.of_equiv e.toLinearEquiv

/-- A proper flat finitely presented family with geometrically reduced fibres
over any affine base has a finite étale algebra of global sections. -/
theorem finite_etale_appTop_of_proper_flat_geometricallyReduced
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    f.appTop.hom.Finite ∧ f.appTop.hom.Etale := by
  let hRΓ : Algebra R Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  have hfp : Module.FinitePresentation R Γ(X, ⊤) :=
    finitePresentation_sectionAlgebra_of_proper_flat_geometricallyReduced f
  have hLocal : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Projective (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] Γ(X, ⊤)) ∧
        Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] Γ(X, ⊤)) := by
    intro P hP
    let A := Localization.AtPrime P
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let fA := pullback.snd f q
    let hAΓ : Algebra A Γ(pullback f q, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ fA.appTop).hom.toAlgebra
    have hApp : fA.appTop = fA.appLE ⊤ ⊤ le_top := fA.app_eq_appLE
    have hAlgebra : Scheme.TwoAffineOpenCover.algebraOfHom fA ⊤ = hAΓ := by
      change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        fA.appLE ⊤ ⊤ le_top).hom.toAlgebra) = _
      rw [← hApp]
    let Q (a : Algebra A Γ(pullback f q, ⊤)) : Prop :=
      let : Algebra A Γ(pullback f q, ⊤) := a
      Module.Projective A Γ(pullback f q, ⊤) ∧ Algebra.Etale A Γ(pullback f q, ⊤)
    have hSource : Q (Scheme.TwoAffineOpenCover.algebraOfHom fA ⊤) :=
      (finite_projective_etale_sectionAlgebra_of_proper_flat_geometricallyReduced_local fA).2
    have hTarget : Q hAΓ := (congrArg Q hAlgebra).mp hSource
    have hProjective : Module.Projective A Γ(pullback f q, ⊤) := hTarget.1
    have hEtale : Algebra.Etale A Γ(pullback f q, ⊤) := hTarget.2
    let e : A ⊗[R] Γ(X, ⊤) ≃ₐ[A] Γ(pullback f q, ⊤) :=
      specPullbackSectionsTensorEquiv (A := A) f
    exact ⟨Module.Projective.of_equiv e.symm.toLinearEquiv, Algebra.Etale.of_equiv e.symm⟩
  have hProjective : Module.Projective R Γ(X, ⊤) := by
    apply Module.projective_of_localization_maximal
    intro P hP
    have h := (hLocal P).1
    exact Module.Projective.of_equiv
      (LocalizedModule.equivTensorProduct P.primeCompl Γ(X, ⊤)).symm
  have hEtale : Algebra.Etale R Γ(X, ⊤) :=
    Algebra.etale_of_finite_projective_of_etale_localizations R Γ(X, ⊤)
      (fun P _ => (hLocal P).2)
  have hFinite : (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom).Finite :=
    inferInstanceAs (Module.Finite R Γ(X, ⊤))
  exact ⟨(RingHom.finite_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv f.appTop).mp hFinite,
    (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv f.appTop).mp hEtale⟩

end AlgebraicGeometry
