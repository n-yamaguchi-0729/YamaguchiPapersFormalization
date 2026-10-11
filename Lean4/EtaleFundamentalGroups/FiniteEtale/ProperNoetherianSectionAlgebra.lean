/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ProperLocalSectionAlgebra
import SchemeTheory.Affine.SpecFlatBaseChangeSections
import SchemeTheory.FiniteEtale.Algebra.EtaleFromLocalizations
import AlgebraicCurves.Geometry.Schemes.finite_appTop_of_isProper_of_isNoetherianRing
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite étale sections over a Noetherian affine base

Actual flat base change identifies each localization of the section algebra
with sections of the localized family. The proved local-family theorem gives
finite projectivity and étaleness there. Localization detects projectivity
and the vanishing of differentials for the original section algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- The original global-section map of a proper flat geometrically reduced
family over a Noetherian affine base is finite étale. The base is not assumed
local or reduced. -/
theorem finite_etale_appTop_of_proper_flat_geometricallyReduced_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [GeometricallyReduced f] : f.appTop.hom.Finite ∧ f.appTop.hom.Etale := by
  have hFinite : f.appTop.hom.Finite :=
    finite_appTop_of_isProper_of_isNoetherianRing f
  let hRΓ : Algebra R Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  have hfin : Module.Finite R Γ(X, ⊤) :=
    hFinite.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.surjective)
  have hfp : Module.FinitePresentation R Γ(X, ⊤) :=
    Module.finitePresentation_of_finite R Γ(X, ⊤)
  have hLocal : ∀ (p : Ideal R) [p.IsMaximal],
      Module.Projective (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Γ(X, ⊤)) ∧
        Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Γ(X, ⊤)) := by
    intro p hp
    let S := Localization.AtPrime p
    let q := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let fS := pullback.snd f q
    let hSΓ : Algebra S Γ(pullback f q, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ fS.appTop).hom.toAlgebra
    have hApp : fS.appTop = fS.appLE ⊤ ⊤ le_top := fS.app_eq_appLE
    have hAlgebra : Scheme.TwoAffineOpenCover.algebraOfHom fS ⊤ = hSΓ := by
      change (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
        fS.appLE ⊤ ⊤ le_top).hom.toAlgebra) = _
      rw [← hApp]
    let P (a : Algebra S Γ(pullback f q, ⊤)) : Prop :=
      let : Algebra S Γ(pullback f q, ⊤) := a
      Module.Projective S Γ(pullback f q, ⊤) ∧ Algebra.Etale S Γ(pullback f q, ⊤)
    have hSource : P (Scheme.TwoAffineOpenCover.algebraOfHom fS ⊤) :=
      ⟨(finite_projective_sectionAlgebra_and_baseChange_local fS).1.2,
        (finite_etale_sectionAlgebra_of_proper_flat_geometricallyReduced_local fS).2⟩
    have hTarget : P hSΓ := (congrArg P hAlgebra).mp hSource
    have hProjective : Module.Projective S Γ(pullback f q, ⊤) := hTarget.1
    have hEtale : Algebra.Etale S Γ(pullback f q, ⊤) := hTarget.2
    let e : S ⊗[R] Γ(X, ⊤) ≃ₐ[S] Γ(pullback f q, ⊤) :=
      specPullbackSectionsTensorEquiv (A := S) f
    exact ⟨Module.Projective.of_equiv e.symm.toLinearEquiv, Algebra.Etale.of_equiv e.symm⟩
  have hProjective : Module.Projective R Γ(X, ⊤) := by
    apply Module.projective_of_localization_maximal
    intro p hp
    have h := (hLocal p).1
    exact Module.Projective.of_equiv
      (LocalizedModule.equivTensorProduct p.primeCompl Γ(X, ⊤)).symm
  have hEtale : Algebra.Etale R Γ(X, ⊤) :=
    Algebra.etale_of_finite_projective_of_etale_localizations R Γ(X, ⊤)
      (fun p _ => (hLocal p).2)
  exact ⟨hFinite, (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv f.appTop).mp hEtale⟩

end AlgebraicGeometry
