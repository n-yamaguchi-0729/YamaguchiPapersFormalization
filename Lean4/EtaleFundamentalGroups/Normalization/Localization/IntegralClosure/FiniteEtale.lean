/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.StalkMap
import EtaleFundamentalGroups.Purity.FiniteEtaleFromBoundaryStalks

/-!
# Finite etaleness of a relative normalization from affine charts

The standard affine open cover of a relative normalization is built from
integral closures.  This file turns formal etaleness of the corresponding
prime-local algebra maps into finite etaleness of the actual global
normalization morphism.  A boundary form allows the local calculation to be
restricted to points outside an open locus where etaleness is already known.
-/

noncomputable section

namespace EtaleFundamentalGroups

open CategoryTheory
open AlgebraicGeometry

universe u

/-- A finite relative normalization is finite etale if the prime-local map
on every affine integral-closure chart is formally etale. -/
theorem isFiniteEtale_fromNormalization_of_chartPrimeLocalizations
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsLocallyNoetherian Y]
    [IsFinite f.fromNormalization]
    (hlocal :
      ∀ (U : Y.Opens) (_hU : IsAffineOpen U)
        (Q : PrimeSpectrum
          (letI := (f.app U).hom.toAlgebra
           integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))),
        letI := (f.app U).hom.toAlgebra
        let C := integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
        let φ : Γ(Y, U) →+* C := algebraMap Γ(Y, U) C
        (Localization.localRingHom
          (Q.comap φ).asIdeal Q.asIdeal φ rfl).FormallyEtale) :
    IsFiniteEtale f.fromNormalization := by
  apply isFiniteEtale_of_isFinite_of_stalkMap_formallyEtale
    f.fromNormalization
  intro y
  obtain ⟨U, Q, hQ⟩ := f.normalizationOpenCover.exists_eq y
  subst y
  exact
    (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (normalizationChartStalkPrimeLocalizationArrowIso f U.2 Q)).mpr
        (hlocal U.1 U.2 Q)

/-- Boundary form of the affine-chart criterion.  If the finite relative
normalization is already etale over an open `V`, it suffices to check the
prime-local integral-closure maps at chart points mapping outside `V`. -/
theorem
    isFiniteEtale_fromNormalization_of_restrict_etale_of_boundary_chartPrimeLocalizations
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsLocallyNoetherian Y]
    [IsFinite f.fromNormalization]
    (V : Y.Opens) (hV : Etale (f.fromNormalization ∣_ V))
    (hlocal :
      ∀ (U : Y.Opens) (hU : IsAffineOpen U)
        (Q : PrimeSpectrum
          (letI := (f.app U).hom.toAlgebra
           integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))),
        f.fromNormalization
            (f.normalizationOpenCover.f ⟨U, hU⟩ Q) ∉ V →
        letI := (f.app U).hom.toAlgebra
        let C := integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
        let φ : Γ(Y, U) →+* C := algebraMap Γ(Y, U) C
        (Localization.localRingHom
          (Q.comap φ).asIdeal Q.asIdeal φ rfl).FormallyEtale) :
    IsFiniteEtale f.fromNormalization := by
  apply
    isFiniteEtale_of_isFinite_of_restrict_etale_of_boundary_stalkMap_formallyEtale
      f.fromNormalization V hV
  intro y hy
  obtain ⟨U, Q, hQ⟩ := f.normalizationOpenCover.exists_eq y
  subst y
  exact
    (RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (normalizationChartStalkPrimeLocalizationArrowIso f U.2 Q)).mpr
        (hlocal U.1 U.2 Q hy)

end EtaleFundamentalGroups

end
