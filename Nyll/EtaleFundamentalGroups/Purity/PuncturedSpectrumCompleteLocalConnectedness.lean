/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompleteLocalOfListFrontier
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationComplete
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyGeneratorCountDomain
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHartshorneLichtenbaumGeometry
import Nyll.EtaleFundamentalGroups.Purity.HartshorneLichtenbaumVanishing
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologySupportDimensionNonvanishing
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Connected finite-generator quotients in complete local domains

This proves the Grothendieck connectedness input used by the local purity
induction from Hartshorne--Lichtenbaum vanishing and top local-cohomology
nonvanishing. The Mayer--Vietoris argument applies to every finite list of
generators, with no regularity assumption on that list.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Hartshorne--Lichtenbaum vanishing and top local-cohomology nonvanishing
imply connectedness for a quotient by any finite list of generators.  The
generator-count vanishing theorem supplies the intersection term in the
Mayer--Vietoris sequence; no regularity assumption on the list is needed. -/
theorem connectedSpace_puncturedSpectrum_quotient_ofList_of_topLocalCohomology
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C]
    (d : ℕ) (hdim : ringKrullDim C = (d : WithBot ℕ∞))
    (xs : List C) (hxs : Ideal.ofList xs ≤ maximalIdeal C)
    (hcodim : xs.length + 2 ≤ d)
    (hNonmax : ∀ I : Ideal C, I.IsRadical → I ≠ maximalIdeal C →
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology I
        (ModuleCat.of C C) d))
    (hTop : ¬ IsZero (EtaleFundamentalGroups.derivedLocalCohomology
      (maximalIdeal C) (ModuleCat.of C C) d)) :
    letI : Nontrivial (C ⧸ Ideal.ofList xs) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hxs
    letI : IsLocalRing (C ⧸ Ideal.ofList xs) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.ofList xs))
        Ideal.Quotient.mk_surjective
    ConnectedSpace
      (Scheme.puncturedSpectrum (C ⧸ Ideal.ofList xs)) := by
  let : Nontrivial (C ⧸ Ideal.ofList xs) :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hxs
  let : IsLocalRing (C ⧸ Ideal.ofList xs) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.ofList xs))
      Ideal.Quotient.mk_surjective
  have hdimBound :
      ((((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C) := by
    rw [hdim]
    exact_mod_cast hcodim
  by_contra hconnected
  apply hTop
  obtain ⟨a, b, _hIa, _hIb, _ha, _hb, hamax, hbmax,
      haRadical, hbRadical, hinf, hsup⟩ :=
    (
exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace_quotient_ofList
      (Ideal.ofList xs) hxs xs rfl hdimBound hconnected)
  have hzeroList :
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (Ideal.ofList xs) (ModuleCat.of C C) (d - 1)) :=
    EtaleFundamentalGroups.derivedLocalCohomology_ofList_isZero_of_isDomain
      xs (ModuleCat.of C C) (d - 1) (by omega)
  have hinfRadical :
      (a ⊓ b).radical = (Ideal.ofList xs).radical := by
    rw [hinf, Ideal.radical_idem]
  have hzeroInf :
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (a ⊓ b) (ModuleCat.of C C) (d - 1)) :=
    hzeroList.of_iso
      (EtaleFundamentalGroups.derivedLocalCohomologyIsoOfSameRadical
        hinfRadical (ModuleCat.of C C) (d - 1))
  have hzeroSup :
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (a ⊔ b) (ModuleCat.of C C) d) :=
    EtaleFundamentalGroups.derivedLocalCohomology_sup_isZero_of_mayerVietoris
      a b (ModuleCat.of C C) (d - 1) d (by omega) hzeroInf
        (hNonmax a haRadical hamax) (hNonmax b hbRadical hbmax)
  have hmaxRadical : (maximalIdeal C).radical = maximalIdeal C :=
    (maximalIdeal.isMaximal C).isPrime.isRadical.radical
  have hsupRadical :
      (a ⊔ b).radical = (maximalIdeal C).radical :=
    hsup.trans hmaxRadical.symm
  exact hzeroSup.of_iso
    (EtaleFundamentalGroups.derivedLocalCohomologyIsoOfSameRadical
      hsupRadical (ModuleCat.of C C) d).symm

/-- Finite-dimensional form of
`connectedSpace_puncturedSpectrum_quotient_ofList_of_topLocalCohomology`.
The natural-number dimension is extracted from the Noetherian local ring,
so callers supply only the Hartshorne--Lichtenbaum vanishing source and
Grothendieck top-nonvanishing source, each stated uniformly for a natural
representative of the Krull dimension. -/
theorem connectedSpace_puncturedSpectrum_quotient_ofList_of_localCohomologySources
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C]
    (xs : List C) (hxs : Ideal.ofList xs ≤ maximalIdeal C)
    (hdim :
      ((((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C))
    (hHL : ∀ (d : ℕ), ringKrullDim C = (d : WithBot ℕ∞) →
      ∀ J : Ideal C, J.IsRadical → J ≠ ⊤ → J ≠ maximalIdeal C →
        IsZero (EtaleFundamentalGroups.derivedLocalCohomology J
          (ModuleCat.of C C) d))
    (hTop : ∀ (d : ℕ), ringKrullDim C = (d : WithBot ℕ∞) →
      ¬ IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (maximalIdeal C) (ModuleCat.of C C) d)) :
    letI : Nontrivial (C ⧸ Ideal.ofList xs) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hxs
    letI : IsLocalRing (C ⧸ Ideal.ofList xs) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.ofList xs))
        Ideal.Quotient.mk_surjective
    ConnectedSpace
      (Scheme.puncturedSpectrum (C ⧸ Ideal.ofList xs)) := by
  obtain ⟨d, hdimNat⟩ :=
    exists_nat_ringKrullDim_eq_of_finiteRingKrullDim (R := C)
  have hcodim : xs.length + 2 ≤ d := by
    rw [hdimNat] at hdim
    exact_mod_cast hdim
  apply
    connectedSpace_puncturedSpectrum_quotient_ofList_of_topLocalCohomology
      d hdimNat xs hxs hcodim
  · intro J hJradical hJnonmax
    by_cases hJproper : J = ⊤
    · subst J
      exact EtaleFundamentalGroups.derivedLocalCohomology_top_isZero
        (ModuleCat.of C C) d
    · exact hHL d hdimNat J hJradical hJproper hJnonmax
  · exact hTop d hdimNat

/-- If an ideal in a complete Noetherian local domain is generated by `r`
elements and the ambient dimension is at least `r + 2`, then the punctured
spectrum of the quotient is connected.

No regularity assumption on the generators is made.  This is essential
after mapping a regular system from the base into a finite normalization. -/
theorem connectedSpace_puncturedSpectrum_quotient_ofList_of_completeLocalDomain
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C]
    (I : Ideal C) (hI : I ≤ maximalIdeal C)
    (xs : List C) (hxs : I = Ideal.ofList xs)
    (hdim :
      ((((xs.length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)) :
    letI : Nontrivial (C ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hI
    letI : IsLocalRing (C ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    ConnectedSpace
      (Scheme.puncturedSpectrum (C ⧸ I)) := by
  subst I
  apply connectedSpace_puncturedSpectrum_quotient_ofList_of_localCohomologySources xs hI hdim
  · intro d hd J hJradical hJproper hJnonmax
    have hcodim : xs.length + 2 ≤ d := by
      have h := hdim
      rw [hd] at h
      exact_mod_cast h
    cases d with
    | zero => omega
    | succ d =>
        have hJrad : J.radical ≠ maximalIdeal C := by
          simpa only [hJradical.radical] using hJnonmax
        exact (open _root_.EtaleFundamentalGroups.Purity in
          derivedLocalCohomology_isZero_of_completeLocalDomain_of_radical_ne
            J hJproper hJrad d hd)
  · intro d hd
    exact EtaleFundamentalGroups.derivedLocalCohomology_maximalIdeal_not_isZero_of_supportDim_eq
      (ModuleCat.of C C) d ((Module.supportDim_self_eq_ringKrullDim C).trans hd)

/-- A nonzero principal hypersurface in a complete Noetherian local domain of
dimension at least three has connected punctured spectrum. -/
theorem connectedSpace_puncturedSpectrum_quotient_span_singleton_of_completeLocalDomain
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) (_hx0 : x ≠ 0) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ConnectedSpace
      (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) := by
  have hI : Ideal.span {x} ≤ maximalIdeal C :=
    (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  have hdim' :
      (((([x].length + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim C) := by
    simpa using hdim
  exact
    connectedSpace_puncturedSpectrum_quotient_ofList_of_completeLocalDomain
      (Ideal.span {x}) hI [x] (Ideal.ofList_singleton x).symm hdim'

end AlgebraicGeometry.FiniteEtale

end
