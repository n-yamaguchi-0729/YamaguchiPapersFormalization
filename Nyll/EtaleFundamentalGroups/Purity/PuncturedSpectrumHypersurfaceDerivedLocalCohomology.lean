/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyMayerVietoris
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyProjectiveDimension
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyRadical
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceDisconnectedReduction

/-!
# Derived local cohomology of a disconnected punctured hypersurface

A clopen separation of a punctured principal hypersurface produces two
radical nonmaximal component ideals.  Their intersection has the radical of
the principal support, while their supremum has maximal radical.  Principal
support vanishing and the derived Mayer--Vietoris sequence then reduce the
connectedness contradiction to top-degree vanishing for the two nonmaximal
component supports.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A disconnected punctured principal hypersurface supplies the derived
local-cohomology support identifications used in Mayer--Vietoris. -/
theorem exists_derivedLocalCohomologyMayerVietorisInputs_of_not_connectedSpace
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) (hxreg : IsSMulRegular C x)
    (M : ModuleCat.{u} C) (i : ℕ) (hi : 2 ≤ i) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ¬ ConnectedSpace
        (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) →
      ∃ a b : Ideal C,
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a.IsRadical ∧ b.IsRadical ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C ∧
        IsZero (EtaleFundamentalGroups.derivedLocalCohomology
          (a ⊓ b) M i) ∧
        Nonempty
          (EtaleFundamentalGroups.derivedLocalCohomology
              (a ⊔ b) M i ≅
            EtaleFundamentalGroups.derivedLocalCohomology
              (maximalIdeal C) M i) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, _hxa, _hxb, _ha, _hb, hamax, hbmax,
      haRadical, hbRadical, hinf, hsup⟩ :=
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace
      hdim x hx hnot
  have hinfRadical :
      (a ⊓ b).radical = (Ideal.span {x}).radical := by
    rw [(haRadical.inf hbRadical).radical]
    exact hinf
  have hzeroSpan :
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (Ideal.span {x}) M i) :=
    EtaleFundamentalGroups.derivedLocalCohomology_span_singleton_isZero_of_isSMulRegular
      x hxreg hx M i hi
  have hzeroInf :
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (a ⊓ b) M i) :=
    hzeroSpan.of_iso
      (EtaleFundamentalGroups.derivedLocalCohomologyIsoOfSameRadical
        hinfRadical M i)
  have hmaxRadical : (maximalIdeal C).radical = maximalIdeal C :=
    (maximalIdeal.isMaximal C).isPrime.isRadical.radical
  have hsupRadical :
      (a ⊔ b).radical = (maximalIdeal C).radical :=
    hsup.trans hmaxRadical.symm
  exact ⟨a, b, hamax, hbmax, haRadical, hbRadical, hinf, hsup,
    hzeroInf,
    ⟨EtaleFundamentalGroups.derivedLocalCohomologyIsoOfSameRadical
      hsupRadical M i⟩⟩

/-- If top-degree derived local cohomology vanishes for every radical
nonmaximal support, disconnectedness of a punctured regular hypersurface
forces maximal-support local cohomology to vanish in the next degree. -/
theorem derivedLocalCohomology_maximal_isZero_of_not_connectedSpace
    {C : Type u} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C)
    (x : C) (hx : x ∈ maximalIdeal C) (hxreg : IsSMulRegular C x)
    (M : ModuleCat.{u} C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)
    (hn₀ : 2 ≤ n₀)
    (hNonmax : ∀ I : Ideal C, I.IsRadical → I ≠ maximalIdeal C →
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology I M n₁)) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ¬ ConnectedSpace
        (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) →
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (maximalIdeal C) M n₁) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, hamax, hbmax, haRadical, hbRadical, _hinf, hsup,
      hzeroInf, _hsupIso⟩ :=
    exists_derivedLocalCohomologyMayerVietorisInputs_of_not_connectedSpace
      hdim x hx hxreg M n₀ hn₀ hnot
  have hzeroSup :
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology
        (a ⊔ b) M n₁) :=
    EtaleFundamentalGroups.derivedLocalCohomology_sup_isZero_of_mayerVietoris
      a b M n₀ n₁ h hzeroInf
        (hNonmax a haRadical hamax)
        (hNonmax b hbRadical hbmax)
  have hmaxRadical : (maximalIdeal C).radical = maximalIdeal C :=
    (maximalIdeal.isMaximal C).isPrime.isRadical.radical
  have hsupRadical :
      (a ⊔ b).radical = (maximalIdeal C).radical :=
    hsup.trans hmaxRadical.symm
  exact hzeroSup.of_iso
    (EtaleFundamentalGroups.derivedLocalCohomologyIsoOfSameRadical
      hsupRadical M n₁).symm

end AlgebraicGeometry.FiniteEtale

end
