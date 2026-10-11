/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.LocalCohomologyProjectiveDimension
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceDisconnectedReduction

/-!
# Local-cohomology inputs from a disconnected punctured hypersurface

The component ideals produced by a separation have radical intersection equal
to the principal support and radical sum equal to the maximal ideal.  This file
turns those equalities into the two support identifications used by the
local-cohomology Mayer--Vietoris argument.  In particular, the intersection
term vanishes in every degree at least two when the hypersurface parameter is
regular.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- If the punctured principal hypersurface is disconnected, its two radical
component ideals give a zero intersection-support local-cohomology term and a
sum-support term canonically isomorphic to maximal-ideal local cohomology.

These are the outer and middle support terms in the Mayer--Vietoris
connectedness argument; all of them are produced from the separation rather
than assumed. -/
theorem exists_localCohomologyMayerVietorisInputs_of_not_connectedSpace
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
        Ideal.span {x} ≤ a ∧ Ideal.span {x} ≤ b ∧
        a ≠ ⊤ ∧ b ≠ ⊤ ∧
        a ≠ maximalIdeal C ∧ b ≠ maximalIdeal C ∧
        a.IsRadical ∧ b.IsRadical ∧
        a ⊓ b = (Ideal.span {x}).radical ∧
        (a ⊔ b).radical = maximalIdeal C ∧
        IsZero ((localCohomology (a ⊓ b) i).obj M) ∧
        Nonempty
          (((localCohomology (a ⊔ b) i).obj M) ≅
            ((localCohomology (maximalIdeal C) i).obj M)) := by
  let D := C ⧸ Ideal.span {x}
  let : Nontrivial D :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing D :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  intro hnot
  obtain ⟨a, b, hxa, hxb, ha, hb, hamax, hbmax,
      haRadical, hbRadical, hinf, hsup⟩ :=
    exists_radical_nonmaximal_ambient_componentIntersectionIdeals_of_not_connectedSpace
      hdim x hx hnot
  have hinfRadical : (a ⊓ b).radical = (Ideal.span {x}).radical := by
    rw [(haRadical.inf hbRadical).radical]
    exact hinf
  have hzeroSpan :
      IsZero ((localCohomology (Ideal.span {x}) i).obj M) :=
    EtaleFundamentalGroups.localCohomology_span_singleton_isZero_of_isSMulRegular
      x hxreg hx M i hi
  have hzeroInf : IsZero ((localCohomology (a ⊓ b) i).obj M) :=
    IsZero.of_iso hzeroSpan
      ((localCohomology.isoOfSameRadical hinfRadical i).app M)
  have hmaxRadical : (maximalIdeal C).radical = maximalIdeal C :=
    (maximalIdeal.isMaximal C).isPrime.isRadical.radical
  have hsupRadical :
      (a ⊔ b).radical = (maximalIdeal C).radical :=
    hsup.trans hmaxRadical.symm
  exact
    ⟨a, b, hxa, hxb, ha, hb, hamax, hbmax, haRadical, hbRadical,
      hinf, hsup, hzeroInf,
      ⟨(localCohomology.isoOfSameRadical hsupRadical i).app M⟩⟩

end AlgebraicGeometry.FiniteEtale

end
