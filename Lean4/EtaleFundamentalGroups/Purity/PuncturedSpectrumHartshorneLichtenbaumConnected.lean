/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceDerivedLocalCohomology

/-!
# Connected hypersurfaces from top local cohomology

This file closes the formal Mayer--Vietoris argument at the
Hartshorne--Lichtenbaum frontier.  Vanishing in top degree for every radical
nonmaximal support, together with nonvanishing for maximal support, forces the
punctured spectrum of a regular principal hypersurface to be connected.

The two cohomological hypotheses are deliberately stated separately.  They
are the Hartshorne--Lichtenbaum vanishing theorem and Grothendieck's top
nonvanishing theorem, respectively; neither is replaced by the desired
connectedness conclusion.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Hartshorne--Lichtenbaum vanishing and top local-cohomology nonvanishing
imply connectedness of a punctured principal hypersurface in dimension at
least three. -/
theorem connectedSpace_puncturedSpectrum_quotient_span_singleton_of_topLocalCohomology
    {C : Type u} [CommRing C] [IsDomain C] [IsLocalRing C]
    [IsNoetherianRing C]
    (d : ℕ) (hdim : ringKrullDim C = (d : WithBot ℕ∞))
    (hd : 3 ≤ d)
    (x : C) (hx : x ∈ maximalIdeal C) (hxreg : IsSMulRegular C x)
    (hNonmax : ∀ I : Ideal C, I.IsRadical → I ≠ maximalIdeal C →
      IsZero (EtaleFundamentalGroups.derivedLocalCohomology I
        (ModuleCat.of C C) d))
    (hTop : ¬ IsZero (EtaleFundamentalGroups.derivedLocalCohomology
      (maximalIdeal C) (ModuleCat.of C C) d)) :
    letI : Nontrivial (C ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
          (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
    letI : IsLocalRing (C ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    ConnectedSpace
      (Scheme.puncturedSpectrum (C ⧸ Ideal.span {x})) := by
  let : Nontrivial (C ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top <|
        (maximalIdeal C).span_singleton_le_iff_mem.mpr hx
  let : IsLocalRing (C ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective
  have hdimThree : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C := by
    rw [hdim]
    exact_mod_cast hd
  have hdPred : 2 ≤ d - 1 := by omega
  have hsucc : 1 + (d - 1) = d := by omega
  by_contra hconnected
  apply hTop
  exact derivedLocalCohomology_maximal_isZero_of_not_connectedSpace
    hdimThree x hx hxreg (ModuleCat.of C C) (d - 1) d hsucc hdPred
      hNonmax hconnected

end AlgebraicGeometry.FiniteEtale

end
