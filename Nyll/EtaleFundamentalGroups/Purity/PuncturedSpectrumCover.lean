/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Noetherian.Defs

/-!
# A finite affine cover of a punctured local spectrum

For a Noetherian local ring, the maximal ideal has a finite generating set.
The corresponding principal opens cover the complement of the closed point.
This file constructs that cover on the actual punctured spectrum, proves its
charts affine, and identifies every chart with the spectrum of the canonical
away localization.
-/

noncomputable section

open IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The finite index type of the chosen minimal-cardinality generating set of
the maximal ideal. -/
abbrev puncturedSpectrumGeneratorIndex :=
  (maximalIdeal R).generators

noncomputable instance puncturedSpectrumGeneratorIndex_finite :
    Finite (puncturedSpectrumGeneratorIndex R) :=
  Set.finite_coe_iff.mpr
    (Submodule.FG.finite_generators
      ((maximalIdeal R).fg_of_isNoetherianRing :
        (maximalIdeal R : Submodule R R).FG))

/-- A generator of the maximal ideal indexing a principal chart of the
punctured spectrum. -/
def puncturedSpectrumGenerator
    (i : puncturedSpectrumGeneratorIndex R) : R :=
  i.1

omit [IsNoetherianRing R] in
theorem puncturedSpectrumGenerator_mem_maximalIdeal
    (i : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumGenerator R i ∈ maximalIdeal R := by
  exact Submodule.FG.generators_mem (maximalIdeal R) i.2

/-- The ambient principal open associated to one chosen maximal-ideal
generator. -/
def puncturedSpectrumAmbientBasicOpen
    (i : puncturedSpectrumGeneratorIndex R) :
    (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R i)

/- Every chosen principal open avoids the closed point, hence lies in the
punctured-spectrum open. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientBasicOpen_le
    (i : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumAmbientBasicOpen R i ≤ puncturedSpectrumOpen R := by
  intro x hx
  change x ≠ closedPoint R
  intro hclosed
  subst x
  exact ((PrimeSpectrum.mem_basicOpen _ _).mp hx)
    (puncturedSpectrumGenerator_mem_maximalIdeal R i)

/- The principal opens indexed by the chosen generators cover precisely the
punctured open inside `Spec R`. -/
omit [IsNoetherianRing R] in
theorem iSup_puncturedSpectrumAmbientBasicOpen :
    (⨆ i : puncturedSpectrumGeneratorIndex R,
      puncturedSpectrumAmbientBasicOpen R i) =
        puncturedSpectrumOpen R := by
  apply le_antisymm
  · exact iSup_le fun i ↦ puncturedSpectrumAmbientBasicOpen_le R i
  · intro x hpunctured
    change x ≠ closedPoint R at hpunctured
    by_contra hcover
    have hgenerator_mem (i : puncturedSpectrumGeneratorIndex R) :
        puncturedSpectrumGenerator R i ∈ x.asIdeal := by
      by_contra hi
      apply hcover
      exact (le_iSup
        (fun i : puncturedSpectrumGeneratorIndex R ↦
          puncturedSpectrumAmbientBasicOpen R i) i)
        ((PrimeSpectrum.mem_basicOpen _ _).mpr hi)
    have hspan :
        Ideal.span (maximalIdeal R).generators = maximalIdeal R := by
      simpa only [Ideal.span] using (maximalIdeal R).span_generators
    have hmaximal_le : maximalIdeal R ≤ x.asIdeal := by
      rw [← hspan]
      exact Ideal.span_le.mpr fun f hf ↦ hgenerator_mem ⟨f, hf⟩
    have hx_le : x.asIdeal ≤ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal x.2.1
    apply hpunctured
    apply PrimeSpectrum.ext
    exact le_antisymm hx_le hmaximal_le

/-- One principal chart, now regarded as an open of the punctured spectrum. -/
def puncturedSpectrumBasicOpen
    (i : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrum R).Opens :=
  puncturedSpectrumInclusion R ⁻¹ᵁ
    puncturedSpectrumAmbientBasicOpen R i

/- The principal charts form a finite open cover of the punctured spectrum. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumBasicOpen_isOpenCover :
    IsOpenCover (puncturedSpectrumBasicOpen R) := by
  change (⨆ i, puncturedSpectrumInclusion R ⁻¹ᵁ
    puncturedSpectrumAmbientBasicOpen R i) = ⊤
  rw [← (puncturedSpectrumInclusion R).preimage_iSup,
    iSup_puncturedSpectrumAmbientBasicOpen]
  exact (puncturedSpectrumOpen R).ι_preimage_self

/-- A principal chart of the punctured spectrum is canonically the spectrum
of the localization obtained by inverting its indexing generator. -/
def puncturedSpectrumBasicOpenIsoSpecAway
    (i : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumBasicOpen R i).toScheme ≅
      Spec (.of (Localization.Away (puncturedSpectrumGenerator R i))) :=
  by
    change
      (((puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R i)).toScheme) ≅ _
    exact Opens.isoOfLE (puncturedSpectrumAmbientBasicOpen_le R i) ≪≫
      basicOpenIsoSpecAway (R := .of R) (puncturedSpectrumGenerator R i)

/- Each principal chart of the punctured spectrum is affine. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumBasicOpen_isAffine
    (i : puncturedSpectrumGeneratorIndex R) :
    IsAffineOpen (puncturedSpectrumBasicOpen R i) := by
  exact IsAffine.of_isIso (puncturedSpectrumBasicOpenIsoSpecAway R i).hom

/-- The finite open cover whose members are the actual principal charts. -/
def puncturedSpectrumOpenCover : (puncturedSpectrum R).OpenCover :=
  (puncturedSpectrum R).openCoverOfIsOpenCover
    (puncturedSpectrumBasicOpen R)
    (puncturedSpectrumBasicOpen_isOpenCover R)

/-- The same finite cover packaged as an affine open cover. -/
def puncturedSpectrumAffineOpenCover :
    (puncturedSpectrum R).AffineOpenCover :=
  AffineOpenCover.ofIsOpenCover
    (puncturedSpectrumBasicOpen R)
    (puncturedSpectrumBasicOpen_isOpenCover R)
    (puncturedSpectrumBasicOpen_isAffine R)

/-- The punctured spectrum of a Noetherian local ring is quasi-compact.  The
proof uses the finite principal affine cover constructed above. -/
theorem compactSpace_puncturedSpectrum : CompactSpace (puncturedSpectrum R) := by
  let : Finite (puncturedSpectrumOpenCover R).I₀ := by
    change Finite (puncturedSpectrumGeneratorIndex R)
    infer_instance
  let (i : (puncturedSpectrumOpenCover R).I₀) :
      IsAffine ((puncturedSpectrumOpenCover R).X i) := by
    change IsAffine ((puncturedSpectrumBasicOpen R i).toScheme)
    exact puncturedSpectrumBasicOpen_isAffine R i
  exact OpenCover.compactSpace (puncturedSpectrumOpenCover R)

end AlgebraicGeometry.Scheme

end
