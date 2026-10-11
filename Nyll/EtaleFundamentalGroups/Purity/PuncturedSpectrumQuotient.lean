/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Hypersurface and quotient maps between punctured spectra

An ideal contained in the maximal ideal of a local ring defines a closed
subscheme whose unique closed point maps to the closed point of the ambient
spectrum.  Hence the quotient morphism restricts canonically to the two
punctured spectra.  This is the geometric restriction map used in induction
on the dimension of a regular local ring.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

local instance finiteEtaleHasPullbacksAlongPuncturedSpectrumQuotient
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongPuncturedSpectrumQuotient
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable (R : Type u) [CommRing R] [IsLocalRing R]

private theorem quotientIdeal_ne_top
    (I : Ideal R) (hI : I ≤ maximalIdeal R) : I ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI

/-- The inverse image of the ambient puncture under a local quotient map is
exactly the puncture of the quotient. -/
theorem preimage_puncturedSpectrumOpen_quotient
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ⁻¹ᵁ
        puncturedSpectrumOpen R =
      puncturedSpectrumOpen (R ⧸ I) := by
  let : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let q : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : IsClosedImmersion q := by
    dsimp only [q]
    exact IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective
  have hqClosed :
      q (closedPoint (CommRingCat.of (R ⧸ I))) =
        closedPoint (CommRingCat.of R) := by
    exact Spec_closedPoint
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change q x ∈ puncturedSpectrumOpen R ↔
    x ∈ puncturedSpectrumOpen (R ⧸ I)
  constructor
  · intro hx
    apply (mem_puncturedSpectrumOpen_iff (R ⧸ I) x).2
    intro hclosed
    have hx' : q x ≠ closedPoint (CommRingCat.of R) :=
      (mem_puncturedSpectrumOpen_iff R (q x)).1 hx
    apply hx'
    rw [hclosed]
    exact hqClosed
  · intro hx
    apply (mem_puncturedSpectrumOpen_iff R (q x)).2
    intro hclosed
    have hx' : x ≠ closedPoint (CommRingCat.of (R ⧸ I)) :=
      (mem_puncturedSpectrumOpen_iff (R ⧸ I) x).1 hx
    apply hx'
    apply q.isEmbedding.injective
    rw [hclosed]
    exact hqClosed.symm

/-- The closed immersion `Spec (R ⧸ I) ⟶ Spec R` restricted to the
punctured spectra, for an ideal contained in the maximal ideal. -/
noncomputable def puncturedSpectrumQuotientMorphism
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    puncturedSpectrum (R ⧸ I) ⟶ puncturedSpectrum R := by
  letI : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let q : Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  letI : IsClosedImmersion q := by
    dsimp only [q]
    exact IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective
  let jI := puncturedSpectrumInclusion (R ⧸ I)
  let j := puncturedSpectrumInclusion R
  letI : IsOpenImmersion j := by
    dsimp only [j, puncturedSpectrumInclusion]
    infer_instance
  apply IsOpenImmersion.lift j (jI ≫ q)
  rintro _ ⟨y, rfl⟩
  have hqClosed :
      q (closedPoint (CommRingCat.of (R ⧸ I))) =
        closedPoint (CommRingCat.of R) := by
    exact Spec_closedPoint
  have hnotClosed :
      q (jI y) ≠ closedPoint (CommRingCat.of R) := by
    intro hclosed
    have hyClosed :
        jI y = closedPoint (CommRingCat.of (R ⧸ I)) := by
      apply q.isEmbedding.injective
      rw [hclosed, hqClosed]
    exact
      ((mem_puncturedSpectrumOpen_iff (R ⧸ I) (jI y)).mp y.property)
        hyClosed
  let z : puncturedSpectrum R :=
    ⟨q (jI y), (mem_puncturedSpectrumOpen_iff R _).mpr hnotClosed⟩
  exact ⟨z, rfl⟩

/-- The punctured quotient map commutes with the two canonical inclusions
into the full affine spectra. -/
@[reassoc (attr := simp)]
theorem puncturedSpectrumQuotientMorphism_comp_inclusion
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    puncturedSpectrumQuotientMorphism R I hI ≫
        puncturedSpectrumInclusion R =
      puncturedSpectrumInclusion (R ⧸ I) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  let : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsOpenImmersion (puncturedSpectrumInclusion R) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  unfold puncturedSpectrumQuotientMorphism
  exact IsOpenImmersion.lift_fac _ _ _

/-- The square formed by a local quotient morphism and the two punctured
spectrum inclusions is cartesian. -/
theorem puncturedSpectrumQuotientMorphism_isPullback
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    IsPullback
      (puncturedSpectrumQuotientMorphism R I hI)
      (puncturedSpectrumInclusion (R ⧸ I))
      (puncturedSpectrumInclusion R)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  let : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsOpenImmersion (puncturedSpectrumInclusion R) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  let : IsOpenImmersion (puncturedSpectrumInclusion (R ⧸ I)) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  apply IsOpenImmersion.isPullback
  · exact (puncturedSpectrumQuotientMorphism_comp_inclusion R I hI).symm
  · simpa only [puncturedSpectrumInclusion, Opens.opensRange_ι] using
      preimage_puncturedSpectrumOpen_quotient R I hI

/-- Restricting a finite-etale cover first to the ambient puncture and then
to the quotient puncture agrees, naturally, with first taking the quotient
base change and then removing its closed point. -/
noncomputable def puncturedSpectrumQuotientPullbackIso
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective
    AlgebraicGeometry.FiniteEtale.pullback
          (puncturedSpectrumInclusion R) ⋙
        AlgebraicGeometry.FiniteEtale.pullback
          (puncturedSpectrumQuotientMorphism R I hI) ≅
      AlgebraicGeometry.FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⋙
        AlgebraicGeometry.FiniteEtale.pullback
          (puncturedSpectrumInclusion (R ⧸ I)) := by
  letI : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (quotientIdeal_ne_top R I hI)
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumQuotientMorphism R I hI)
      (puncturedSpectrumInclusion R)).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (puncturedSpectrumQuotientMorphism_comp_inclusion R I hI) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumInclusion (R ⧸ I))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

end AlgebraicGeometry.Scheme
