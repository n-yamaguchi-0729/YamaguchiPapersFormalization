/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletion
import EtaleFundamentalGroups.Purity.PuncturedSpectrumQuotient

/-!
# Punctured spectra under maximal-adic completion

A local ring map which carries the source maximal ideal onto the target
maximal ideal pulls the punctured spectrum back to the target punctured
spectrum.  This file packages the resulting cartesian square and its
finite-etale pullback comparison.

For maximal-adic completion, purity of the completed ring therefore extends
every cover from the original puncture after completion.  Descending that
completed extension is a separate algebraization problem; it is not assumed
here.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

local instance finiteEtaleHasPullbacksAlongPuncturedSpectrumCompletionDescentFrontier
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongPuncturedSpectrumCompletionDescentFrontier
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- A local ring map which maps the maximal ideal onto the maximal ideal
pulls the punctured open back to the punctured open. -/
theorem preimage_puncturedSpectrumOpen_of_map_maximalIdeal_eq
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hmax : (maximalIdeal R).map f = maximalIdeal S) :
    Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ puncturedSpectrumOpen R =
      puncturedSpectrumOpen S := by
  let q : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom f)
  have hqClosed :
      q (closedPoint (CommRingCat.of S)) =
        closedPoint (CommRingCat.of R) := by
    exact Spec_closedPoint
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change q x ∈ puncturedSpectrumOpen R ↔
    x ∈ puncturedSpectrumOpen S
  constructor
  · intro hx
    apply (mem_puncturedSpectrumOpen_iff S x).2
    intro hclosed
    exact ((mem_puncturedSpectrumOpen_iff R (q x)).1 hx) <| by
      rw [hclosed]
      exact hqClosed
  · intro hx
    apply (mem_puncturedSpectrumOpen_iff R (q x)).2
    intro hclosed
    apply ((mem_puncturedSpectrumOpen_iff S x).1 hx)
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal x.2.1
    · change maximalIdeal S ≤ x.1
      rw [← hmax, Ideal.map_le_iff_le_comap]
      have hcomap := congrArg PrimeSpectrum.asIdeal hclosed
      change x.1.comap f = maximalIdeal R at hcomap
      exact hcomap.ge

/-- The morphism between punctured spectra induced by a local ring map whose
maximal ideal extension is the target maximal ideal. -/
noncomputable def puncturedSpectrumMorphismOfMapMaximalIdealEq
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hmax : (maximalIdeal R).map f = maximalIdeal S) :
    puncturedSpectrum S ⟶ puncturedSpectrum R :=
  (Spec.map (CommRingCat.ofHom f)).resLE
    (puncturedSpectrumOpen R) (puncturedSpectrumOpen S)
    (preimage_puncturedSpectrumOpen_of_map_maximalIdeal_eq f hmax).ge

/-- The punctured-spectrum morphism commutes with the two canonical open
immersions into affine spectra. -/
@[reassoc (attr := simp)]
theorem puncturedSpectrumMorphismOfMapMaximalIdealEq_comp_inclusion
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hmax : (maximalIdeal R).map f = maximalIdeal S) :
    puncturedSpectrumMorphismOfMapMaximalIdealEq f hmax ≫
        puncturedSpectrumInclusion R =
      puncturedSpectrumInclusion S ≫
        Spec.map (CommRingCat.ofHom f) := by
  unfold puncturedSpectrumMorphismOfMapMaximalIdealEq
  exact Scheme.Hom.resLE_comp_ι _ _

/-- The square of a local affine morphism and the induced punctured-spectrum
morphism is cartesian when the maximal ideal is obtained by extension. -/
theorem puncturedSpectrumMorphismOfMapMaximalIdealEq_isPullback
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hmax : (maximalIdeal R).map f = maximalIdeal S) :
    IsPullback
      (puncturedSpectrumMorphismOfMapMaximalIdealEq f hmax)
      (puncturedSpectrumInclusion S)
      (puncturedSpectrumInclusion R)
      (Spec.map (CommRingCat.ofHom f)) := by
  let : IsOpenImmersion (puncturedSpectrumInclusion R) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  let : IsOpenImmersion (puncturedSpectrumInclusion S) := by
    dsimp only [puncturedSpectrumInclusion]
    infer_instance
  apply IsOpenImmersion.isPullback
  · exact
      (puncturedSpectrumMorphismOfMapMaximalIdealEq_comp_inclusion
        f hmax).symm
  · simpa only [puncturedSpectrumInclusion, Opens.opensRange_ι] using
      preimage_puncturedSpectrumOpen_of_map_maximalIdeal_eq f hmax

/-- Restriction to the puncture commutes naturally with base change along a
local map carrying the maximal ideal onto the maximal ideal. -/
noncomputable def puncturedSpectrumPullbackIsoOfMapMaximalIdealEq
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hmax : (maximalIdeal R).map f = maximalIdeal S) :
    AlgebraicGeometry.FiniteEtale.pullback
          (puncturedSpectrumInclusion R) ⋙
        AlgebraicGeometry.FiniteEtale.pullback
          (puncturedSpectrumMorphismOfMapMaximalIdealEq f hmax) ≅
      AlgebraicGeometry.FiniteEtale.pullback
          (Spec.map (CommRingCat.ofHom f)) ⋙
        AlgebraicGeometry.FiniteEtale.pullback
          (puncturedSpectrumInclusion S) := by
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumMorphismOfMapMaximalIdealEq f hmax)
      (puncturedSpectrumInclusion R)).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (puncturedSpectrumMorphismOfMapMaximalIdealEq_comp_inclusion
        f hmax) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumInclusion S)
      (Spec.map (CommRingCat.ofHom f))

/-- Purity on the target of a local map extends every cover of the source
puncture after base change to the target puncture. -/
theorem exists_extension_after_baseChange_of_hasPuncturedPurity
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hmax : (maximalIdeal R).map f = maximalIdeal S)
    (hpurity : AlgebraicGeometry.FiniteEtale.HasPuncturedPurity S)
    (Y : AlgebraicGeometry.FiniteEtale (puncturedSpectrum R)) :
    ∃ X : AlgebraicGeometry.FiniteEtale (Spec (.of S)),
      Nonempty
        ((AlgebraicGeometry.FiniteEtale.pullback
            (puncturedSpectrumInclusion S)).obj X ≅
          (AlgebraicGeometry.FiniteEtale.pullback
            (puncturedSpectrumMorphismOfMapMaximalIdealEq f hmax)).obj Y) := by
  exact
    (AlgebraicGeometry.FiniteEtale.hasPuncturedPurity_iff S).mp hpurity
      ((AlgebraicGeometry.FiniteEtale.pullback
        (puncturedSpectrumMorphismOfMapMaximalIdealEq f hmax)).obj Y)

end AlgebraicGeometry.Scheme

namespace EtaleFundamentalGroups

universe u

open AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The map from the puncture of the maximal-adic completion to the original
punctured spectrum. -/
noncomputable def maximalAdicCompletionPuncturedSpectrumMorphism
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Scheme.puncturedSpectrum (AdicCompletion (maximalIdeal R) R) ⟶
      Scheme.puncturedSpectrum R :=
  puncturedSpectrumMorphismOfMapMaximalIdealEq
    (algebraMap R (AdicCompletion (maximalIdeal R) R))
    AdicCompletion.maximalIdeal_eq_map.symm

/-- The maximal-adic completion square with the two punctured-spectrum
inclusions is cartesian. -/
theorem maximalAdicCompletionPuncturedSpectrumMorphism_isPullback
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsPullback
      (maximalAdicCompletionPuncturedSpectrumMorphism R)
      (Scheme.puncturedSpectrumInclusion
        (AdicCompletion (maximalIdeal R) R))
      (Scheme.puncturedSpectrumInclusion R)
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdicCompletion (maximalIdeal R) R)))) :=
  puncturedSpectrumMorphismOfMapMaximalIdealEq_isPullback
    (algebraMap R (AdicCompletion (maximalIdeal R) R))
    AdicCompletion.maximalIdeal_eq_map.symm

/-- If the maximal-adic completion has punctured purity, every finite-etale
cover of the original puncture acquires an extension over the completed
local spectrum after base change. -/
theorem exists_maximalAdicCompletion_extension_of_hasPuncturedPurity
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hpurity : AlgebraicGeometry.FiniteEtale.HasPuncturedPurity
      (AdicCompletion (maximalIdeal R) R))
    (Y : AlgebraicGeometry.FiniteEtale (Scheme.puncturedSpectrum R)) :
    ∃ X : AlgebraicGeometry.FiniteEtale
        (Spec (.of (AdicCompletion (maximalIdeal R) R))),
      Nonempty
        ((AlgebraicGeometry.FiniteEtale.pullback
            (Scheme.puncturedSpectrumInclusion
              (AdicCompletion (maximalIdeal R) R))).obj X ≅
          (AlgebraicGeometry.FiniteEtale.pullback
            (maximalAdicCompletionPuncturedSpectrumMorphism R)).obj Y) :=
  exists_extension_after_baseChange_of_hasPuncturedPurity
    (algebraMap R (AdicCompletion (maximalIdeal R) R))
    AdicCompletion.maximalIdeal_eq_map.symm hpurity Y

end EtaleFundamentalGroups

end
