/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The closed fiber and puncture of the actual geometric stalk

The maximal ideal of an arbitrary local base ring generates the maximal ideal
of its geometric étale stalk. A nonunit germ is represented on an affine
pointed étale neighborhood; after localization at the selected prime, the
unramified local algebra theorem expresses it in the extended base ideal.
Essential finite type is used only for this localized neighborhood ring.

Consequently the inverse image of the base closed point is exactly the stalk
closed point, and the actual punctured stalk spectrum is the base change of
the punctured base spectrum. No finiteness, reducedness, normality, dimension,
or separability assumption on the chosen geometric overfield is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  (φ : R →+* Ω) [IsLocalHom φ]

/-- The maximal ideal of the local base generates the maximal ideal of the
actual geometric étale stalk. -/
theorem geometricStalkStructureMap_map_maximalIdeal :
    (IsLocalRing.maximalIdeal R).map (geometricStalkStructureMap φ) =
      IsLocalRing.maximalIdeal (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le (geometricStalkStructureMap φ))
  intro a ha
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let H := geometricStalk s
  obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representative s a
  obtain ⟨V, v, g, hVaffine, hg⟩ := geometricStalk_exists_affine_refinement s W t
  have : IsAffine V.left := hVaffine
  let β : R →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  let : Algebra R Γ(V.left, ⊤) := β.toAlgebra
  have hβ : β.Etale := by
    change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
          inferInstance)
    · exact HasRingHomProperty.appTop (P := @Etale)
        (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) inferInstance
  have : Algebra.Etale R Γ(V.left, ⊤) := hβ
  let B := Localization.AtPrime (geometricNeighborhoodPrime s V v).asIdeal
  let δ : B →+* H := geometricStalkLocalizedGerm s V v
  have hcoeff : δ.comp (algebraMap R B) = geometricStalkStructureMap φ := by
    rw [IsScalarTower.algebraMap_eq R Γ(V.left, ⊤) B, ← RingHom.comp_assoc]
    exact (congrArg (fun f : Γ(V.left, ⊤) →+* H => f.comp β)
      (geometricStalkLocalizedGerm_comp s V v)).trans
        (geometricStalkGerm_comp_structure φ V v)
  have : IsLocalHom (δ.comp (algebraMap R B)) := by
    rw [hcoeff]
    infer_instance
  have : IsLocalHom (algebraMap R B) := isLocalHom_of_comp (algebraMap R B) δ
  have : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R Γ(V.left, ⊤) B
  have : Algebra.FormallyUnramified R B :=
    Algebra.FormallyUnramified.comp R Γ(V.left, ⊤) B
  let b : B := algebraMap Γ(V.left, ⊤) B (g.left.appTop z)
  have hrepresent : δ b = a := by
    change geometricStalkLocalizedGerm s V v
      (algebraMap Γ(V.left, ⊤) B (g.left.appTop z)) = a
    rw [geometricStalkLocalizedGerm_apply]
    have hgerm : g.left.appTop ≫ geometricStalkGerm s V v = geometricStalkGerm s W t := by
      have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
        g v (etaleSections (Spec (CommRingCat.of R)))
      rw [hg] at h
      exact h
    exact (ConcreteCategory.congr_hom hgerm z).trans hz
  have hb : b ∈ IsLocalRing.maximalIdeal B := by
    intro hbunit
    apply ha
    rw [← hrepresent]
    exact hbunit.map δ
  have hbbase : b ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R B) := by
    rw [Algebra.FormallyUnramified.map_maximalIdeal]
    exact hb
  have hmap := Ideal.mem_map_of_mem δ hbbase
  rw [Ideal.map_map, hcoeff, hrepresent] at hmap
  exact hmap

/-- The closed fiber of the actual geometric stalk spectrum has exactly its
closed point as its underlying set. -/
theorem geometricStalkStructureMap_comap_eq_closedPoint_iff
    (x : PrimeSpectrum (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :
    PrimeSpectrum.comap (geometricStalkStructureMap φ) x = IsLocalRing.closedPoint R ↔
      x = IsLocalRing.closedPoint (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  constructor
  · intro hx
    apply PrimeSpectrum.ext
    apply le_antisymm (IsLocalRing.le_maximalIdeal x.2.1)
    rw [← geometricStalkStructureMap_map_maximalIdeal φ]
    apply Ideal.map_le_iff_le_comap.mpr
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal hx).symm
  · rintro rfl
    exact IsLocalRing.comap_closedPoint (geometricStalkStructureMap φ)

/-- The inverse image of the punctured local spectrum is the actual punctured
geometric stalk spectrum, for an arbitrary local base ring. -/
theorem geometricStalkStructureMap_preimage_puncturedSpectrumOpen :
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) ⁻¹ᵁ
        Scheme.puncturedSpectrumOpen R =
      Scheme.puncturedSpectrumOpen (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  ext x
  change PrimeSpectrum.comap (geometricStalkStructureMap φ) x ≠ IsLocalRing.closedPoint R ↔
    x ≠ IsLocalRing.closedPoint (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  exact not_congr (geometricStalkStructureMap_comap_eq_closedPoint_iff φ x)

/-- The actual punctured geometric stalk spectrum is the pullback of the
punctured base spectrum along the actual stalk structure map. -/
def geometricStalkPuncturedSpectrumPullbackIso :
    pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
        (Scheme.puncturedSpectrumInclusion R) ≅
      Scheme.puncturedSpectrum (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
  pullbackRestrictIsoRestrict
      (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
      (Scheme.puncturedSpectrumOpen R) ≪≫
    (Spec (CommRingCat.of (geometricStalk (Spec.map (CommRingCat.ofHom φ))))).isoOfEq
      (geometricStalkStructureMap_preimage_puncturedSpectrumOpen φ)

/-- The puncture comparison respects the canonical map to the full stalk
spectrum. -/
@[reassoc]
theorem geometricStalkPuncturedSpectrumPullbackIso_hom_inclusion :
    (geometricStalkPuncturedSpectrumPullbackIso φ).hom ≫
        Scheme.puncturedSpectrumInclusion
          (geometricStalk (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
        (Scheme.puncturedSpectrumInclusion R) := by
  change ((pullbackRestrictIsoRestrict
      (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
      (Scheme.puncturedSpectrumOpen R)).hom ≫
    ((Spec (CommRingCat.of (geometricStalk (Spec.map (CommRingCat.ofHom φ))))).isoOfEq
      (geometricStalkStructureMap_preimage_puncturedSpectrumOpen φ)).hom) ≫
      (Scheme.puncturedSpectrumOpen
        (geometricStalk (Spec.map (CommRingCat.ofHom φ)))).ι =
      pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
        (Scheme.puncturedSpectrumOpen R).ι
  rw [Category.assoc, Scheme.isoOfEq_hom_ι, pullbackRestrictIsoRestrict_hom_ι]

end EtaleFundamentalGroups.StrictHenselian
