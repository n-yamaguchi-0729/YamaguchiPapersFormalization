/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
import EtaleFundamentalGroups.StrictHenselian.StrictGenericTrivialCover
import EtaleFundamentalGroups.StrictHenselian.StrictGenericNormalizationEtale
import EtaleFundamentalGroups.FiniteEtale.TrivialBaseChangeAlgebra
import EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition
import EtaleFundamentalGroups.GaloisCategories.Surjectivity
import EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import EtaleFundamentalGroups.GaloisCategories.ExactSequence
import SchemeTheory.Normalization.Normal
import SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology


/-!
# The normal-local strict-generic fundamental-group sequence

The right map is the actual fraction-field pullback map and the left map
is induced by the actual geometric-stalk fraction-field homomorphism.
Finite étale covers trivialized by the strict generic field extend by their
actual finite étale normalizations. Covers of the original local ring become
trivial through the actual strictly henselian stalk. The existing Galois-category
criterion gives surjectivity, trivial composite and closed normal generation
of the kernel, with the original maps and geometric point retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem fractionPullback_fullyFaithful
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ Spec (.of (FractionRing R))) :
    Nonempty (FiniteEtale.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).FullyFaithful := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have : IsPreimmersion r := IsPreimmersion.of_isLocalization R⁰
  have : IsDominant r := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (FiniteEtale.pullback r) :=
    pullback_preservesLimitsOfShape_pempty r
  exact ((autHomOfCompIso_surjective_tfae (fiber (point ≫ r)) (fiber point)
    (FiniteEtale.pullback r) (pullbackFiberIso r point)).out 1 2).mp
      (fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant r point)

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]

private theorem strictGeneric_fundamentalGroup_comp_eq_one
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))) :
    let j : Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) ⟶
        Spec (.of (FractionRing R)) :=
      Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ))
    let r : Spec (.of (FractionRing R)) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    (fundamentalGroupHom r (point ≫ j)).comp (fundamentalGroupHom j point) = 1 := by
  intro j r
  apply ContinuousMonoidHom.ext
  intro a
  change fundamentalGroupHom r (point ≫ j) (fundamentalGroupHom j point a) = 1
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let q := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  let b := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  have hfactor : q ≫ b = j ≫ r := by
    change Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫
        Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)) =
      Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (geometricStalkFractionFieldMap_algebraMap φ x).symm
  have : Subsingleton π₁ᵉᵗ(point ≫ q) :=
    subsingleton_fundamentalGroup_geometricStalk (Spec.map (CommRingCat.ofHom φ)) (point ≫ q)
  have heta : (point ≫ q) ≫ b = (point ≫ j) ≫ r := by
    rw [Category.assoc, hfactor, ← Category.assoc]
  have he := fundamentalGroupHom_comp_conj_of_common_composite
    j r q b (j ≫ r) rfl hfactor.symm point ((point ≫ j) ≫ r) rfl heta a
  have hlocal : fundamentalGroupHom q point a = 1 := Subsingleton.elim _ _
  have hone {v w : Spec (.of Ω') ⟶ Spec (.of R)} (e : v = w) :
      e ▸ (1 : π₁ᵉᵗ(v)) = (1 : π₁ᵉᵗ(w)) := by
    cases e
    rfl
  simpa only [hlocal, map_one, hone] using he

private theorem strictGeneric_exists_epi_of_trivial
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))))
    (W : FiniteEtale (Spec (.of (FractionRing R))))
    (hW : ∃ (ι : Type) (_ : Finite ι), Nonempty
      ((∐ fun _ : ι => ⊤_ (FiniteEtale (Spec (.of
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))))) ≅
          (FiniteEtale.pullback (Spec.map
            (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)))).obj W)) :
    ∃ (Z : FiniteEtale (Spec (.of R)))
      (q : (FiniteEtale.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R))))).obj Z ⟶ W), Epi q := by
  let j := Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ))
  have hfixed : ∀ (g : Aut (fiber point))
      (w : (fiber point).obj ((FiniteEtale.pullback j).obj W)), g • w = w :=
    (exists_iso_finite_coproduct_terminal_iff_fixed (F'' := fiber point)
      ((FiniteEtale.pullback j).obj W)).mp hW
  have himage := image_fixed_of_pullback_fiber_fixed j point W hfixed
  obtain ⟨Z, ⟨e⟩⟩ :=
    (fractionCover_normalization_finiteEtale_and_essImage_of_strictGeneric_image_fixed
      φ W point himage).2
  exact ⟨Z, e.hom, inferInstance⟩

/-- The actual fundamental-group sequence for a normal local domain and its
strict generic field. The kernel is the smallest closed normal subgroup
containing the actual strict-generic image. -/
@[stacks 0BSM]
theorem geometricStalk_normalLocal_exactSequence
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))) :
    let j : Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) ⟶
        Spec (.of (FractionRing R)) :=
      Spec.map (CommRingCat.ofHom (geometricStalkFractionFieldMap φ))
    let r : Spec (.of (FractionRing R)) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    Function.Surjective (fundamentalGroupHom r (point ≫ j)) ∧
      (fundamentalGroupHom r (point ≫ j)).comp (fundamentalGroupHom j point) = 1 ∧
      (fundamentalGroupHom r (point ≫ j)).toMonoidHom.ker =
        ProCGroups.Presentations.Subgroup.closedNormalClosure
          (Set.range (fundamentalGroupHom j point)) := by
  intro j r
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (FiniteEtale.pullback r) :=
    pullback_preservesLimitsOfShape_pempty r
  apply ((autHomOfCompIso_exact_sequence_tfae
    (FiniteEtale.pullback r) (FiniteEtale.pullback j)
      (pullbackFiberIso r (point ≫ j)) (pullbackFiberIso j point)).out 3 1).mp
  refine ⟨fractionPullback_fullyFaithful (point ≫ j), ?_, ?_⟩
  · exact (autHomOfCompIso_comp_eq_one_iff
      (FiniteEtale.pullback r) (FiniteEtale.pullback j)
        (pullbackFiberIso r (point ≫ j)) (pullbackFiberIso j point)).mp
          (strictGeneric_fundamentalGroup_comp_eq_one φ point)
  · intro W hW
    exact strictGeneric_exists_epi_of_trivial φ point W hW

end EtaleFundamentalGroups.StrictHenselian
