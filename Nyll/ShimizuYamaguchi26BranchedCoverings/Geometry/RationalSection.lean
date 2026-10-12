/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Set.Image
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.Closeds

/-!
# Rational points and their integral section closures

The primitive numerator and denominator of an actual rational projective point
supply Bezout coefficients. These construct a section of the integral projective
line, whose image is the homogeneous linear zero locus already used for special
fibre intersections. The image of the original point over the rational numbers is
exactly the generic point of this section. Consequently its Zariski closure is
that same zero locus, as in the definition of the divisors in Lemma 2.3 of
Shimizu and Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

/-- The actual integral section obtained from a rational projective point's
primitive coordinates and their Bezout identity. -/
def rationalSection (a : Projectivization ℚ (ℚ × ℚ)) :
    Spec (CommRingCat.of ℤ) ⟶ ProjectiveLine ℤ :=
  let h := rationalPointCoordinates_isCoprime a
  integralSection (rationalPointNumerator a) (rationalPointDenominator a)
    h.choose h.choose_spec.choose h.choose_spec.choose_spec

/-- The constructed morphism is a section of the integral projective line. -/
theorem rationalSection_comp_π (a : Projectivization ℚ (ℚ × ℚ)) :
    rationalSection a ≫ ProjSpace.π ℤ 1 = 𝟙 (Spec (CommRingCat.of ℤ)) :=
  specZIsTerminal.hom_ext _ _

instance (a : Projectivization ℚ (ℚ × ℚ)) : IsClosedImmersion (rationalSection a) := by
  unfold rationalSection
  infer_instance

/-- The actual section image equals the homogeneous support used in the
special-fibre intersection calculations. -/
theorem range_rationalSection (a : Projectivization ℚ (ℚ × ℚ)) :
    Set.range (rationalSection a) = rationalSectionSupport a := by
  unfold rationalSection rationalSectionSupport
  exact range_integralSection _ _ _ _ _

/-- The rational projective-scheme point represented by the primitive
coordinates of the given point of `Projectivization ℚ (ℚ × ℚ)`. -/
def rationalProjectiveSchemePoint (a : Projectivization ℚ (ℚ × ℚ)) : ProjectiveLine ℚ :=
  fieldSectionPoint (rationalPointNumerator a : ℚ) (rationalPointDenominator a : ℚ)
    ((rationalPointCoordinates_isCoprime a).intCast (R := ℚ)).ne_zero_or_ne_zero

/-- The original rational point, viewed as a point of the integral projective line. -/
def rationalSectionGenericPoint (a : Projectivization ℚ (ℚ × ℚ)) : ProjectiveLine ℤ :=
  ProjSpace.map ℤ ℚ 1 (rationalProjectiveSchemePoint a)

/-- The point over the rational numbers is the image of the generic point of
`Spec ℤ` under the constructed integral section. -/
theorem rationalSectionGenericPoint_eq (a : Projectivization ℚ (ℚ × ℚ)) :
    rationalSectionGenericPoint a = rationalSection a (⊥ : PrimeSpectrum ℤ) := by
  have hmem : rationalSectionGenericPoint a ∈ rationalSectionSupport a := by
    rw [rationalSectionGenericPoint, mem_rationalSectionSupport_baseChange_iff]
    exact linearSectionEquation_mem_fieldSectionPoint _ _
      (((rationalPointCoordinates_isCoprime a).intCast (R := ℚ)).ne_zero_or_ne_zero)
  have hbase : ProjSpace.π ℤ 1 (rationalSectionGenericPoint a) =
      (⊥ : PrimeSpectrum ℤ) := by
    have hcomp : ProjSpace.map ℤ ℚ 1 ≫ ProjSpace.π ℤ 1 =
        ProjSpace.π ℚ 1 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) :=
      specZIsTerminal.hom_ext _ _
    change (ProjSpace.map ℤ ℚ 1 ≫ ProjSpace.π ℤ 1)
      (rationalProjectiveSchemePoint a) = _
    rw [hcomp, Scheme.Hom.comp_apply]
    have hq : ProjSpace.π ℚ 1 (rationalProjectiveSchemePoint a) =
        (⊥ : PrimeSpectrum ℚ) := Subsingleton.elim _ _
    rw [hq]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap ℤ ℚ) (⊥ : Ideal ℚ) = ⊥
    exact Ideal.comap_bot_of_injective _ Int.cast_injective
  rw [← range_rationalSection] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hpzero : p = (⊥ : PrimeSpectrum ℤ) := by
    let η : Spec (CommRingCat.of ℤ) := (⊥ : PrimeSpectrum ℤ)
    have hsection : p = (rationalSection a ≫ ProjSpace.π ℤ 1) p := by
      rw [rationalSection_comp_π]
      exact (CategoryTheory.id_apply (X := (Spec (CommRingCat.of ℤ)).carrier) p).symm
    have hpoint : (rationalSection a ≫ ProjSpace.π ℤ 1) p =
        ProjSpace.π ℤ 1 (rationalSectionGenericPoint a) := by
      rw [Scheme.Hom.comp_apply, hp]
    have hgeneric : ProjSpace.π ℤ 1 (rationalSectionGenericPoint a) = η := hbase
    exact hsection.trans (hpoint.trans hgeneric)
  rw [← hp, hpzero]

/-- The homogeneous support is precisely the Zariski closure of the original
rational point in the integral projective line. -/
theorem closure_rationalSectionGenericPoint (a : Projectivization ℚ (ℚ × ℚ)) :
    closure ({rationalSectionGenericPoint a} : Set (ProjectiveLine ℤ)) =
      rationalSectionSupport a := by
  let η : Spec (CommRingCat.of ℤ) := (⊥ : PrimeSpectrum ℤ)
  have hgeneric : closure ({η} : Set (Spec (CommRingCat.of ℤ))) = Set.univ := by
    change closure ({(⊥ : PrimeSpectrum ℤ)} : Set (PrimeSpectrum ℤ)) = Set.univ
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.asIdeal_bot,
      PrimeSpectrum.zeroLocus_bot]
  have hpoint : rationalSectionGenericPoint a = rationalSection a η :=
    rationalSectionGenericPoint_eq a
  calc
    closure ({rationalSectionGenericPoint a} : Set (ProjectiveLine ℤ)) =
        closure ((rationalSection a) '' ({η} : Set (Spec (CommRingCat.of ℤ)))) := by
      rw [Set.image_singleton, ← hpoint]
    _ = (rationalSection a) '' closure ({η} : Set (Spec (CommRingCat.of ℤ))) :=
      (rationalSection a).isClosedEmbedding.closure_image_eq _
    _ = Set.range (rationalSection a) := by rw [hgeneric, Set.image_univ]
    _ = rationalSectionSupport a := range_rationalSection a

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The support complement of the actual product of section kernel ideals
is the finite intersection of the nonvanishing opens of their equations. -/
theorem rationalSectionFamily_supportComplement
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∏ a ∈ A, (rationalSection a).ker).supportComplement =
      A.inf (fun a =>
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
          (linearSectionEquation (rationalPointNumerator a)
            (rationalPointDenominator a))) := by
  have hsingle (a : Projectivization ℚ (ℚ × ℚ)) :
      (rationalSection a).ker.supportComplement =
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
          (linearSectionEquation (rationalPointNumerator a)
            (rationalPointDenominator a)) := by
    apply TopologicalSpace.Opens.ext
    change ((rationalSection a).ker.support : Set (ProjectiveLine ℤ))ᶜ = _
    have hker : ((rationalSection a).ker.support : Set (ProjectiveLine ℤ)) =
        closure (Set.range (rationalSection a)) :=
      Scheme.Hom.support_ker (rationalSection a)
    have hclosed : closure (Set.range (rationalSection a)) =
        Set.range (rationalSection a) :=
      (rationalSection a).isClosedEmbedding.isClosed_range.closure_eq
    have hopen :
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
          (linearSectionEquation (rationalPointNumerator a)
            (rationalPointDenominator a)) : Set (ProjectiveLine ℤ)) =
          (rationalSectionSupport a)ᶜ :=
      ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (rationalPointNumerator a)
          (rationalPointDenominator a))
    exact (congrArg (fun Z : Set (ProjectiveLine ℤ) => Zᶜ)
      (hker.trans (hclosed.trans (range_rationalSection a)))).trans hopen.symm
  have hfinite : (∏ a ∈ A, (rationalSection a).ker).supportComplement =
      A.inf (fun a => (rationalSection a).ker.supportComplement) := by
    change (∏ a ∈ A, (rationalSection a).ker).support.compl =
      A.inf (fun a => (rationalSection a).ker.support.compl)
    rw [Scheme.IdealSheafData.support_finset_prod]
    exact map_finset_sup
      (TopologicalSpace.Closeds.complOrderIso (ProjectiveLine ℤ)) A
      (fun a => (rationalSection a).ker.support)
  exact hfinite.trans (Finset.inf_congr rfl fun a _ => hsingle a)

end ShimizuYamaguchi26BranchedCoverings
