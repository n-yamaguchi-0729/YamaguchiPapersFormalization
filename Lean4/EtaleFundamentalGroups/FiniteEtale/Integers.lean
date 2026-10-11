/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Data.Int.Order.Units
import EtaleFundamentalGroups.FiniteEtale.GenericFiber.Connected
import EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component
import EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Finite étale algebras over the integers

Hermite–Minkowski excludes a nontrivial number field whose ring of integers
is unramified over `ℤ`: no prime can divide its discriminant, whereas a
number field of degree greater than one has absolute discriminant greater
than two. Applying this to a component of the generic fibre shows that a
connected finite étale `ℤ`-algebra is `ℤ` itself.
-/

noncomputable section

open scoped TensorProduct NumberField

namespace EtaleFundamentalGroups

/-- An everywhere unramified number field has degree one over `ℚ`. -/
theorem numberField_finrank_eq_one_of_formallyUnramified
    (K : Type*) [Field K] [NumberField K]
    [Algebra.FormallyUnramified ℤ (𝓞 K)] :
    Module.finrank ℚ K = 1 := by
  have hunit : IsUnit (NumberField.discr K) := by
    by_contra hnunit
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor
      hnunit (NumberField.discr_ne_zero K)
    apply ((NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K)
      (irreducible_iff_prime.mp hp)).mpr ?_) hpd
    intro P hP hlying
    let : P.IsMaximal := hP
    exact (Algebra.formallyUnramified_iff_forall.mp
      (inferInstance : Algebra.FormallyUnramified ℤ (𝓞 K)))
      ⟨P, inferInstance⟩
  have habs : |NumberField.discr K| = 1 := Int.isUnit_iff_abs_eq.mp hunit
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  by_contra hne
  have hgt : 1 < Module.finrank ℚ K := by omega
  have hbound := NumberField.abs_discr_gt_two (K := K) hgt
  omega

/-- For an everywhere unramified number field, every algebraic integer is
an ordinary integer. -/
theorem integerAlgebraMap_ringOfIntegers_bijective
    (K : Type*) [Field K] [NumberField K]
    [Algebra.FormallyUnramified ℤ (𝓞 K)] :
    Function.Bijective (algebraMap ℤ (𝓞 K)) := by
  refine ⟨FaithfulSMul.algebraMap_injective ℤ (𝓞 K), ?_⟩
  intro x
  obtain ⟨q, hq⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).mp
      (numberField_finrank_eq_one_of_formallyUnramified K) (x : K)
  have hqmap : algebraMap ℚ K q = (x : K) := by
    simpa only [Algebra.smul_def, mul_one] using hq
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := K)).mp
      (hqmap.symm ▸ x.property)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change algebraMap ℤ K z = (x : K)
  calc
    (algebraMap ℤ K) z = (algebraMap ℚ K) ((algebraMap ℤ ℚ) z) :=
      IsScalarTower.algebraMap_apply ℤ ℚ K z
    _ = (algebraMap ℚ K) q := by rw [hz]
    _ = (x : K) := hqmap

/-- The structure map of a connected finite étale `ℤ`-algebra is bijective.
Connectedness makes the algebra a domain; étaleness gives flatness, hence
torsion-freeness. The number-field unramified theorem then applies. -/
theorem integerAlgebraMap_bijective_of_connected_finiteEtale
    (T : Type*) [CommRing T]
    [Algebra.Etale ℤ T]
    [ConnectedSpace (PrimeSpectrum T)]
    (hfiniteT : RingHom.Finite (algebraMap ℤ T)) :
    Function.Bijective (algebraMap ℤ T) := by
  classical
  let : Module ℤ T := Algebra.toModule
  let : Module.Finite ℤ T := (RingHom.finite_algebraMap).mp hfiniteT
  let : IsDomain T :=
    finiteEtale_isDomain_of_connectedSpace_primeSpectrum (R := ℤ) (K := ℚ)
  let : Module.Flat ℤ T := inferInstance
  let : Module.IsTorsionFree ℤ T := inferInstance
  let : FaithfulSMul ℤ T := (Module.isTorsionFree_iff_faithfulSMul).mp inferInstance
  exact bijective_algebraMap_int_of_finite_of_unramified
end EtaleFundamentalGroups

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

/-- A connected finite étale cover of `Spec ℤ` has an invertible structure
morphism. Its global-sections algebra is a connected finite étale
`ℤ`-algebra, so the arithmetic theorem above applies. -/
theorem isIso_hom_of_connected_over_integers
    (Y : FiniteEtale (Spec (CommRingCat.of ℤ)))
    [ConnectedSpace Y.left] : IsIso Y.hom := by
  let hY : IsFiniteEtale Y.hom := Y.prop
  let : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of ℤ))).obj Y.right) := by
    change IsAffine (Spec (CommRingCat.of ℤ))
    infer_instance
  let : IsFinite Y.hom := hY.toIsFinite
  let : Etale Y.hom := hY.toEtale
  let : IsAffine ((𝟭 Scheme).obj Y.left) := by
    change IsAffine Y.left
    exact isAffine_of_isAffineHom Y.hom
  let A := Γ(Y.left, ⊤)
  let : Algebra ℤ A := Ring.toIntAlgebra A
  let : Module ℤ A := Algebra.toModule
  let e : Γ(Spec (CommRingCat.of ℤ), ⊤) ≃+* ℤ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv
  have hmap : algebraMap ℤ A = Y.hom.appTop.hom.comp e.symm.toRingHom :=
    Subsingleton.elim _ _
  have hfinite : RingHom.Finite (algebraMap ℤ A) := by
    rw [hmap]
    exact RingHom.finite_respectsIso.2 Y.hom.appTop.hom e.symm
      Y.hom.finite_appTop
  have hetale : RingHom.Etale (algebraMap ℤ A) := by
    rw [hmap]
    apply RingHom.Etale.respectsIso.2
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp
      (inferInstance : Etale Y.hom)
  let : Module.Finite ℤ A := (RingHom.finite_algebraMap).mp hfinite
  let : Algebra.Etale ℤ A := (RingHom.etale_algebraMap).mp hetale
  let : ConnectedSpace (PrimeSpectrum A) :=
    Y.left.isoSpec.schemeIsoToHomeo.connectedSpace_iff.mp inferInstance
  let eA : ℤ ≃+* A := RingEquiv.ofBijective (algebraMap ℤ A)
    (EtaleFundamentalGroups.integerAlgebraMap_bijective_of_connected_finiteEtale A hfinite)
  let eY : Y.left ≅ Spec (CommRingCat.of ℤ) :=
    Y.left.isoSpec ≪≫ Scheme.Spec.mapIso eA.toCommRingCatIso.op
  have heY : eY.hom = Y.hom := specZIsTerminal.hom_ext _ _
  rw [← heY]
  infer_instance

/-- The geometric fibre of a connected finite étale cover of `Spec ℤ`
consists of exactly one point. -/
theorem subsingleton_fiber_of_connected_over_integers
    (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ))
    (Y : FiniteEtale (Spec (CommRingCat.of ℤ)))
    [ConnectedSpace Y.left] : Subsingleton ((fiber ξ).obj Y) := by
  let : IsIso Y.hom := isIso_hom_of_connected_over_integers Y
  let e : (Limits.pullback Y.hom ξ : Scheme) ≃ₜ Spec (CommRingCat.of Ω) :=
    (asIso (Limits.pullback.snd Y.hom ξ)).schemeIsoToHomeo
  change Subsingleton (Limits.pullback Y.hom ξ : Scheme)
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim (e x) (e y))⟩

end AlgebraicGeometry.FiniteEtale
