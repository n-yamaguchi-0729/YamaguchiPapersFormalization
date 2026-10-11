/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The socle of an essential extension of the residue field

In an essential extension of the residue field, the elements killed by the
maximal ideal form precisely the given residue-field image.  Indeed, the
cyclic submodule of any such element meets that image; a coefficient
outside the maximal ideal is a unit and recovers the original element.

Evaluation at one identifies maps from a quotient ring with the elements
annihilated by its defining ideal.  Consequently maps from the residue
field into its essential extension form a copy of the residue field.
The arguments use the existing `R`-module structures throughout.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

private theorem quotient_linearMap_range_le_torsionBySet
    (I : Ideal R) (f : (R ⧸ I) →ₗ[R] E) :
    LinearMap.range f ≤ Submodule.torsionBySet R E I := by
  intro z hz
  obtain ⟨q, rfl⟩ := hz
  apply (Submodule.mem_torsionBySet_iff (I : Set R) (f q)).mpr
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← f.map_smul]
  have hquot : (a : R) • Ideal.Quotient.mk I b = 0 := by
    change Ideal.Quotient.mk I ((a : R) * b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right b a.property)
  rw [hquot, map_zero]

/-- Evaluation at one identifies quotient-module homomorphisms with
vectors annihilated by the quotient ideal. -/
def quotientHomEquivTorsionBySet (I : Ideal R) :
    ((R ⧸ I) →ₗ[R] E) ≃ₗ[R] Submodule.torsionBySet R E I where
  toFun f := ⟨f (Ideal.Quotient.mk I 1),
    quotient_linearMap_range_le_torsionBySet I f ⟨Ideal.Quotient.mk I 1, rfl⟩⟩
  invFun z := I.liftQ (LinearMap.toSpanSingleton R E (z : E)) (by
    intro a ha
    change a • (z : E) = 0
    exact (Submodule.mem_torsionBySet_iff (I : Set R) (z : E)).mp z.property ⟨a, ha⟩)
  left_inv f := by
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    change a • f (Ideal.Quotient.mk I 1) = f (Ideal.Quotient.mk I a)
    rw [← f.map_smul]
    congr 1
    change Ideal.Quotient.mk I (a * 1) = Ideal.Quotient.mk I a
    rw [mul_one]
  right_inv z := by
    apply Subtype.ext
    change (1 : R) • (z : E) = (z : E)
    exact one_smul R (z : E)
  map_add' f g := Subtype.ext rfl
  map_smul' a f := Subtype.ext rfl

/-- The quotient-Hom equivalence evaluates a linear map at the class of one. -/
theorem quotientHomEquivTorsionBySet_apply
    (I : Ideal R) (f : (R ⧸ I) →ₗ[R] E) :
    (quotientHomEquivTorsionBySet (R := R) (E := E) I f : E) =
      f (Ideal.Quotient.mk I 1) := rfl

/-- The inverse quotient-Hom equivalence sends the class of `a` to `a • z`. -/
theorem quotientHomEquivTorsionBySet_symm_apply_mk
    (I : Ideal R) (z : Submodule.torsionBySet R E I) (a : R) :
    (quotientHomEquivTorsionBySet (R := R) (E := E) I).symm z
        (Ideal.Quotient.mk I a) = a • (z : E) := rfl

variable [IsLocalRing R]

/-- In an essential extension of a residue-field image, that image is
exactly the submodule annihilated by the maximal ideal. -/
theorem torsionBySet_maximalIdeal_eq_range
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hess : IsEssentialSubmodule (LinearMap.range i)) :
    Submodule.torsionBySet R E (IsLocalRing.maximalIdeal R) =
      LinearMap.range i := by
  classical
  refine le_antisymm ?_
    (quotient_linearMap_range_le_torsionBySet (IsLocalRing.maximalIdeal R) i)
  intro z hz
  have hzAnn : ∀ a : R, a ∈ IsLocalRing.maximalIdeal R → a • z = (0 : E) := by
    intro a ha
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := E)
      (s := ((IsLocalRing.maximalIdeal R : Ideal R) : Set R)) z).mp hz ⟨a, ha⟩
  by_contra hzRange
  have hdisjoint : Disjoint (LinearMap.range i) (Submodule.span R {z}) := by
    apply (Submodule.disjoint_span_singleton'' (R := R) (M := E)
      (s := LinearMap.range i) (x := z)).mpr
    intro a hwRange
    by_cases ha : a ∈ IsLocalRing.maximalIdeal R
    · exact hzAnn a ha
    · have haUnit : IsUnit a := by
        by_contra haNotUnit
        exact ha ((IsLocalRing.mem_maximalIdeal a).mpr haNotUnit)
      obtain ⟨unit, rfl⟩ := haUnit
      have hzIn : z ∈ LinearMap.range i := by
        have hmul := (LinearMap.range i).smul_mem (↑unit⁻¹ : R) hwRange
        simpa only [smul_smul, Units.inv_mul, one_smul] using hmul
      exact False.elim (hzRange hzIn)
  have hspan : Submodule.span R {z} = ⊥ :=
    hess (Submodule.span R {z}) hdisjoint
  have hzSpan : z ∈ Submodule.span R {z} := Submodule.mem_span_singleton_self z
  rw [hspan] at hzSpan
  have hzZero : z = 0 := (Submodule.mem_bot R).mp hzSpan
  apply hzRange
  rw [hzZero]
  exact (LinearMap.range i).zero_mem

/-- The socle of an essential extension of an embedded residue field is
linearly equivalent to that residue field. -/
def residueFieldHullSocleEquiv
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i)) :
    Submodule.torsionBySet R E (IsLocalRing.maximalIdeal R) ≃ₗ[R]
      (R ⧸ IsLocalRing.maximalIdeal R) :=
  (LinearEquiv.ofEq
    (Submodule.torsionBySet R E (IsLocalRing.maximalIdeal R)) (LinearMap.range i)
    (torsionBySet_maximalIdeal_eq_range i hess)).trans
      (LinearEquiv.ofInjective i hi).symm

/-- Homomorphisms from the residue field into its essential extension
form a copy of the residue field. -/
def residueFieldHullHomEquiv
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i)) :
    ((R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E) ≃ₗ[R]
      (R ⧸ IsLocalRing.maximalIdeal R) :=
  (quotientHomEquivTorsionBySet (R := R) (E := E)
    (IsLocalRing.maximalIdeal R)).trans (residueFieldHullSocleEquiv i hi hess)

end EtaleFundamentalGroups.Purity

end
