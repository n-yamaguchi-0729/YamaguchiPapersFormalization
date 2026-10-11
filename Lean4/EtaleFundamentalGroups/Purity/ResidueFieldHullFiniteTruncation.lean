/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.InjectiveHullFiniteLengthDual
import EtaleFundamentalGroups.Purity.InjectiveResidueFieldCogenerator
import EtaleFundamentalGroups.Purity.ResidueFieldHullSocle
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Scalar endomorphisms on finite truncations of a residue-field hull

An endomorphism of an injective residue-field hull restricts to scalar
multiplication on the elements annihilated by an ideal with finite-length
quotient.  Finite biduality supplies the scalar as a class in that
quotient.  Separation by the injective hull proves that its residue
class is unique.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing

variable {R E : Type u} [CommRing R] [IsLocalRing R]
variable [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- On the submodule annihilated by an ideal with finite-length quotient,
every endomorphism of an injective residue-field hull is scalar. -/
theorem exists_smul_eq_on_torsionBySet_of_finiteLength_quotient
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    (J : Ideal R) (hJ : IsFiniteLength R (R ⧸ J)) (f : E →ₗ[R] E) :
    ∃ r : R, ∀ z : E, (∀ a : R, a ∈ J → a • z = 0) → f z = r • z := by
  let g : ((R ⧸ J) →ₗ[R] E) →ₗ[R] E :=
    f.comp (residueFieldHullEvaluation R E (R ⧸ J) (Ideal.Quotient.mk J 1))
  obtain ⟨q, hq⟩ :=
    (bijective_residueFieldHullEvaluation_of_finiteLength i hi hess hJ).surjective g
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨r, ?_⟩
  intro z hz
  have hzJ : z ∈ Submodule.torsionBySet R E (J : Set R) :=
    (Submodule.mem_torsionBySet_iff (R := R) (M := E) (s := (J : Set R)) z).mpr
      (fun a => hz a a.property)
  let zJ : Submodule.torsionBySet R E (J : Set R) := ⟨z, hzJ⟩
  have h := DFunLike.congr_fun hq ((quotientHomEquivTorsionBySet J).symm zJ)
  change (quotientHomEquivTorsionBySet J).symm zJ (Ideal.Quotient.mk J r) =
    f ((quotientHomEquivTorsionBySet J).symm zJ (Ideal.Quotient.mk J 1)) at h
  simpa only [quotientHomEquivTorsionBySet_symm_apply_mk, one_smul] using h.symm

/-- If the difference of two scalars kills all elements annihilated by
`J`, that difference belongs to `J`.  This separation statement does not
require the quotient by `J` to have finite length. -/
theorem sub_mem_ideal_of_smul_eq_zero_on_torsionBySet
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (J : Ideal R) (r s : R)
    (hrs : ∀ z : E, (∀ a : R, a ∈ J → a • z = 0) → (r - s) • z = 0) :
    r - s ∈ J := by
  by_contra hnot
  have hq : Ideal.Quotient.mk J (r - s) ≠ 0 :=
    fun h => hnot (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨g, hg⟩ :=
    exists_linearMap_apply_ne_zero_of_injective_residueField i hi
      (Ideal.Quotient.mk J (r - s)) hq
  apply hg
  have hz : ∀ a : R, a ∈ J → a • g (Ideal.Quotient.mk J 1) = 0 := by
    intro a ha
    have hquot : a • (Ideal.Quotient.mk J 1 : R ⧸ J) = 0 := by
      change Ideal.Quotient.mk J (a * 1) = 0
      rw [mul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (g.map_smul a (Ideal.Quotient.mk J 1)).symm.trans
      ((congrArg g hquot).trans g.map_zero)
  have hscalar : (r - s) • Ideal.Quotient.mk J 1 = Ideal.Quotient.mk J (r - s) := by
    change Ideal.Quotient.mk J ((r - s) * 1) = Ideal.Quotient.mk J (r - s)
    rw [mul_one]
  rw [← hscalar, map_smul]
  exact hrs (g (Ideal.Quotient.mk J 1)) hz

end EtaleFundamentalGroups.Purity
