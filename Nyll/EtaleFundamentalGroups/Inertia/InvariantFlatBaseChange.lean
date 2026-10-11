/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.InvariantBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.TensorProduct.Basic


/-!
# Fixed subalgebras commute with flat base change

For a finite group, the fixed subalgebra is the kernel of the linear map
`r ↦ (g ↦ g • r - r)`. Flat tensor product preserves this kernel, and tensor
product commutes with the finite product indexed by the group. Consequently
every invariant tensor comes from the tensor product of the fixed subalgebra.

The resulting algebra equivalence uses the actual action on the second tensor
factor and the canonical inclusion of the fixed subalgebra.
-/

namespace EtaleFundamentalGroups.Inertia

open scoped TensorProduct Pointwise

universe u v w z

variable (B : Type u) (A : Type v) (R : Type w) (G : Type z)
  [CommRing B] [CommRing A] [CommRing R] [Algebra B A] [Algebra B R]
  [Group G] [MulSemiringAction G R] [SMulCommClass G B R]

local instance : MulSemiringAction G (A ⊗[B] R) := baseChangeAction B A R G

/-- The tensor action commutes with scalars from the base-change algebra. -/
theorem baseChangeAction_smulCommClass : SMulCommClass G A (A ⊗[B] R) := by
  constructor
  intro g a x
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  have h : g • algebraMap A (A ⊗[B] R) a = algebraMap A (A ⊗[B] R) a := by
    change g • (a ⊗ₜ[B] (1 : R)) = a ⊗ₜ[B] (1 : R)
    rw [baseChangeAction_tmul, smul_one]
  rw [h]

local instance : SMulCommClass G A (A ⊗[B] R) := baseChangeAction_smulCommClass B A R G

private def actionDifference : R →ₗ[B] (G → R) :=
  LinearMap.pi fun g => (MulSemiringAction.toAlgHom B R g).toLinearMap - LinearMap.id

private theorem actionDifference_exact :
    Function.Exact (FixedPoints.subalgebra B R G).val.toLinearMap
      (actionDifference B R G) := by
  intro r
  constructor
  · intro h
    refine ⟨⟨r, ?_⟩, rfl⟩
    intro g
    exact sub_eq_zero.mp (congrFun h g)
  · rintro ⟨r, rfl⟩
    funext g
    exact sub_eq_zero.mpr (r.property g)

private def invariantTensorHom :
    (A ⊗[B] FixedPoints.subalgebra B R G) →ₐ[A]
      FixedPoints.subalgebra A (A ⊗[B] R) G :=
  (Algebra.TensorProduct.map (AlgHom.id A A) (FixedPoints.subalgebra B R G).val).codRestrict
    (FixedPoints.subalgebra A (A ⊗[B] R) G) (by
      intro x g
      induction x with
      | tmul a r =>
          rw [Algebra.TensorProduct.map_tmul, baseChangeAction_tmul]
          change a ⊗ₜ[B] (g • (r : R)) = a ⊗ₜ[B] (r : R)
          rw [r.property g]
      | add x y hx hy =>
          rw [map_add, smul_add, hx, hy])

private theorem invariantTensorHom_bijective [Finite G] [Module.Flat B A] :
    Function.Bijective (invariantTensorHom B A R G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  constructor
  · intro x y h
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := A)
      (FixedPoints.subalgebra B R G).val.toLinearMap Subtype.val_injective
    apply hinj
    exact congrArg Subtype.val h
  · intro x
    have hcoordinates (y : A ⊗[B] R) :
        TensorProduct.piRight B B A (fun _ : G => R)
            ((actionDifference B R G).lTensor A y) = fun g => g • y - y := by
      induction y with
      | tmul a r =>
          funext g
          change a ⊗ₜ[B] (g • r - r) = g • (a ⊗ₜ[B] r) - a ⊗ₜ[B] r
          rw [baseChangeAction_tmul, TensorProduct.tmul_sub]
      | add y z hy hz =>
          rw [map_add, map_add, hy, hz]
          funext g
          change (g • y - y) + (g • z - z) = g • (y + z) - (y + z)
          rw [smul_add, add_sub_add_comm]
    have hzero : (actionDifference B R G).lTensor A (x : A ⊗[B] R) = 0 := by
      apply (TensorProduct.piRight B B A (fun _ : G => R)).injective
      rw [hcoordinates, map_zero]
      funext g
      exact sub_eq_zero.mpr (x.property g)
    obtain ⟨y, hy⟩ := (Module.Flat.lTensor_exact A (actionDifference_exact B R G)
      (x : A ⊗[B] R)).mp hzero
    exact ⟨y, Subtype.ext hy⟩

/-- Fixed subalgebras of finite group actions commute with flat base change.
The forward map is induced by the inclusion of the original fixed subalgebra. -/
noncomputable def invariantFlatBaseChangeEquiv [Finite G] [Module.Flat B A] :
    (A ⊗[B] FixedPoints.subalgebra B R G) ≃ₐ[A]
      FixedPoints.subalgebra A (A ⊗[B] R) G :=
  AlgEquiv.ofBijective (invariantTensorHom B A R G)
    (invariantTensorHom_bijective B A R G)

/-- The flat base-change equivalence has the canonical inclusion square. -/
theorem invariantFlatBaseChangeEquiv_val_comp [Finite G] [Module.Flat B A] :
    (FixedPoints.subalgebra A (A ⊗[B] R) G).val.comp
        (invariantFlatBaseChangeEquiv B A R G).toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id A A) (FixedPoints.subalgebra B R G).val :=
  rfl


/-- If the original fixed elements are exactly the image of the base, the
same holds after flat base change. The proof uses the actual fixed-subalgebra
base-change equivalence and its canonical inclusion square. -/
theorem baseChangeAction_isInvariant [Finite G] [Module.Flat B A]
    [Algebra.IsInvariant B R G] : Algebra.IsInvariant A (A ⊗[B] R) G := by
  have hsurj : Function.Surjective (algebraMap B (FixedPoints.subalgebra B R G)) := by
    intro r
    obtain ⟨b, hb⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) r.val r.property
    exact ⟨b, Subtype.ext hb⟩
  constructor
  intro x hx
  obtain ⟨z, hz⟩ := (invariantFlatBaseChangeEquiv B A R G).surjective ⟨x, hx⟩
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.includeLeft_surjective
    (R := B) (T := FixedPoints.subalgebra B R G) A A hsurj z
  have hval := (AlgHom.congr_fun (invariantFlatBaseChangeEquiv_val_comp B A R G) z).symm.trans
    (congrArg Subtype.val hz)
  rw [← ha] at hval
  change ((Algebra.TensorProduct.map (AlgHom.id A A) (FixedPoints.subalgebra B R G).val).comp
    Algebra.TensorProduct.includeLeft) a = x at hval
  rw [Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_apply, AlgHom.id_apply] at hval
  exact ⟨a, hval⟩

/-- Every prime fiber after flat base change of a finite invariant action is
finite. A nonempty fiber is the orbit of any one of its actual primes. -/
theorem baseChangeAction_finite_primesOver [Finite G] [Module.Flat B A]
    [Algebra.IsInvariant B R G] (p : Ideal A) :
    (p.primesOver (A ⊗[B] R)).Finite := by
  have : Algebra.IsInvariant A (A ⊗[B] R) G := baseChangeAction_isInvariant B A R G
  by_cases h : (p.primesOver (A ⊗[B] R)).Nonempty
  · obtain ⟨Q, hQ, hQp⟩ := h
    have : Q.IsPrime := hQ
    have : Q.LiesOver p := hQp
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A (A ⊗[B] R) G p Q]
    exact Set.finite_range (fun g : G => g • Q)
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

end EtaleFundamentalGroups.Inertia
