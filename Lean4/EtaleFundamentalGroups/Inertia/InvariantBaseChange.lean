/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# Inertia under base change

The action on the second tensor factor preserves inertia at every ideal and
its contraction. In particular, this proves Stacks Project, Tag 0BSS for
arbitrary base change from the fixed subring. No finiteness or primality is
needed for this ideal-theoretic statement.

Reference: https://stacks.math.columbia.edu/tag/0BSS
-/

open scoped TensorProduct

namespace EtaleFundamentalGroups.Inertia

universe u v w z

section BaseChange

variable (B : Type u) (A : Type v) (R : Type w) (G : Type z)
  [CommRing B] [CommRing A] [CommRing R] [Algebra B A] [Algebra B R]
  [Group G] [MulSemiringAction G R] [SMulCommClass G B R]

/-- Extend a ring action, fixing the base, to the second tensor factor. -/
abbrev baseChangeAction : MulSemiringAction G (A ⊗[B] R) :=
  MulSemiringAction.compHom (A ⊗[B] R)
    { toFun := fun g =>
        (Algebra.TensorProduct.map (AlgHom.id B A)
          (MulSemiringAction.toAlgHom B R g)).toRingHom
      map_one' := by
        change (Algebra.TensorProduct.map (AlgHom.id B A)
          (MulSemiringAction.toAlgHom B R 1)).toRingHom = (AlgHom.id B (A ⊗[B] R)).toRingHom
        apply congrArg AlgHom.toRingHom
        apply Algebra.TensorProduct.ext'
        intro a r
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          MulSemiringAction.toAlgHom_apply, one_smul]
      map_mul' g h := by
        change (Algebra.TensorProduct.map (AlgHom.id B A)
          (MulSemiringAction.toAlgHom B R (g * h))).toRingHom =
            ((Algebra.TensorProduct.map (AlgHom.id B A)
              (MulSemiringAction.toAlgHom B R g)).comp
                (Algebra.TensorProduct.map (AlgHom.id B A)
                  (MulSemiringAction.toAlgHom B R h))).toRingHom
        apply congrArg AlgHom.toRingHom
        apply Algebra.TensorProduct.ext'
        intro a r
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, MulSemiringAction.toAlgHom_apply, mul_smul] }

local instance : MulSemiringAction G (A ⊗[B] R) := baseChangeAction B A R G

/-- The extended action fixes the first tensor factor. -/
theorem baseChangeAction_tmul (g : G) (a : A) (r : R) :
    g • (a ⊗ₜ[B] r) = a ⊗ₜ[B] (g • r) :=
  Algebra.TensorProduct.map_tmul (AlgHom.id B A)
    (MulSemiringAction.toAlgHom B R g) a r

/-- Inertia is unchanged by tensor base change, at any ideal and its
contraction to the acted-on factor. -/
theorem inertia_comap_includeRight (Q : Ideal (A ⊗[B] R)) :
    (Q.comap (Algebra.TensorProduct.includeRight (R := B) (A := A)
      (B := R)).toRingHom).inertia G = Q.inertia G := by
  apply Subgroup.ext
  intro g
  rw [Ideal.mem_inertia, Ideal.mem_inertia]
  constructor
  · intro hg x
    induction x with
    | tmul a r =>
        rw [baseChangeAction_tmul, ← TensorProduct.tmul_sub]
        have hr : (1 : A) ⊗ₜ[B] (g • r - r) ∈ Q := hg r
        have hmul := Q.mul_mem_left (a ⊗ₜ[B] (1 : R)) hr
        simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hmul
    | add x y hx hy =>
        rw [smul_add, add_sub_add_comm]
        exact Q.add_mem hx hy
  · intro hg r
    have hr := hg ((1 : A) ⊗ₜ[B] r)
    rw [baseChangeAction_tmul, ← TensorProduct.tmul_sub] at hr
    exact hr

/-- The prescribed action on the fixed tensor factor commutes with an
actual change of the coefficient algebra. This is the existing tensor-map
composition identity applied to the two independent coordinates. -/
theorem baseChangeAction_map {A' : Type*} [CommRing A'] [Algebra B A']
    (f : A →ₐ[B] A') :
    let : MulSemiringAction G (A' ⊗[B] R) := baseChangeAction B A' R G
    ∀ (g : G) (x : A ⊗[B] R),
      Algebra.TensorProduct.map f (AlgHom.id B R) (g • x) =
        g • Algebra.TensorProduct.map f (AlgHom.id B R) x := by
  intro targetAction g x
  change Algebra.TensorProduct.map f (AlgHom.id B R)
      (Algebra.TensorProduct.map (AlgHom.id B A) (MulSemiringAction.toAlgHom B R g) x) =
    Algebra.TensorProduct.map (AlgHom.id B A') (MulSemiringAction.toAlgHom B R g)
      (Algebra.TensorProduct.map f (AlgHom.id B R) x)
  have h :
      (Algebra.TensorProduct.map f (AlgHom.id B R)).comp
          (Algebra.TensorProduct.map (AlgHom.id B A) (MulSemiringAction.toAlgHom B R g)) =
        (Algebra.TensorProduct.map (AlgHom.id B A') (MulSemiringAction.toAlgHom B R g)).comp
          (Algebra.TensorProduct.map f (AlgHom.id B R)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp only [AlgHom.id_comp, AlgHom.comp_id]
  exact AlgHom.congr_fun h x

end BaseChange

/-- Stacks Project, Tag 0BSS: a base change from the invariant subring
preserves the inertia group at each prime (and, more generally, each ideal).
The tensor action is constructed from the given action on `R`. -/
theorem inertia_invariantBaseChange
    (A : Type v) (R : Type w) (G : Type z)
    [CommRing A] [CommRing R] [Group G] [MulSemiringAction G R]
    [Algebra (FixedPoints.subring R G) A]
    (Q : Ideal (A ⊗[FixedPoints.subring R G] R)) :
    letI := baseChangeAction (FixedPoints.subring R G) A R G
    (Q.comap (Algebra.TensorProduct.includeRight
      (R := FixedPoints.subring R G) (A := A) (B := R)).toRingHom).inertia G =
      Q.inertia G :=
  inertia_comap_includeRight (FixedPoints.subring R G) A R G Q

end EtaleFundamentalGroups.Inertia
