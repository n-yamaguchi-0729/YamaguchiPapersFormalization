/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# A cyclic Laurent monomial cover as an explicit radical

The endomorphism of the Laurent monomial algebra induced by multiplication by
`n` on `ℤ` becomes, after adjoining an `n`-th root of the degree-one
monomial, the original Laurent monomial algebra.  The equivalence below keeps
track of both the adjoined root and the original base map.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/--
The cyclic Laurent monomial cover is the radical extension obtained by adjoining
an `n`-th root of the degree-one monomial.  The returned equivalence sends the
adjoined root to that monomial, and its restriction to the coefficient Laurent
algebra is the map induced by multiplication by `n` on `ℤ`.
-/
theorem exists_cyclicLaurentRingEquiv
    {R : Type u} [CommRing R] (n : ℕ) (hn : 0 < n) :
    let A := AddMonoidAlgebra R ℤ
    let u : A := AddMonoidAlgebra.single (1 : ℤ) (1 : R)
    let f : A[X] := X ^ n - C u
    ∃ e : AdjoinRoot f ≃+* A,
      e (AdjoinRoot.root f) = u ∧
        e.toRingHom.comp (AdjoinRoot.of f) =
          AddMonoidAlgebra.mapDomainRingHom R (nsmulAddMonoidHom n) := by
  dsimp only
  let A := AddMonoidAlgebra R ℤ
  let u : A := AddMonoidAlgebra.single (1 : ℤ) (1 : R)
  let f : A[X] := X ^ n - C u
  let φ : A →ₐ[R] A :=
    AddMonoidAlgebra.mapDomainAlgHom R R (nsmulAddMonoidHom n)
  have hφu : φ u = u ^ n := by
    change
      AddMonoidAlgebra.mapDomain (nsmulAddMonoidHom n)
          (AddMonoidAlgebra.single (1 : ℤ) (1 : R)) =
        AddMonoidAlgebra.single (1 : ℤ) (1 : R) ^ n
    rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_pow]
    simp
  have hf : f.eval₂ φ u = 0 := by
    simp [f, hφu]
  let forward : AdjoinRoot f →ₐ[R] A :=
    AdjoinRoot.liftAlgHom f φ u hf
  have hu : IsUnit u := by
    rw [isUnit_iff_exists_inv]
    refine ⟨AddMonoidAlgebra.single (-1 : ℤ) (1 : R), ?_⟩
    change
      AddMonoidAlgebra.single (1 : ℤ) (1 : R) *
          AddMonoidAlgebra.single (-1 : ℤ) (1 : R) = 1
    rw [AddMonoidAlgebra.single_mul_single]
    rw [show (1 : ℤ) + (-1 : ℤ) = 0 by norm_num, one_mul]
    rfl
  have hroot_pow :
      AdjoinRoot.root f ^ n = AdjoinRoot.of f u := by
    rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root]
    simp [f]
  have hroot : IsUnit (AdjoinRoot.root f) := by
    refine (isUnit_pow_iff hn.ne').mp ?_
    rw [hroot_pow]
    exact hu.map (AdjoinRoot.of f)
  let z : (AdjoinRoot f)ˣ := hroot.unit
  let rootPowers : Multiplicative ℤ →* AdjoinRoot f :=
    (Units.coeHom (AdjoinRoot f)).comp (zpowersHom (AdjoinRoot f)ˣ z)
  let inverse : A →ₐ[R] AdjoinRoot f :=
    AddMonoidAlgebra.lift R (AdjoinRoot f) ℤ rootPowers
  have hinverse_u : inverse u = AdjoinRoot.root f := by
    change
      (AddMonoidAlgebra.lift R (AdjoinRoot f) ℤ rootPowers)
          (AddMonoidAlgebra.of R ℤ (Multiplicative.ofAdd (1 : ℤ))) =
        AdjoinRoot.root f
    rw [AddMonoidAlgebra.lift_of]
    simp [rootPowers, z]
  have hforward_base :
      forward.comp (AdjoinRoot.ofAlgHom R f) = φ := by
    apply AlgHom.ext
    intro x
    exact AdjoinRoot.liftAlgHom_of f φ u hf x
  have hinverse_base :
      inverse.comp φ = AdjoinRoot.ofAlgHom R f := by
    apply AddMonoidAlgebra.algHom_ext'
    · apply MonoidHom.ext_mint
      change inverse (φ u) = AdjoinRoot.of f u
      rw [hφu, map_pow, hinverse_u, hroot_pow]
    · ext
  have hforward_inverse :
      forward.comp inverse = AlgHom.id R A := by
    apply AddMonoidAlgebra.algHom_ext'
    · apply MonoidHom.ext_mint
      change forward (inverse u) = u
      rw [hinverse_u]
      exact AdjoinRoot.liftAlgHom_root f φ u hf
    · ext
  have hinverse_forward :
      inverse.comp forward = AlgHom.id R (AdjoinRoot f) := by
    apply AdjoinRoot.algHom_ext'
    · rw [AlgHom.comp_assoc, hforward_base, hinverse_base]
      rfl
    · change inverse (forward (AdjoinRoot.root f)) = AdjoinRoot.root f
      rw [AdjoinRoot.liftAlgHom_root, hinverse_u]
  let e : AdjoinRoot f ≃ₐ[R] A :=
    AlgEquiv.ofAlgHom forward inverse hforward_inverse hinverse_forward
  refine ⟨e.toRingEquiv, ?_, ?_⟩
  · change forward (AdjoinRoot.root f) = u
    exact AdjoinRoot.liftAlgHom_root f φ u hf
  · change forward.toRingHom.comp (AdjoinRoot.of f) =
      AddMonoidAlgebra.mapDomainRingHom R (nsmulAddMonoidHom n)
    change (forward.comp (AdjoinRoot.ofAlgHom R f)).toRingHom = φ.toRingHom
    exact congrArg AlgHom.toRingHom hforward_base

end EtaleFundamentalGroups.Kummer
