/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Lifting power-torsion elements through quotient maps

A power-torsion vector defines a map from a quotient of the ring. For
an ideal family cofinal with ordinary powers, lifting those quotient
maps therefore lifts every power-torsion vector to a power-torsion
vector. This proves surjectivity on the torsion submodules directly,
without constructing a filtered-colimit comparison.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- Lifting maps from a cofinal family of ideal quotients gives
surjectivity on ideal-power torsion. -/
theorem idealPowerTorsionFunctor_map_surjective_of_quotient_lifting
    (I : Ideal R) (J : ℕ → Ideal R)
    (hJI : ∀ n : ℕ, ∃ m : ℕ, J m ≤ I ^ n)
    (hIJ : ∀ m : ℕ, ∃ n : ℕ, I ^ n ≤ J m)
    {A B : ModuleCat.{u} R} (f : A ⟶ B)
    (hlift : ∀ m : ℕ, Function.Surjective
      (fun g : (R ⧸ J m) →ₗ[R] A => f.hom.comp g)) :
    Function.Surjective ((idealPowerTorsionFunctor I).map f) := by
  change Function.Surjective (Ideal.primaryComponent.map I f.hom)
  intro z
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (M := B) (I := I) (z : B)).mp z.property
  obtain ⟨m, hm⟩ := hJI n
  let zMap : R →ₗ[R] B := LinearMap.toSpanSingleton R B (z : B)
  have hzMap : J m ≤ LinearMap.ker zMap := by
    intro a ha
    change a • (z : B) = 0
    exact (Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) (z : B)).mp hn
      ⟨a, hm ha⟩
  let qz : (R ⧸ J m) →ₗ[R] B := (J m).liftQ zMap hzMap
  obtain ⟨g, hg⟩ := hlift m qz
  let y : A := g ((J m).mkQ 1)
  have hy : y ∈ Ideal.primaryComponent A I := by
    obtain ⟨k, hk⟩ := hIJ m
    apply (Ideal.primaryComponent_mem (M := A) (I := I) y).mpr
    refine ⟨k, ?_⟩
    apply (Submodule.mem_torsionBySet_iff ((I ^ k : Ideal R) : Set R) y).mpr
    intro a
    have hq : (a : R) • (J m).mkQ 1 = 0 := by
      rw [← map_smul, smul_eq_mul, mul_one]
      exact (Submodule.Quotient.mk_eq_zero (J m)).mpr (hk a.property)
    change (a : R) • g ((J m).mkQ 1) = 0
    rw [← g.map_smul, hq, map_zero]
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change f.hom y = (z : B)
  have h := DFunLike.congr_fun hg ((J m).mkQ 1)
  change f.hom y = (1 : R) • (z : B) at h
  simpa only [one_smul] using h

end EtaleFundamentalGroups.Purity
