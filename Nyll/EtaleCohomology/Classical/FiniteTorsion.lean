/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The direct limit of ordinary finite-torsion étale cohomology

We use the finite constant groups of circle elements killed by `(n+1)!`.
Their inclusions define a cofinal system of finite cyclic coefficients. The
groups below are the direct limit of the actual derived étale cohomology
groups. They are not defined using fundamental-group characters.

This definition does not assert that derived cohomology commutes with this
direct limit for an arbitrary scheme. Such an identification with cohomology
of the infinite constant torsion sheaf requires a separate comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology.Classical

/-- The finite subgroup of circle elements of order dividing `(n+1)!`. -/
def factorialRoots (n : ℕ) : Subgroup Circle :=
  (powMonoidHom (Nat.factorial (n + 1))).ker

instance (n : ℕ) : Finite (factorialRoots n) := by
  classical
  refine Finite.of_injective (f := fun z : factorialRoots n =>
    (⟨(z.val : ℂ), Multiset.mem_toFinset.mpr
      ((Polynomial.mem_nthRoots (Nat.factorial_pos (n + 1))).2 ?_)⟩ :
      ↑(Polynomial.nthRoots (Nat.factorial (n + 1)) (1 : ℂ)).toFinset)) ?_
  · have hz : (z.val : Circle) ^ Nat.factorial (n + 1) = 1 := z.property
    exact congrArg (fun w : Circle => (w : ℂ)) hz
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun w : ↑(Polynomial.nthRoots (Nat.factorial (n + 1)) (1 : ℂ)).toFinset =>
        (w : ℂ)) h

/-- Factorial divisibility gives the inclusions of the finite coefficient subgroups. -/
theorem factorialRoots_mono {m n : ℕ} (h : m ≤ n) : factorialRoots m ≤ factorialRoots n := by
  intro z hz
  change z ^ Nat.factorial (m + 1) = 1 at hz
  change z ^ Nat.factorial (n + 1) = 1
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial (Nat.add_le_add_right h 1)
  rw [hk, pow_mul, hz, one_pow]

/-- Constant finite torsion coefficients in the same universe as the scheme. -/
abbrev finiteTorsionCoefficients (n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} (Additive (factorialRoots n)))

/-- The actual inclusion between two finite coefficient groups. -/
def finiteTorsionInclusion (m n : ℕ) (h : m ≤ n) :
    finiteTorsionCoefficients.{u} m →+ finiteTorsionCoefficients.{u} n where
  toFun a := ULift.up (Additive.ofMul
    ⟨a.down.toMul.val, factorialRoots_mono h a.down.toMul.property⟩)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Derived small-étale cohomology with the actual finite constant coefficients. -/
def finiteTorsionLevel (X : Scheme.{u}) (i n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (finiteTorsionCoefficients n)) i)

/-- The transition maps are induced by inclusions of the original constant sheaves. -/
def finiteTorsionTransition (X : Scheme.{u}) (i m n : ℕ) (h : m ≤ n) :
    finiteTorsionLevel X i m →+ finiteTorsionLevel X i n :=
  Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom (finiteTorsionInclusion m n h))) i

instance (X : Scheme.{u}) (i : ℕ) :
    DirectedSystem (fun n => finiteTorsionLevel X i n)
      (fun {_ _} h => finiteTorsionTransition X i _ _ h) where
  map_self := by
    intro n a
    have he : AddCommGrpCat.ofHom (finiteTorsionInclusion.{u} n n le_rfl) =
        𝟙 (finiteTorsionCoefficients n) := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl)
    change Sheaf.H.map ((constantSheaf _ AddCommGrpCat.{u}).map _) i a = a
    rw [he, CategoryTheory.Functor.map_id]
    exact Sheaf.H.map_id_apply a
  map_map := by
    intro k n m hmn hnk a
    have he : AddCommGrpCat.ofHom (finiteTorsionInclusion.{u} m k (hmn.trans hnk)) =
        AddCommGrpCat.ofHom (finiteTorsionInclusion m n hmn) ≫
          AddCommGrpCat.ofHom (finiteTorsionInclusion n k hnk) :=
      AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl)
    change Sheaf.H.map _ i (Sheaf.H.map _ i a) =
      Sheaf.H.map ((constantSheaf _ AddCommGrpCat.{u}).map _) i a
    rw [he, CategoryTheory.Functor.map_comp]
    exact (Sheaf.H.map_comp_apply _ _ a).symm

/-- The finite-coefficient direct limit of ordinary étale cohomology. -/
abbrev finiteTorsionCohomology (X : Scheme.{u}) (i : ℕ) : Type u :=
  DirectLimit (fun n => finiteTorsionLevel X i n) (finiteTorsionTransition X i)

/-- A finite-level cohomology class defines a class in the direct limit. -/
private def directLimitInclusion (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (f : ∀ m n, m ≤ n → G m →+ G n) [DirectedSystem G (f · · ·)] (n : ℕ) :
    G n →+ DirectLimit G f where
  toFun a := ⟦⟨n, a⟩⟧
  map_zero' := (DirectLimit.zero_def n).symm
  map_add' a b := (DirectLimit.add_def n a b).symm

/-- A finite-level cohomology class defines a class in the direct limit. -/
def finiteTorsionClass (X : Scheme.{u}) (i n : ℕ) :
    finiteTorsionLevel X i n →+ finiteTorsionCohomology X i :=
  directLimitInclusion (fun n => finiteTorsionLevel X i n) (finiteTorsionTransition X i) n

end EtaleCohomology.Classical
