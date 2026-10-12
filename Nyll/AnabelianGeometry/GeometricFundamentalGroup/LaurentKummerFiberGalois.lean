/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerFiber
import Nyll.AnabelianGeometry.KummerTheory.RootCharacter
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Galois stabilizers of Laurent Kummer fibre points

Postcomposition gives the actual Galois action on the algebra points of a
Laurent Kummer fibre. Its point stabilizer fixes exactly the radical field.
This identifies the arithmetic point data without a roots-of-unity assumption.
-/

noncomputable section

namespace AnabelianGeometry.GeometricFundamentalGroup

open Polynomial

universe u v
variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- Evaluation at a base-field scalar is fixed by every base-field automorphism. -/
theorem laurentScalarEvaluation_fixed (a : Kˣ) (σ : L ≃ₐ[K] L)
    (p : LaurentPolynomial K) :
    σ (laurentScalarEvaluation a p) = laurentScalarEvaluation a p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T m b =>
    simp only [laurentScalarEvaluation, LaurentPolynomial.eval₂_C_mul_T]
    rw [← map_zpow, Units.coe_map]
    change σ (algebraMap K L b * algebraMap K L ((a ^ m : Kˣ) : K)) =
      algebraMap K L b * algebraMap K L ((a ^ m : Kˣ) : K)
    rw [map_mul, σ.commutes, σ.commutes]

/-- Galois acts on actual algebra points by postcomposition. -/
instance laurentKummerFiberMulAction (n : ℕ) (a : Kˣ) :
    MulAction (L ≃ₐ[K] L) (LaurentKummerFiberHom (L := L) n a) where
  smul σ f := ⟨σ.toRingHom.comp f.val, by
    rw [RingHom.comp_assoc, f.property]
    apply RingHom.ext
    intro p
    exact laurentScalarEvaluation_fixed a σ p⟩
  one_smul f := by
    apply Subtype.ext
    apply RingHom.ext
    intro p
    rfl
  mul_smul σ τ f := by
    apply Subtype.ext
    apply RingHom.ext
    intro p
    rfl

/-- Fixing a fibre point is equivalent to fixing its radical coordinate. -/
theorem mem_laurentKummerFiber_stabilizer_iff (n : ℕ) (a : Kˣ)
    (f : LaurentKummerFiberHom (L := L) n a) (σ : L ≃ₐ[K] L) :
    σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) f ↔
      σ (f.val (AdjoinRoot.root _)) = f.val (AdjoinRoot.root _) := by
  change σ • f = f ↔ _
  constructor
  · intro h
    exact congrArg (fun g : LaurentKummerFiberHom (L := L) n a =>
      g.val (AdjoinRoot.root _)) h
  · intro h
    apply Subtype.ext
    apply AdjoinRoot.ringHom_ext
    · exact (σ • f).property.trans f.property.symm
    · exact h

/-- A positive-degree fibre point has a nonzero radical coordinate. -/
theorem laurentKummerFiber_root_ne_zero {n : ℕ} (hn : n ≠ 0) (a : Kˣ)
    (f : LaurentKummerFiberHom (L := L) n a) :
    f.val (AdjoinRoot.root _) ≠ 0 := by
  intro hz
  have hp := laurentKummerFiberHom_root_pow n a f
  rw [hz, zero_pow hn] at hp
  exact ((map_ne_zero (algebraMap K L)).mpr a.ne_zero) hp.symm

/-- The stabilizer of an actual fibre point is the fixing subgroup of its
radical field, including in an infinite ambient extension. -/
theorem laurentKummerFiber_stabilizer {n : ℕ} (hn : n ≠ 0) (a : Kˣ)
    (f : LaurentKummerFiberHom (L := L) n a) :
    MulAction.stabilizer (L ≃ₐ[K] L) f =
      (IntermediateField.adjoin K ({f.val (AdjoinRoot.root _)} : Set L)).fixingSubgroup := by
  ext σ
  rw [mem_laurentKummerFiber_stabilizer_iff,
    AnabelianGeometry.KummerTheory.mem_fixingSubgroup_adjoin_iff_rootRatio_eq_one
      (laurentKummerFiber_root_ne_zero hn a f),
    AnabelianGeometry.KummerTheory.rootRatio_eq_one_iff
      (laurentKummerFiber_root_ne_zero hn a f)]

/-- Recover the radical field from the Galois stabilizer of the fibre point. -/
theorem fixedField_laurentKummerFiber_stabilizer [IsGalois K L]
    {n : ℕ} (hn : n ≠ 0) (a : Kˣ) (f : LaurentKummerFiberHom (L := L) n a) :
    IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) f) =
      IntermediateField.adjoin K ({f.val (AdjoinRoot.root _)} : Set L) := by
  rw [laurentKummerFiber_stabilizer hn a f, InfiniteGalois.fixedField_fixingSubgroup]

end AnabelianGeometry.GeometricFundamentalGroup
