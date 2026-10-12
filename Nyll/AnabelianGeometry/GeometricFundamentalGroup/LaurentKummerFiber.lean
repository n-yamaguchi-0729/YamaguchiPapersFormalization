/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerAlgebra

/-!
# Roots as points of the Laurent Kummer fibre

The points of the actual Laurent Kummer algebra above a nonzero scalar
are exactly the roots of its Kummer equation. Both directions are explicit
ring homomorphisms and the inverse laws follow from the quotient universal
property. No identification of a cover fibre with a root set is assumed.
-/

noncomputable section

namespace AnabelianGeometry.GeometricFundamentalGroup

open Polynomial

universe u v
variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- Evaluation of the Laurent coordinate at a nonzero base-field scalar. -/
def laurentScalarEvaluation (a : Kˣ) : LaurentPolynomial K →+* L :=
  LaurentPolynomial.eval₂ (algebraMap K L) (Units.map (algebraMap K L) a)

/-- Points of the actual Kummer algebra above the specified Laurent point. -/
def LaurentKummerFiberHom (n : ℕ) (a : Kˣ) :=
  {f : LaurentKummerAlgebra K n →+* L //
    f.comp (AdjoinRoot.of (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K))) =
      laurentScalarEvaluation a}

/-- The Laurent coordinate specializes to the chosen base scalar. -/
theorem laurentScalarEvaluation_coordinate (a : Kˣ) :
    laurentScalarEvaluation (L := L) a (LaurentPolynomial.T 1) =
      algebraMap K L (a : K) := by
  simp only [laurentScalarEvaluation, LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map]
  rfl

/-- The coordinate of a fibre point satisfies its Kummer equation. -/
theorem laurentKummerFiberHom_root_pow (n : ℕ) (a : Kˣ)
    (f : LaurentKummerFiberHom (L := L) n a) :
    f.val (AdjoinRoot.root (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K))) ^ n =
      algebraMap K L (a : K) := by
  let p : (LaurentPolynomial K)[X] := X ^ n - C (LaurentPolynomial.T 1)
  have hr : AdjoinRoot.root p ^ n = AdjoinRoot.of p (LaurentPolynomial.T 1) := by
    have h := AdjoinRoot.eval₂_root p
    change (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K)).eval₂
      (AdjoinRoot.of p) (AdjoinRoot.root p) = 0 at h
    simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h
  have hf := congrArg (fun g : LaurentPolynomial K →+* L => g (LaurentPolynomial.T 1))
    f.property
  calc
    f.val (AdjoinRoot.root p) ^ n = f.val (AdjoinRoot.root p ^ n) := (map_pow _ _ _).symm
    _ = f.val (AdjoinRoot.of p (LaurentPolynomial.T 1)) := congrArg f.val hr
    _ = laurentScalarEvaluation a (LaurentPolynomial.T 1) := hf
    _ = algebraMap K L (a : K) := laurentScalarEvaluation_coordinate a

/-- A root defines an actual point above the chosen Laurent scalar. -/
def laurentKummerFiberHomOfRoot (n : ℕ) (a : Kˣ) (r : L)
    (hr : r ^ n = algebraMap K L (a : K)) : LaurentKummerFiberHom (L := L) n a :=
  ⟨AdjoinRoot.lift (laurentScalarEvaluation a) r (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
      laurentScalarEvaluation_coordinate, hr, sub_self]), AdjoinRoot.lift_comp_of _⟩

/-- The fibre-point and root constructions are inverse, for the actual
Laurent Kummer cover algebra. -/
def laurentKummerFiberEquivRoots (n : ℕ) (a : Kˣ) :
    LaurentKummerFiberHom (L := L) n a ≃ {r : L // r ^ n = algebraMap K L (a : K)} where
  toFun f := ⟨f.val (AdjoinRoot.root _), laurentKummerFiberHom_root_pow n a f⟩
  invFun r := laurentKummerFiberHomOfRoot (L := L) n a r.val r.property
  left_inv f := by
    apply Subtype.ext
    apply AdjoinRoot.ringHom_ext
    · simp only [laurentKummerFiberHomOfRoot, AdjoinRoot.lift_comp_of]
      exact f.property.symm
    · simp only [laurentKummerFiberHomOfRoot, AdjoinRoot.lift_root]
  right_inv r := by
    apply Subtype.ext
    simp only [laurentKummerFiberHomOfRoot, AdjoinRoot.lift_root]

end AnabelianGeometry.GeometricFundamentalGroup
