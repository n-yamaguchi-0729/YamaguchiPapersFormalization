/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerGeometricFiber
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerFiberGalois
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-!
# Arithmetic fibres at rational Laurent points

Pull the named Kummer cover back along a rational point to obtain an actual
finite-etale scheme over the base field. Its geometric fibre is identified
with the algebra-point description, through the actual pullback square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u
variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- Evaluate a Laurent monomial directly in the base field before scalar extension. -/
theorem laurentScalarEvaluation_monomial (a : Kˣ) (b : K) (m : ℤ) :
    laurentScalarEvaluation (L := L) a (LaurentPolynomial.C b * LaurentPolynomial.T m) =
      algebraMap K L (b * ((a ^ m : Kˣ) : K)) := by
  rw [laurentScalarEvaluation, LaurentPolynomial.eval₂_C_mul_T,
    ← map_zpow, Units.coe_map, map_mul]
  rfl

/-- Laurent scalar evaluation commutes with extension of the base field. -/
theorem laurentScalarEvaluation_baseChange (a : Kˣ) :
    (algebraMap K L).comp (laurentScalarEvaluation (L := K) a) =
      laurentScalarEvaluation (L := L) a := by
  apply RingHom.ext
  intro p
  change algebraMap K L (laurentScalarEvaluation (L := K) a p) =
    laurentScalarEvaluation (L := L) a p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | C_mul_T m b =>
    rw [laurentScalarEvaluation_monomial, laurentScalarEvaluation_monomial]
    rfl

/-- The geometric Laurent point is the scalar extension of its rational point. -/
theorem laurentKummerPoint_baseChange (a : Kˣ) :
    ξ K L ≫ laurentKummerPoint (L := K) a = laurentKummerPoint (L := L) a := by
  change Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
    Spec.map (CommRingCat.ofHom (laurentScalarEvaluation (L := K) a)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : LaurentPolynomial K →+* L => Spec.map (CommRingCat.ofHom f))
    (laurentScalarEvaluation_baseChange a)

/-- The actual finite-etale scheme over the base obtained by taking the
Kummer fibre at the rational point. -/
def laurentKummerArithmeticFiber [CharZero K] (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    FiniteEtale (Spec (.of K)) :=
  (FiniteEtale.pullback (laurentKummerPoint (L := K) a)).obj
    (laurentKummerCover K n hn)

/-- The pullback square identifies field-valued points with Laurent fibre points. -/
def laurentKummerArithmeticOverEquiv [CharZero K]
    (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    (Over.mk (ξ K L) ⟶ (laurentKummerArithmeticFiber n hn a).toComma) ≃
      LaurentKummerSchemeFiber (L := L) n a where
  toFun z := ⟨z.left ≫ pullback.fst (laurentKummerProjection K n)
      (laurentKummerPoint (L := K) a), by
    change (z.left ≫ pullback.fst (laurentKummerProjection K n)
      (laurentKummerPoint (L := K) a)) ≫ laurentKummerProjection K n = _
    have hz : z.left ≫ pullback.snd (laurentKummerProjection K n)
        (laurentKummerPoint (L := K) a) = ξ K L := z.w
    have hcondition :
        pullback.fst (laurentKummerProjection K n) (laurentKummerPoint (L := K) a) ≫
          laurentKummerProjection K n =
        pullback.snd (laurentKummerProjection K n) (laurentKummerPoint (L := K) a) ≫
          laurentKummerPoint (L := K) a := pullback.condition
    erw [Category.assoc, hcondition, ← Category.assoc, hz]
    exact laurentKummerPoint_baseChange a⟩
  invFun f := Over.homMk
    (pullback.lift f.val (ξ K L) (f.property.trans (laurentKummerPoint_baseChange a).symm))
    (pullback.lift_snd _ _ _)
  left_inv z := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans z.w.symm
  right_inv f := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

/-- The actual arithmetic geometric fibre is equivalent to the algebra points. -/
def laurentKummerArithmeticFiberEquiv [CharZero K] [IsSepClosed L]
    (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    (fib K L).obj (laurentKummerArithmeticFiber n hn a) ≃
      LaurentKummerFiberHom (L := L) n a :=
  ((fiberObjEquivHom (ξ K L) (laurentKummerArithmeticFiber n hn a)).trans
    (laurentKummerArithmeticOverEquiv n hn a)).trans (laurentKummerSchemeFiberEquiv n a)

/-- The point map underlying the arithmetic comparison is the actual
projection from the pullback scheme. -/
theorem laurentKummerArithmeticFiberEquiv_spec [CharZero K] [IsSepClosed L]
    (n : ℕ) (hn : 0 < n) (a : Kˣ)
    (z : (fib K L).obj (laurentKummerArithmeticFiber n hn a)) :
    Spec.map (CommRingCat.ofHom (laurentKummerArithmeticFiberEquiv n hn a z).val) =
      (fiberObjEquivHom (ξ K L) (laurentKummerArithmeticFiber n hn a) z).left ≫
        pullback.fst (laurentKummerProjection K n) (laurentKummerPoint (L := K) a) := by
  exact Spec.map_preimage _

end AnabelianGeometry.GeometricFundamentalGroup
