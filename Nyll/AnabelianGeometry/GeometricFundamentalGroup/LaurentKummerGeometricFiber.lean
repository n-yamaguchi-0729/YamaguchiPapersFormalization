/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerFiber
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerCovers
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-!
# The geometric fibre of the actual Laurent Kummer cover

The quotient-algebra description is compared with scheme morphisms using
full faithfulness of Spec, and then with the existing geometric fibre
functor. Consequently the actual finite-etale fibre is equivalent to the
set of roots of its defining Kummer equation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u
variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- The spectrum morphism of the explicit Laurent Kummer algebra. -/
def laurentKummerProjection (K : Type u) [Field K] (n : ℕ) :
    Spec (.of (LaurentKummerAlgebra K n)) ⟶ Spec (.of (LaurentPolynomial K)) :=
  Spec.map (CommRingCat.ofHom
    (AdjoinRoot.of (X ^ n - C (LaurentPolynomial.T 1 : LaurentPolynomial K))))

/-- The geometric Laurent point determined by a nonzero scalar. -/
def laurentKummerPoint (a : Kˣ) : Spec (.of L) ⟶ Spec (.of (LaurentPolynomial K)) :=
  Spec.map (CommRingCat.ofHom (laurentScalarEvaluation (L := L) a))

/-- Scheme-valued points above the specified Laurent point. -/
def LaurentKummerSchemeFiber (n : ℕ) (a : Kˣ) :=
  {f : Spec (.of L) ⟶ Spec (.of (LaurentKummerAlgebra K n)) //
    f ≫ laurentKummerProjection K n = laurentKummerPoint (L := L) a}

/-- The affine scheme fibre points are exactly the previously constructed algebra points. -/
def laurentKummerSchemeFiberEquiv (n : ℕ) (a : Kˣ) :
    LaurentKummerSchemeFiber (L := L) n a ≃ LaurentKummerFiberHom (L := L) n a where
  toFun f := ⟨(Spec.preimage f.val).hom, by
    have h := congrArg (fun g : Spec (.of L) ⟶ Spec (.of (LaurentPolynomial K)) =>
      (Spec.preimage g).hom) f.property
    simpa only [laurentKummerProjection, laurentKummerPoint, Spec.preimage_comp,
      Spec.preimage_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h⟩
  invFun f := ⟨Spec.map (CommRingCat.ofHom f.val), by
    change Spec.map (CommRingCat.ofHom f.val) ≫
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of _)) =
        Spec.map (CommRingCat.ofHom (laurentScalarEvaluation a))
    rw [← Spec.map_comp]
    exact congrArg (fun g : LaurentPolynomial K →+* L => Spec.map (CommRingCat.ofHom g))
      f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact Spec.map_preimage f.val
  right_inv f := by
    apply Subtype.ext
    exact congrArg (fun g : CommRingCat.of (LaurentKummerAlgebra K n) ⟶ CommRingCat.of L =>
      g.hom) (Spec.preimage_map (CommRingCat.ofHom f.val))

/-- The named actual finite-etale Laurent Kummer cover of positive degree. -/
def laurentKummerCover (K : Type u) [Field K] [CharZero K]
    (n : ℕ) (hn : 0 < n) : FiniteEtale (Spec (.of (LaurentPolynomial K))) := by
  have : Module.Finite (LaurentPolynomial K) (LaurentKummerAlgebra K n) :=
    (finite_free_finrank_laurentKummerAlgebra K hn).1
  have : Algebra.Etale (LaurentPolynomial K) (LaurentKummerAlgebra K n) :=
    etale_laurentKummerAlgebra K hn
  have : IsFiniteEtale (laurentKummerProjection K n) := by
    change IsFiniteEtale (Spec.map (CommRingCat.ofHom
      (algebraMap (LaurentPolynomial K) (LaurentKummerAlgebra K n))))
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    constructor
  exact FiniteEtale.mk (laurentKummerProjection K n)

/-- Compare the actual geometric fibre functor with its scheme-valued points. -/
def laurentKummerGeometricFiberEquivScheme [CharZero K] [IsSepClosed L]
    (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    (fiber (laurentKummerPoint (L := L) a)).obj (laurentKummerCover K n hn) ≃
      LaurentKummerSchemeFiber (L := L) n a :=
  (fiberObjEquivHom (laurentKummerPoint (L := L) a) (laurentKummerCover K n hn)).trans
    { toFun := fun f => ⟨f.left, Over.w f⟩
      invFun := fun f => Over.homMk f.val f.property
      left_inv := fun f => by apply Over.OverMorphism.ext; rfl
      right_inv := fun f => by apply Subtype.ext; rfl }

/-- The actual geometric fibre of the named finite-etale cover consists
precisely of the roots of its Kummer equation. -/
def laurentKummerGeometricFiberEquivRoots [CharZero K] [IsSepClosed L]
    (n : ℕ) (hn : 0 < n) (a : Kˣ) :
    (fiber (laurentKummerPoint (L := L) a)).obj (laurentKummerCover K n hn) ≃
      {r : L // r ^ n = algebraMap K L (a : K)} :=
  ((laurentKummerGeometricFiberEquivScheme n hn a).trans
    (laurentKummerSchemeFiberEquiv n a)).trans (laurentKummerFiberEquivRoots n a)

end AnabelianGeometry.GeometricFundamentalGroup
