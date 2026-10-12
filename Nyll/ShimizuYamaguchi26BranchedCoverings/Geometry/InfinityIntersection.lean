/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Set.Image
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring

/-!
# Intersection with the section at infinity

On the affine chart with coordinate `w = T₁ / T₀`, the equations of the
section at infinity and a section given by a primitive pair `(u,v)` are
`w` and `v - u*w`. The affine intersection of these equations has coordinate ring
`R[w] / (w, v-u*w)`.

The actual quotient algebra is identified with `R / (v)`. When the coefficient
ring is a DVR, its length as an `R[w]`-module is the additive valuation of `v`.
Both the isomorphism and the equality of lengths are proved from the two
equations; no intersection comparison is supplied as an assumption.

This is the affine algebra calculation in Lemma 2.3 of Ryoji Shimizu and
Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The projective-stalk calculation and the integer `p`-adic normalization are
developed in `ProjectiveInfinityIntersection`; the primitive section images
are constructed in `RationalSection`. Identifying the original global section
ideals in the local chart and the normal-crossing criterion remains separate.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

universe u

variable {R : Type u} [CommRing R]

/-- The ideal of the two section equations on the chart with coordinate `w`. -/
def infinityIntersectionIdeal (u v : R) : Ideal R[X] :=
  Ideal.span {Polynomial.X, Polynomial.C v - Polynomial.C u * Polynomial.X}

/-- Extending coefficients preserves the two concrete intersection equations. -/
theorem infinityIntersectionIdeal_map {S : Type*} [CommRing S] (f : R →+* S) (u v : R) :
    (infinityIntersectionIdeal u v).map (Polynomial.mapRingHom f) =
      infinityIntersectionIdeal (f u) (f v) := by
  simp only [infinityIntersectionIdeal, Ideal.map_span, Set.image_pair,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C]

/-- Eliminating the chart coordinate leaves exactly the denominator equation. -/
theorem infinityIntersectionIdeal_eq (u v : R) :
    infinityIntersectionIdeal u v = Ideal.span {Polynomial.C v, Polynomial.X} := by
  unfold infinityIntersectionIdeal
  have heq : Polynomial.C v - Polynomial.C u * Polynomial.X =
      Polynomial.X * (-Polynomial.C u) + Polynomial.C v := by ring
  rw [heq, Ideal.span_pair_left_mul_add, Ideal.span_pair_comm]

/-- The actual affine intersection algebra of the two section equations. -/
abbrev InfinityIntersectionAlgebra (u v : R) := R[X] ⧸ infinityIntersectionIdeal u v

/-- Evaluation at zero constructs the affine intersection algebra as `R / (v)`. -/
def infinityIntersectionEquiv (u v : R) :
    InfinityIntersectionAlgebra u v ≃ₐ[R] R ⧸ Ideal.span {v} :=
  (Ideal.quotientEquivAlgOfEq R
    (show infinityIntersectionIdeal u v =
        Ideal.span {Polynomial.C v, Polynomial.X - Polynomial.C (0 : R)} by
      rw [infinityIntersectionIdeal_eq, Polynomial.C_0, sub_zero])).trans
    (Polynomial.quotientSpanCXSubCAlgEquiv v (0 : R))

/-- The affine intersection is the spectrum of the actual denominator quotient. -/
def infinityIntersectionIso (u v : R) :
    Spec (CommRingCat.of (InfinityIntersectionAlgebra u v)) ≅
      Spec (CommRingCat.of (R ⧸ Ideal.span {v})) :=
  (Scheme.Spec.mapIso (infinityIntersectionEquiv u v).toRingEquiv.toCommRingCatIso.op).symm

/-- Every intersection-algebra element is the image of a coefficient. -/
theorem infinityIntersection_algebraMap_surjective (u v : R) :
    Function.Surjective (algebraMap R (InfinityIntersectionAlgebra u v)) := by
  intro q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((infinityIntersectionEquiv u v) q)
  refine ⟨r, ?_⟩
  apply (infinityIntersectionEquiv u v).injective
  rw [(infinityIntersectionEquiv u v).commutes]
  exact hr

/-- The polynomial-ring length of the affine intersection equals its coefficient-ring length.
The comparison follows from the two actual surjective coefficient maps. -/
theorem infinityIntersection_length_eq_base (u v : R) :
    Module.length R[X] (InfinityIntersectionAlgebra u v) =
      Module.length R (InfinityIntersectionAlgebra u v) := by
  calc
    _ = Module.length (InfinityIntersectionAlgebra u v)
        (InfinityIntersectionAlgebra u v) :=
      Module.length_eq_of_surjective (S := R[X])
        (R := InfinityIntersectionAlgebra u v) (M := InfinityIntersectionAlgebra u v)
        (Ideal.Quotient.mk_surjective)
    _ = Module.length R (InfinityIntersectionAlgebra u v) :=
      (Module.length_eq_of_surjective (S := R)
        (R := InfinityIntersectionAlgebra u v) (M := InfinityIntersectionAlgebra u v)
        (infinityIntersection_algebraMap_surjective u v)).symm

/-- On a DVR coefficient ring, the affine intersection length is the valuation of `v`.
This includes the infinite length when `v = 0`, so no hidden distinctness assumption
is needed for the algebra calculation. -/
theorem infinityIntersection_length [IsDomain R] [IsDiscreteValuationRing R] (u v : R) :
    Module.length R[X] (InfinityIntersectionAlgebra u v) =
      IsDiscreteValuationRing.addVal R v := by
  rw [infinityIntersection_length_eq_base,
    (infinityIntersectionEquiv u v).toLinearEquiv.length_eq, Module.length_quotient]
  calc
    Order.coheight (Ideal.span {v}) =
        IsDiscreteValuationRing.addVal R (Submodule.IsPrincipal.generator (Ideal.span {v})) := by
      simpa only [IsDiscreteValuationRing.idealOrderIsoENat_apply,
        Order.coheight_toDual, Order.height_enat] using
        (Order.coheight_orderIso (IsDiscreteValuationRing.idealOrderIsoENat R)
          (Ideal.span {v})).symm
    _ = IsDiscreteValuationRing.addVal R v :=
      (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
        (Submodule.IsPrincipal.associated_generator_span_self v)

end ShimizuYamaguchi26BranchedCoverings
