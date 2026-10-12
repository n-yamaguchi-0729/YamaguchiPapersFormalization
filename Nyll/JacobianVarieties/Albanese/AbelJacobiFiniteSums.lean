/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Albanese.FiniteSums
import Nyll.JacobianVarieties.Picard.Exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Abel–Jacobi finite sums and principal differences

The group law and Abel–Jacobi map constructed from the represented Picard functor
identify finite sums of geometric-fibre points with the classes of their normalized
point divisors. Hence principal differences of those divisors give the same sum.

The proof uses the actual point-difference comparison supplied by the represented
Picard construction, followed by list induction and the defining quotient for Pic⁰.
It concerns that constructed Abel–Jacobi map over algebraically closed geometric
fibres. It makes no universality claim for an arbitrary map to an abelian variety.

The imported Picard construction retains its Anthropic FLT provenance in its source.
The point-divisor construction and finite-sum argument below are new contributions.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
  NeronModelInfra GoodReductionJacobian

namespace AlgebraicCurve.CurveModel

/-- The degree-zero divisor obtained by subtracting a base point from a geometric point. -/
def pointDifference {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
    (s x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    Divisor.degZero (K := K) (F := F) :=
  ⟨Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
      sub_self]⟩

/-- The sum of point differences is the point divisor minus its degree times the base point. -/
theorem coe_sum_pointDifference {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (xs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)) :
    ((xs.map (M.pointDifference s)).sum : Divisor K F) =
      (xs.map (fun x => Finsupp.single (M.pointEquivPlace x) (1 : ℤ))).sum -
        xs.length • Finsupp.single (M.pointEquivPlace s) (1 : ℤ) := by
  induction xs with
  | nil =>
    simp only [List.map_nil, List.sum_nil, AddSubgroup.coe_zero, List.length_nil,
      zero_nsmul, sub_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, AddSubgroup.coe_add, List.length_cons]
    change (Finsupp.single (M.pointEquivPlace x) (1 : ℤ) -
      Finsupp.single (M.pointEquivPlace s) 1) +
        ((xs.map (M.pointDifference s)).sum : Divisor K F) = _
    rw [ih, add_nsmul, one_nsmul, sub_add_sub_comm]
    rw [add_comm (Finsupp.single (M.pointEquivPlace s) (1 : ℤ))]

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry.RelPicard

/-- Evaluate a relative map at a point of a geometric-fibre curve model. -/
def fibrePointImage {R : Type u} [CommRing R]
    {C A : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {a : A ⟶ Spec (CommRingCat.of R)} (q : SchemeHomOver c a)
    {K : Type u} [Field K] (i : R →+* K)
    {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
    (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i)))
    (he : e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom i)) a :=
  ⟨x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ q.1, by
    simp only [Category.assoc, q.2]
    rw [pullback.condition, ← Category.assoc e, he, ← Category.assoc x.1,
      x.2, Category.id_comp]⟩

/-- The constructed Abel–Jacobi map identifies finite sums with normalized divisor classes;
principal differences therefore leave those sums unchanged on geometric fibres. -/
theorem exists_abelJacobi_finiteSums_of_representsRelSubPic
    (R : Type u) [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase)
    (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw R D.toBase) (aj : SchemeHomOver c D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (x y : SchemeHomOver t D.toBase), L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        ∀ he : e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase,
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            (∀ xs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase),
              pts (Pic0.mk (xs.map (M.pointDifference s)).sum) =
                L.sumList (Spec.map (CommRingCat.ofHom i))
                  (xs.map (fibrePointImage c aj i M e he))) ∧
            (∀ xs ys : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase),
              Divisor.IsPrincipal
                (((xs.map (M.pointDifference s)).sum : Divisor K F) -
                  ((ys.map (M.pointDifference s)).sum : Divisor K F)) →
              L.sumList (Spec.map (CommRingCat.ofHom i))
                  (xs.map (fibrePointImage c aj i M e he)) =
                L.sumList (Spec.map (CommRingCat.ofHom i))
                  (ys.map (fibrePointImage c aj i M e he))) := by
  obtain ⟨L, aj, habelian, hcomm, hone, haj, -, hpoints⟩ :=
    exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic R c ε D h hsm hpr hgc
  refine ⟨L, aj, habelian, hcomm, hone, haj, ?_⟩
  intro K _ _ i F _ _ _ M e _ he
  obtain ⟨pts, hadd, hpoint⟩ := hpoints K i F M e he
  refine ⟨pts, hadd, ?_⟩
  intro s hs
  have hzero : pts 0 = L.one (Spec.map (CommRingCat.ofHom i)) := by
    obtain ⟨z, hz⟩ := pts.surjective (L.one (Spec.map (CommRingCat.ofHom i)))
    have hzadd := hadd 0 z
    rw [zero_add, hz, L.mul_one] at hzadd
    exact hzadd.symm
  have hsingle (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
      pts (Pic0.mk (M.pointDifference s x)) = fibrePointImage c aj i M e he x := by
    obtain ⟨Dv, hDv, hx⟩ := hpoint x s hs
    have hsame : Dv = M.pointDifference s x := Subtype.ext hDv
    rw [hsame] at hx
    exact Subtype.ext hx
  have hsum (xs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)) :
      pts (Pic0.mk (xs.map (M.pointDifference s)).sum) =
        L.sumList (Spec.map (CommRingCat.ofHom i))
          (xs.map (fibrePointImage c aj i M e he)) := by
    induction xs with
    | nil =>
      rw [List.map_nil, List.sum_nil, Pic0.mk_zero, List.map_nil, L.sumList_nil]
      exact hzero
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, Pic0.mk_add, hadd,
        List.map_cons, L.sumList_cons, hsingle, ih]
  refine ⟨hsum, ?_⟩
  intro xs ys hprincipal
  have hclass : Pic0.mk (xs.map (M.pointDifference s)).sum =
      Pic0.mk (ys.map (M.pointDifference s)).sum := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub, Divisor.mem_principal]
    exact hprincipal
  exact (hsum xs).symm.trans ((congrArg pts hclass).trans (hsum ys))

end AlgebraicGeometry.RelPicard
