/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationCover
import EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTransitions
import EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTranslations
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.TateModule
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.Algebra.Group.Submonoid.Defs

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import ProCGroups.Abelian.FullTateModule

/-!
# Actual torsion fibres of invertible multiplication covers

The indices form the multiplicative submonoid of positive integers invertible
in the ground field. The actual fibre comparison and its transition formula
work in arbitrary characteristic over a separably closed field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication

/-- The positive multiplication indices invertible in the ground field. -/
def unitIndices (K : Type) [Field K] : Submonoid ℕ+ where
  carrier := {n | IsUnit ((n : ℕ) : K)}
  one_mem' := by
    change IsUnit ((1 : ℕ) : K)
    rw [Nat.cast_one]
    exact isUnit_one
  mul_mem' := by
    intro a b ha hb
    change IsUnit (((a : ℕ) * (b : ℕ) : ℕ) : K)
    rw [Nat.cast_mul]
    exact ha.mul hb

variable {K : Type} [Field K] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of K)}
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The actual multiplication cover at an allowed index. -/
def cover [IsProper f] [Smooth f] (n : unitIndices K) : FiniteEtale A :=
  G.unitMultiplicationCover hc (n.1 : ℕ) n.2

/-- The allowed multiplication cover is connected when the group is geometrically connected. -/
theorem isConnected_cover [IsProper f] [Smooth f] [GeometricallyConnected f]
    (n : unitIndices K) : IsConnected (cover G hc n) :=
  G.isConnected_unitMultiplicationCover hc (n.1 : ℕ) n.2

private def pointOverEquivKernelSection (a : A ⟶ A) (e : Spec (CommRingCat.of K) ⟶ A) :
    SchemeHomOver e a ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (pullback.snd a e) where
  toFun x := ⟨pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp e).symm),
    pullback.lift_snd _ _ _⟩
  invFun z := ⟨z.1 ≫ pullback.fst a e, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]⟩
  left_inv x := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  right_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd]
      exact z.2.symm

/-- The actual geometric fibre at the unit of the multiplication cover is
the actual torsion subgroup of algebraic points. -/
def fiberEquivTorsion [IsSepClosed K] [IsProper f] [Smooth f]
    (n : unitIndices K) :
    (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
        (cover G hc n) ≃ ProCGroups.torsionLevel (G.AlgPoints hc K) n.1 := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let C : FiniteEtale A := cover G hc n
  let e₁ : (FiniteEtale.fiber e).obj C ≃ SchemeHomOver e (G.schemeNsmul (n.1 : ℕ)) :=
    (FiniteEtale.fiberObjEquivHom e C).trans
      (schemeHomOverEquivOverHom e (G.schemeNsmul (n.1 : ℕ))).symm
  exact (e₁.trans (pointOverEquivKernelSection (G.schemeNsmul (n.1 : ℕ)) e)).trans
    (G.torsionLevelEquivSchemeKerPoints hc n.1).symm


/-- The actual multiplication map `[m]` between the multiplication covers. -/
def transition [IsProper f] [Smooth f] (n m : unitIndices K) :
    cover G hc (n * m) ⟶ cover G hc n :=
  MorphismProperty.Over.homMk (G.schemeNsmul (m.1 : ℕ)) (by
    change G.schemeNsmul (m.1 : ℕ) ≫ G.schemeNsmul (n.1 : ℕ) =
      G.schemeNsmul ((n.1 : ℕ) * (m.1 : ℕ))
    rw [G.schemeNsmul_comp_schemeNsmul, Nat.mul_comm])

/-- The fibre comparison identifies the same actual scheme point, including the
transport from the scalar identity to the scheme identity. -/
theorem fiberEquivTorsion_toPoint
    [IsSepClosed K] [IsProper f] [Smooth f] (n : unitIndices K)
    (x : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (cover G hc n)) :
    (AlgPoints.toPoint (fiberEquivTorsion G hc n x).1).1 =
      (FiniteEtale.fiberObjEquivHom (G.one (𝟙 (Spec (CommRingCat.of K)))).1
        (cover G hc n) x).left := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let p : Over.mk e ⟶ (cover G hc n).toComma :=
    FiniteEtale.fiberObjEquivHom e (cover G hc n) x
  let s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (G.schemeKerStr (n.1 : ℕ)) :=
    ⟨pullback.lift p.left (𝟙 _) (p.w.trans (Category.id_comp e).symm),
      pullback.lift_snd _ _ _⟩
  have hs : G.torsionLevelEquivSchemeKerPoints hc n.1
      (fiberEquivTorsion G hc n x) = s :=
    (G.torsionLevelEquivSchemeKerPoints hc n.1).apply_symm_apply s
  have h₁ : (AlgPoints.toPoint (fiberEquivTorsion G hc n x).1).1 =
      (G.torsionLevelEquivSchemeKerPoints hc n.1
        (fiberEquivTorsion G hc n x)).1 ≫
        pullback.fst (G.schemeNsmul (n.1 : ℕ)) e :=
    (G.torsionLevelEquivSchemeKerPoints_comp_fst hc n.1 _).symm
  have h₂ : (G.torsionLevelEquivSchemeKerPoints hc n.1
      (fiberEquivTorsion G hc n x)).1 ≫
      pullback.fst (G.schemeNsmul (n.1 : ℕ)) e =
      s.1 ≫ pullback.fst (G.schemeNsmul (n.1 : ℕ)) e :=
    congrArg (fun q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (G.schemeKerStr (n.1 : ℕ)) => q.1 ≫ pullback.fst (G.schemeNsmul (n.1 : ℕ)) e) hs
  have h₃ : s.1 ≫ pullback.fst (G.schemeNsmul (n.1 : ℕ)) e = p.left :=
    pullback.lift_fst p.left (𝟙 (Spec (CommRingCat.of K)))
      (p.w.trans (Category.id_comp e).symm)
  exact h₁.trans (h₂.trans h₃)

/-- The actual geometric-fibre map of `[m]` is exactly the full Tate transition. -/
theorem fiberEquivTorsion_transition
    [IsSepClosed K] [IsProper f] [Smooth f] (n m : unitIndices K)
    (x : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (cover G hc (n * m))) :
    fiberEquivTorsion G hc n
        ((FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).map
          (transition G hc n m) x) =
      ProCGroups.torsionTransition (G.AlgPoints hc K) n.1 m.1
        (fiberEquivTorsion G hc (n * m) x) := by
  apply Subtype.ext
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change (AlgPoints.toPoint (fiberEquivTorsion G hc n
      ((FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).map
        (transition G hc n m) x)).1).1 =
    (AlgPoints.toPoint ((m.1 : ℕ) •
      (fiberEquivTorsion G hc (n * m) x).1)).1
  rw [AlgPoints.toPoint_nsmul, nsmul_coe_eq_comp_schemeNsmul,
    fiberEquivTorsion_toPoint G,
    fiberEquivTorsion_toPoint G]
  exact (congrArg (fun h => h.left)
    (FiniteEtale.fiberObjEquivHom_naturality
      (G.one (𝟙 (Spec (CommRingCat.of K)))).1
      (transition G hc n m) x)).symm

/-- Translation by an actual torsion section is a deck automorphism of the allowed cover. -/
def translation [IsProper f] [Smooth f] (n : unitIndices K)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (ht : G.IsTorsionPoint (𝟙 _) (n.1 : ℕ) t) : Aut (cover G hc n) :=
  MorphismProperty.Over.isoMk (G.translateIso t)
    (G.translate_comp_schemeNsmul hc (n.1 : ℕ) t ht)

/-- Every allowed actual torsion group is finite over a separably closed field. -/
theorem finite_torsionLevel [IsSepClosed K] [IsProper f] [Smooth f]
    (n : unitIndices K) : Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n.1) :=
  Finite.of_equiv _ (fiberEquivTorsion G hc n)

end GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
