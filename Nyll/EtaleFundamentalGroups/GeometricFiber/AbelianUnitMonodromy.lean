/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitTorsionFiber
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperGroupScheme
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Monodromy at actual torsion points in arbitrary characteristic

For every invertible positive integer, the actual multiplication fibre is a
torsor under its torsion points. Deck translations prove that unit monodromy
is an additive map to the actual torsion group.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue
open scoped FintypeCatDiscrete

namespace GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication

variable {K : Type} [Field K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

private theorem scalarIdentity_specMap :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
  change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
  rw [CommRingCat.ofHom_id]
  exact Spec.map_id (CommRingCat.of K)

private def torsionPointSection (n : unitIndices K)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n.1) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f :=
  ⟨(AlgPoints.toPoint t.1).1, (AlgPoints.toPoint t.1).2.trans (scalarIdentity_specMap (K := K))⟩

private theorem torsionPointSection_isTorsion (n : unitIndices K)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n.1) :
    G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) (n.1 : ℕ)
      (torsionPointSection G hc n t) := by
  let s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K))
  let p : SchemeHomOver s f := AlgPoints.toPoint t.1
  have ht : G.nsmul s (n.1 : ℕ) p = G.one s :=
    (AlgPoints.nsmul_eq_zero_iff (n.1 : ℕ) t.1).mp t.2
  apply Subtype.ext
  rw [nsmul_coe_eq_comp_schemeNsmul]
  calc
    p.1 ≫ G.schemeNsmul (n.1 : ℕ) = (G.nsmul s (n.1 : ℕ) p).1 :=
      (nsmul_coe_eq_comp_schemeNsmul G (n.1 : ℕ) p).symm
    _ = (G.one s).1 := congrArg Subtype.val ht
    _ = (G.one (𝟙 (Spec (CommRingCat.of K)))).1 :=
      congrArg (fun r : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) =>
        (G.one r).1) (scalarIdentity_specMap (K := K))

variable [IsSepClosed K] [IsProper f] [Smooth f]

/-- The unit in the actual geometric fibre of the multiplication cover. -/
def unit (n : unitIndices K) :
    (fiber (G.one (𝟙 (Spec (.of K)))).1).obj (cover G hc n) :=
  (fiberEquivTorsion G hc n).symm 0

/-- Evaluation of actual monodromy at the unit, expressed in actual torsion points. -/
def monodromy (n : unitIndices K)
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    ProCGroups.torsionLevel (G.AlgPoints hc K) n.1 :=
  fiberEquivTorsion G hc n (g • unit G hc n)

/-- Connectedness of the multiplication cover makes unit evaluation surjective. -/
theorem monodromy_surjective [GeometricallyConnected f] (n : unitIndices K) :
    Function.Surjective (monodromy G hc n) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : IsConnected (cover G hc n) := isConnected_cover G hc n
  intro x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) (unit G hc n)
      ((fiberEquivTorsion G hc n).symm x)
  refine ⟨g, ?_⟩
  exact (congrArg (fiberEquivTorsion G hc n) hg).trans
    ((fiberEquivTorsion G hc n).apply_symm_apply x)

local instance (n : ℕ+) : TopologicalSpace (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
  ProCGroups.FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n

/-- Unit evaluation is continuous for the discrete topology on actual torsion points. -/
theorem monodromy_continuous (n : unitIndices K) :
    Continuous (monodromy G hc n) := by
  exact (continuous_of_discreteTopology :
    Continuous (fiberEquivTorsion G hc n)).comp
      (continuous_id.smul continuous_const)

private def torsionDeckTranslation (n : unitIndices K)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n.1) :
    Aut (cover G hc n) :=
  translation G hc n (torsionPointSection G hc n t)
    (torsionPointSection_isTorsion G hc n t)


private theorem fiberEquiv_map_torsionDeckTranslation (n : unitIndices K)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n.1)
    (z : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (cover G hc n)) :
    fiberEquivTorsion G hc n
        ((FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).map
          (torsionDeckTranslation G hc n t).hom z) =
      fiberEquivTorsion G hc n z + t := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K))
  let p : SchemeHomOver s f :=
    AlgPoints.toPoint (fiberEquivTorsion G hc n z).1
  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f := torsionPointSection G hc n t
  have hu : GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) u =
      AlgPoints.toPoint t.1 := by
    apply Subtype.ext
    change s ≫ (AlgPoints.toPoint t.1).1 = (AlgPoints.toPoint t.1).1
    exact (congrArg (fun r : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) =>
      r ≫ (AlgPoints.toPoint t.1).1) (scalarIdentity_specMap (K := K))).trans
        (Category.id_comp (AlgPoints.toPoint t.1).1)
  apply Subtype.ext
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change (AlgPoints.toPoint (fiberEquivTorsion G hc n
      ((FiniteEtale.fiber e).map (torsionDeckTranslation G hc n t).hom z)).1).1 =
    (AlgPoints.toPoint ((fiberEquivTorsion G hc n z).1 + t.1)).1
  rw [AlgPoints.toPoint_add, fiberEquivTorsion_toPoint G]
  have h := FiniteEtale.fiberObjEquivHom_naturality e
    (torsionDeckTranslation G hc n t).hom z
  let q : Spec (CommRingCat.of K) ⟶ A :=
    (FiniteEtale.fiberObjEquivHom e (cover G hc n) z).left
  let q' : Spec (CommRingCat.of K) ⟶ A :=
    (FiniteEtale.fiberObjEquivHom e (cover G hc n)
      ((FiniteEtale.fiber e).map (torsionDeckTranslation G hc n t).hom z)).left
  have hleft : q' = q ≫ G.translate u := congrArg
    (fun r : Over.mk e ⟶ (cover G hc n).toComma => r.left) h.symm
  have hp : p.1 = q :=
    fiberEquivTorsion_toPoint G hc n z
  change q' = (G.mul s p (AlgPoints.toPoint t.1)).1
  calc
    q' = q ≫ G.translate u := hleft
    _ = p.1 ≫ G.translate u := congrArg (fun q : Spec (CommRingCat.of K) ⟶ A =>
      q ≫ G.translate u) hp.symm
    _ = (G.mul s p
        (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) u)).1 :=
      G.point_comp_translate s p u
    _ = (G.mul s p (AlgPoints.toPoint t.1)).1 :=
      congrArg (fun q : SchemeHomOver s f => (G.mul s p q).1) hu

/-- Actual monodromy on every point of a multiplication fibre is addition by
its value at the unit, under the actual torsion comparison. -/
theorem fiberEquivTorsion_smul (n : unitIndices K)
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (CommRingCat.of K)))).1))
    (z : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (cover G hc n)) :
    fiberEquivTorsion G hc n (g • z) =
      monodromy G hc n g + fiberEquivTorsion G hc n z := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let t := fiberEquivTorsion G hc n z
  let d : Aut (cover G hc n) := torsionDeckTranslation G hc n t
  have hunit : fiberEquivTorsion G hc n (unit G hc n) = 0 :=
    (fiberEquivTorsion G hc n).apply_symm_apply 0
  have hz : (FiniteEtale.fiber e).map d.hom (unit G hc n) = z := by
    apply (fiberEquivTorsion G hc n).injective
    exact (fiberEquiv_map_torsionDeckTranslation G hc n t (unit G hc n)).trans
      ((congrArg (fun x => x + t) hunit).trans (zero_add t))
  calc
    fiberEquivTorsion G hc n (g • z) =
        fiberEquivTorsion G hc n
          (g • (FiniteEtale.fiber e).map d.hom (unit G hc n)) :=
      congrArg (fun x => fiberEquivTorsion G hc n (g • x)) hz.symm
    _ = fiberEquivTorsion G hc n
        ((FiniteEtale.fiber e).map d.hom (g • unit G hc n)) := by
      rw [mulAction_naturality]
    _ = monodromy G hc n g + t :=
      fiberEquiv_map_torsionDeckTranslation G hc n t (g • unit G hc n)

/-- Unit evaluation sends the identity of the actual fundamental group to zero. -/
theorem monodromy_one (n : unitIndices K) :
    monodromy G hc n 1 = 0 := by
  change fiberEquivTorsion G hc n (1 • unit G hc n) = 0
  rw [one_smul]
  exact (fiberEquivTorsion G hc n).apply_symm_apply 0

/-- Unit evaluation sends the actual fundamental-group product to addition
in the actual torsion subgroup of algebraic points. -/
theorem monodromy_mul (n : unitIndices K)
    (g h : π₁ᵉᵗ((G.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    monodromy G hc n (g * h) =
      monodromy G hc n g + monodromy G hc n h := by
  change fiberEquivTorsion G hc n
      ((g * h) • unit G hc n) = _
  rw [mul_smul, fiberEquivTorsion_smul G hc n]
  rfl

/-- Unit evaluation as a continuous homomorphism to the actual finite torsion group. -/
def monodromyHom (n : unitIndices K) :
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →ₜ*
      Multiplicative (ProCGroups.torsionLevel (G.AlgPoints hc K) n.1) where
  toFun g := Multiplicative.ofAdd (monodromy G hc n g)
  map_one' := congrArg Multiplicative.ofAdd (monodromy_one G hc n)
  map_mul' g h := congrArg Multiplicative.ofAdd (monodromy_mul G hc n g h)
  continuous_toFun := monodromy_continuous G hc n

end GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
