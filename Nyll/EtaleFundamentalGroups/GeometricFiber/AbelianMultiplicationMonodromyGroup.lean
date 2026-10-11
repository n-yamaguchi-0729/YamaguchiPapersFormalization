/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromy
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTransitions
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTranslations
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Additivity of actual multiplication monodromy

The torsion comparison preserves the underlying scheme point. Translation by
that same point therefore acts on the actual geometric fibre by torsion
addition. Naturality of a fibre-functor automorphism against these deck
translations makes its action translation by its value at the unit. Thus
unit evaluation sends the fundamental-group product to actual torsion addition.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

private theorem scalarIdentity_specMap :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
  change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
  rw [CommRingCat.ofHom_id]
  exact Spec.map_id (CommRingCat.of K)

/-- The actual torsion point, with the identity spectrum map as base. -/
def torsionPointSection (n : ℕ+)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f :=
  ⟨(AlgPoints.toPoint t.1).1, (AlgPoints.toPoint t.1).2.trans (scalarIdentity_specMap (K := K))⟩

/-- The section underlying an algebraic torsion point is annihilated by the
same multiplication map. -/
theorem torsionPointSection_isTorsion (n : ℕ+)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
    G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) (n : ℕ)
      (torsionPointSection G hc n t) := by
  let s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K))
  let p : SchemeHomOver s f := AlgPoints.toPoint t.1
  have ht : G.nsmul s (n : ℕ) p = G.one s :=
    (AlgPoints.nsmul_eq_zero_iff (n : ℕ) t.1).mp t.2
  apply Subtype.ext
  rw [nsmul_coe_eq_comp_schemeNsmul]
  calc
    p.1 ≫ G.schemeNsmul (n : ℕ) = (G.nsmul s (n : ℕ) p).1 :=
      (nsmul_coe_eq_comp_schemeNsmul G (n : ℕ) p).symm
    _ = (G.one s).1 := congrArg Subtype.val ht
    _ = (G.one (𝟙 (Spec (CommRingCat.of K)))).1 :=
      congrArg (fun r : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) =>
        (G.one r).1) (scalarIdentity_specMap (K := K))

/-- The deck translation of the multiplication cover defined by an actual torsion point. -/
def torsionDeckTranslation [CharZero K] [IsProper f] [Smooth f] (n : ℕ+)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
    Aut (G.multiplicationCover hc n) :=
  G.multiplicationCoverTranslation hc n (torsionPointSection G hc n t)
    (torsionPointSection_isTorsion G hc n t)

variable [IsAlgClosed K] [CharZero K] [IsProper f] [Smooth f]

/-- The torsion-fibre comparison carries the actual deck translation to
addition by its defining point. -/
theorem fiberEquiv_map_torsionDeckTranslation (n : ℕ+)
    (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (z : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (G.multiplicationCover hc n)) :
    G.multiplicationCoverFiberEquivTorsion hc n
        ((FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).map
          (torsionDeckTranslation G hc n t).hom z) =
      G.multiplicationCoverFiberEquivTorsion hc n z + t := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K))
  let p : SchemeHomOver s f :=
    AlgPoints.toPoint (G.multiplicationCoverFiberEquivTorsion hc n z).1
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
  change (AlgPoints.toPoint (G.multiplicationCoverFiberEquivTorsion hc n
      ((FiniteEtale.fiber e).map (torsionDeckTranslation G hc n t).hom z)).1).1 =
    (AlgPoints.toPoint ((G.multiplicationCoverFiberEquivTorsion hc n z).1 + t.1)).1
  rw [AlgPoints.toPoint_add, G.multiplicationCoverFiberEquivTorsion_toPoint]
  have h := FiniteEtale.fiberObjEquivHom_naturality e
    (torsionDeckTranslation G hc n t).hom z
  let q : Spec (CommRingCat.of K) ⟶ A :=
    (FiniteEtale.fiberObjEquivHom e (G.multiplicationCover hc n) z).left
  let q' : Spec (CommRingCat.of K) ⟶ A :=
    (FiniteEtale.fiberObjEquivHom e (G.multiplicationCover hc n)
      ((FiniteEtale.fiber e).map (torsionDeckTranslation G hc n t).hom z)).left
  have hleft : q' = q ≫ G.translate u := congrArg
    (fun r : Over.mk e ⟶ (G.multiplicationCover hc n).toComma => r.left) h.symm
  have hp : p.1 = q :=
    G.multiplicationCoverFiberEquivTorsion_toPoint hc n z
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
theorem multiplicationCoverFiberEquivTorsion_smul (n : ℕ+)
    (g : π₁ᵉᵗ((G.one (𝟙 (Spec (CommRingCat.of K)))).1))
    (z : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (G.multiplicationCover hc n)) :
    G.multiplicationCoverFiberEquivTorsion hc n (g • z) =
      G.multiplicationMonodromy hc n g + G.multiplicationCoverFiberEquivTorsion hc n z := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let t := G.multiplicationCoverFiberEquivTorsion hc n z
  let d : Aut (G.multiplicationCover hc n) := torsionDeckTranslation G hc n t
  have hunit : G.multiplicationCoverFiberEquivTorsion hc n (G.multiplicationCoverUnit hc n) = 0 :=
    (G.multiplicationCoverFiberEquivTorsion hc n).apply_symm_apply 0
  have hz : (FiniteEtale.fiber e).map d.hom (G.multiplicationCoverUnit hc n) = z := by
    apply (G.multiplicationCoverFiberEquivTorsion hc n).injective
    exact (fiberEquiv_map_torsionDeckTranslation G hc n t (G.multiplicationCoverUnit hc n)).trans
      ((congrArg (fun x => x + t) hunit).trans (zero_add t))
  calc
    G.multiplicationCoverFiberEquivTorsion hc n (g • z) =
        G.multiplicationCoverFiberEquivTorsion hc n
          (g • (FiniteEtale.fiber e).map d.hom (G.multiplicationCoverUnit hc n)) :=
      congrArg (fun x => G.multiplicationCoverFiberEquivTorsion hc n (g • x)) hz.symm
    _ = G.multiplicationCoverFiberEquivTorsion hc n
        ((FiniteEtale.fiber e).map d.hom (g • G.multiplicationCoverUnit hc n)) := by
      rw [mulAction_naturality]
    _ = G.multiplicationMonodromy hc n g + t :=
      fiberEquiv_map_torsionDeckTranslation G hc n t (g • G.multiplicationCoverUnit hc n)

/-- Unit evaluation sends the identity of the actual fundamental group to zero. -/
theorem multiplicationMonodromy_one (n : ℕ+) :
    G.multiplicationMonodromy hc n 1 = 0 := by
  change G.multiplicationCoverFiberEquivTorsion hc n (1 • G.multiplicationCoverUnit hc n) = 0
  rw [one_smul]
  exact (G.multiplicationCoverFiberEquivTorsion hc n).apply_symm_apply 0

/-- Unit evaluation sends the actual fundamental-group product to addition
in the actual torsion subgroup of algebraic points. -/
theorem multiplicationMonodromy_mul (n : ℕ+)
    (g h : π₁ᵉᵗ((G.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    G.multiplicationMonodromy hc n (g * h) =
      G.multiplicationMonodromy hc n g + G.multiplicationMonodromy hc n h := by
  change G.multiplicationCoverFiberEquivTorsion hc n
      ((g * h) • G.multiplicationCoverUnit hc n) = _
  rw [mul_smul, G.multiplicationCoverFiberEquivTorsion_smul hc n]
  rfl

end GoodReductionJacobian.RelativeGroupLaw
