/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.TateModule
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Multiplication covers and Tate transitions

Multiplication by `m` gives an actual morphism from the `(n*m)` multiplication
cover to the `n` multiplication cover. Under the identification of their
geometric fibres with torsion points, this morphism induces the multiplication
transition used in the full Tate module.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

private theorem nsmul_nsmul_point {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n m : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t n (G.nsmul t m x) = G.nsmul t (m * n) x := by
  let : Group (SchemeHomOver t f) := G.pointGroup t
  have hp (k : ℕ) (y : SchemeHomOver t f) : G.nsmul t k y = y ^ k := by
    induction k with
    | zero => exact (pow_zero y).symm
    | succ k ih =>
      rw [G.nsmul_succ, ih]
      exact (pow_succ y k).symm
  rw [hp, hp, hp, pow_mul]

/-- Composition of the actual multiplication morphisms multiplies their indices. -/
theorem schemeNsmul_comp_schemeNsmul (m n : ℕ) :
    G.schemeNsmul m ≫ G.schemeNsmul n = G.schemeNsmul (m * n) := by
  calc
    G.schemeNsmul m ≫ G.schemeNsmul n =
        (G.nsmul f n (G.nsmul f m idPoint)).1 :=
      (nsmul_coe_eq_comp_schemeNsmul G n (G.nsmul f m idPoint)).symm
    _ = G.schemeNsmul (m * n) :=
      congrArg Subtype.val (nsmul_nsmul_point G f n m idPoint)

/-- The actual multiplication map `[m]` between the multiplication covers. -/
def multiplicationCoverTransition [CharZero K] [IsProper f] [Smooth f] (n m : ℕ+) :
    G.multiplicationCover hc (n * m) ⟶ G.multiplicationCover hc n :=
  MorphismProperty.Over.homMk (G.schemeNsmul (m : ℕ)) (by
    change G.schemeNsmul (m : ℕ) ≫ G.schemeNsmul (n : ℕ) =
      G.schemeNsmul ((n : ℕ) * (m : ℕ))
    rw [G.schemeNsmul_comp_schemeNsmul, Nat.mul_comm])

/-- The fibre comparison identifies the same actual scheme point, including the
transport from the scalar identity to the scheme identity. -/
theorem multiplicationCoverFiberEquivTorsion_toPoint
    [IsAlgClosed K] [CharZero K] [IsProper f] [Smooth f] (n : ℕ+)
    (x : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (G.multiplicationCover hc n)) :
    (AlgPoints.toPoint (G.multiplicationCoverFiberEquivTorsion hc n x).1).1 =
      (FiniteEtale.fiberObjEquivHom (G.one (𝟙 (Spec (CommRingCat.of K)))).1
        (G.multiplicationCover hc n) x).left := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let p : Over.mk e ⟶ (G.multiplicationCover hc n).toComma :=
    FiniteEtale.fiberObjEquivHom e (G.multiplicationCover hc n) x
  let s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (G.schemeKerStr (n : ℕ)) :=
    ⟨pullback.lift p.left (𝟙 _) (p.w.trans (Category.id_comp e).symm),
      pullback.lift_snd _ _ _⟩
  have hs : G.torsionLevelEquivSchemeKerPoints hc n
      (G.multiplicationCoverFiberEquivTorsion hc n x) = s :=
    (G.torsionLevelEquivSchemeKerPoints hc n).apply_symm_apply s
  have h₁ : (AlgPoints.toPoint (G.multiplicationCoverFiberEquivTorsion hc n x).1).1 =
      (G.torsionLevelEquivSchemeKerPoints hc n
        (G.multiplicationCoverFiberEquivTorsion hc n x)).1 ≫
        pullback.fst (G.schemeNsmul (n : ℕ)) e :=
    (G.torsionLevelEquivSchemeKerPoints_comp_fst hc n _).symm
  have h₂ : (G.torsionLevelEquivSchemeKerPoints hc n
      (G.multiplicationCoverFiberEquivTorsion hc n x)).1 ≫
      pullback.fst (G.schemeNsmul (n : ℕ)) e =
      s.1 ≫ pullback.fst (G.schemeNsmul (n : ℕ)) e :=
    congrArg (fun q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (G.schemeKerStr (n : ℕ)) => q.1 ≫ pullback.fst (G.schemeNsmul (n : ℕ)) e) hs
  have h₃ : s.1 ≫ pullback.fst (G.schemeNsmul (n : ℕ)) e = p.left :=
    pullback.lift_fst p.left (𝟙 (Spec (CommRingCat.of K)))
      (p.w.trans (Category.id_comp e).symm)
  exact h₁.trans (h₂.trans h₃)

/-- The actual geometric-fibre map of `[m]` is exactly the full Tate transition. -/
theorem multiplicationCoverFiberEquivTorsion_transition
    [IsAlgClosed K] [CharZero K] [IsProper f] [Smooth f] (n m : ℕ+)
    (x : (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
      (G.multiplicationCover hc (n * m))) :
    G.multiplicationCoverFiberEquivTorsion hc n
        ((FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).map
          (G.multiplicationCoverTransition hc n m) x) =
      ProCGroups.torsionTransition (G.AlgPoints hc K) n m
        (G.multiplicationCoverFiberEquivTorsion hc (n * m) x) := by
  apply Subtype.ext
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change (AlgPoints.toPoint (G.multiplicationCoverFiberEquivTorsion hc n
      ((FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).map
        (G.multiplicationCoverTransition hc n m) x)).1).1 =
    (AlgPoints.toPoint ((m : ℕ) •
      (G.multiplicationCoverFiberEquivTorsion hc (n * m) x).1)).1
  rw [AlgPoints.toPoint_nsmul, nsmul_coe_eq_comp_schemeNsmul,
    G.multiplicationCoverFiberEquivTorsion_toPoint,
    G.multiplicationCoverFiberEquivTorsion_toPoint]
  exact (congrArg (fun h => h.left)
    (FiniteEtale.fiberObjEquivHom_naturality
      (G.one (𝟙 (Spec (CommRingCat.of K)))).1
      (G.multiplicationCoverTransition hc n m) x)).symm

end GoodReductionJacobian.RelativeGroupLaw
