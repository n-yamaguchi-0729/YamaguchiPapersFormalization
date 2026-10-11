/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.TateModule
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import ProCGroups.Abelian.FullTateModule

/-!
# Multiplication covers and their actual torsion fibres

For a proper smooth commutative relative group law in characteristic zero,
multiplication by a positive integer is finite étale. Geometric connectedness
makes this an actual connected cover. At its unit point, its geometric fibre
is identified with the actual torsion subgroup of algebraic points, using
the pullback universal property and the existing scheme-kernel comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

include hc in
/-- The actual positive multiplication map is finite étale; its relative
dimension is obtained from smoothness and the group law. -/
theorem isFiniteEtale_schemeNsmul_of_charZero [CharZero K] [IsProper f] [Smooth f]
    (n : ℕ+) : IsFiniteEtale (G.schemeNsmul (n : ℕ)) := by
  obtain ⟨d, hd⟩ := G.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have : SmoothOfRelativeDimension d f := hd
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt n.property))
  have : Etale (G.schemeNsmul (n : ℕ)) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d (n : ℕ) hn
  have : IsProper (G.schemeNsmul (n : ℕ)) := by
    have : IsProper (G.schemeNsmul (n : ℕ) ≫ f) := by
      rw [G.schemeNsmul_over]
      infer_instance
    exact IsProper.of_comp _ f
  have : LocallyQuasiFinite (G.schemeNsmul (n : ℕ)) :=
    locallyQuasiFinite_of_etale (G.schemeNsmul (n : ℕ))
  have : IsFinite (G.schemeNsmul (n : ℕ)) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  exact IsFiniteEtale.mk

/-- The finite étale cover whose actual scheme morphism is multiplication by `n`. -/
def multiplicationCover [CharZero K] [IsProper f] [Smooth f] (n : ℕ+) : FiniteEtale A := by
  have : IsFiniteEtale (G.schemeNsmul (n : ℕ)) :=
    G.isFiniteEtale_schemeNsmul_of_charZero hc n
  exact FiniteEtale.mk (G.schemeNsmul (n : ℕ))

/-- Geometric connectedness of the group scheme makes its multiplication cover connected. -/
theorem isConnected_multiplicationCover [CharZero K] [IsProper f] [Smooth f]
    [GeometricallyConnected f] (n : ℕ+) : IsConnected (G.multiplicationCover hc n) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : ConnectedSpace (G.multiplicationCover hc n).left :=
    inferInstanceAs (ConnectedSpace A)
  exact FiniteEtale.isConnected_of_connectedSpace_left (G.multiplicationCover hc n)

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
def multiplicationCoverFiberEquivTorsion [IsAlgClosed K] [CharZero K] [IsProper f] [Smooth f]
    (n : ℕ+) :
    (FiniteEtale.fiber (G.one (𝟙 (Spec (CommRingCat.of K)))).1).obj
        (G.multiplicationCover hc n) ≃ ProCGroups.torsionLevel (G.AlgPoints hc K) n := by
  let e : Spec (CommRingCat.of K) ⟶ A := (G.one (𝟙 _)).1
  let C : FiniteEtale A := G.multiplicationCover hc n
  let e₁ : (FiniteEtale.fiber e).obj C ≃ SchemeHomOver e (G.schemeNsmul (n : ℕ)) :=
    (FiniteEtale.fiberObjEquivHom e C).trans
      (schemeHomOverEquivOverHom e (G.schemeNsmul (n : ℕ))).symm
  exact (e₁.trans (pointOverEquivKernelSection (G.schemeNsmul (n : ℕ)) e)).trans
    (G.torsionLevelEquivSchemeKerPoints hc n).symm

end GoodReductionJacobian.RelativeGroupLaw
