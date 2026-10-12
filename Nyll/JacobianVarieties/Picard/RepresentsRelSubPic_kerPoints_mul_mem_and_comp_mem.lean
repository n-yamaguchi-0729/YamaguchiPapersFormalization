/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Multiplication and endomorphisms of points reducing to the identity

Naturality of a relative group law makes its reduction kernel closed under multiplication.
Every multiplicative endomorphism preserves that kernel.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.KernelPointMultiplication

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (RelativePic0Designation schemeHomOverComp RelativeGroupLaw)

namespace RelativeGroupLaw

export _root_.GoodReductionJacobian.RelativeGroupLaw (pointGroup one mul_natural one_mul mul)


open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian


section ReducesToOne

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)
  {T T₀ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₀ : T₀ ⟶ Spec (CommRingCat.of R)}
  (r : T₀ ⟶ T) (hr : r ≫ t = t₀)

theorem comp_eq_one_iff (x : SchemeHomOver t f) :
    r ≫ x.1 = (L.one t₀).1 ↔ GoodReductionJacobian.schemeHomOverComp r hr x = L.one t₀ :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

include hr in
theorem comp_mul_eq_one_of_comp_eq_one (x y : SchemeHomOver t f)
    (hx : r ≫ x.1 = (L.one t₀).1) (hy : r ≫ y.1 = (L.one t₀).1) :
    r ≫ (L.mul t x y).1 = (L.one t₀).1 := by
  rw [comp_eq_one_iff L r hr] at hx hy ⊢
  rw [L.mul_natural t t₀ r hr, hx, hy, L.one_mul]

theorem hom_one (φ : SchemeHomOver f f)
    (hφ : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
        L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one s) φ = L.one s := by
  let := L.pointGroup s
  have h := hφ s (L.one s) (L.one s)
  rw [L.one_mul] at h
  have h' : (NeronModelInfra.schemeHomOverComp (L.one s) φ : SchemeHomOver s f) =
      NeronModelInfra.schemeHomOverComp (L.one s) φ *
        NeronModelInfra.schemeHomOverComp (L.one s) φ := h
  exact (left_eq_mul.mp h').symm ▸ rfl

theorem comp_comp_hom_eq_one_of_comp_eq_one (φ : SchemeHomOver f f)
    (hφ : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
        L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    (x : SchemeHomOver t f) (hx : r ≫ x.1 = (L.one t₀).1) :
    r ≫ (x.1 ≫ φ.1) = (L.one t₀).1 := by
  rw [← Category.assoc, hx]
  exact congrArg Subtype.val (hom_one L φ hφ t₀)

end ReducesToOne

end GoodReductionJacobian.RelativeGroupLaw

theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    let tε := Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
    let t₀ := Scheme.TwoAffineOpenCover.specMap R A
    (∀ x y : SchemeHomOver tε D.toBase,
        dualNumberReduction R A ≫ x.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ y.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ (L.mul tε x y).1 = (L.one t₀).1) ∧
    (∀ (φ : SchemeHomOver D.toBase D.toBase),
        (∀ {T : Scheme.{u}} (s : T ⟶ Spec (.of R)) (x y : SchemeHomOver s D.toBase),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ)
              (NeronModelInfra.schemeHomOverComp y φ)) →
        ∀ x : SchemeHomOver tε D.toBase, dualNumberReduction R A ≫ x.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ (x.1 ≫ φ.1) = (L.one t₀).1) := by
  intro L tε t₀
  refine ⟨fun x y hx hy => ?_, fun φ hφ x hx => ?_⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_one_of_comp_eq_one L
      (dualNumberReduction R A)
      (dualNumberReduction_comp_specMap R A) x y hx hy
  · exact GoodReductionJacobian.RelativeGroupLaw.comp_comp_hom_eq_one_of_comp_eq_one L
      (dualNumberReduction R A)
      φ hφ x hx
end JacobianVarieties.Picard.Proofs.KernelPointMultiplication
end ProofImplementation
