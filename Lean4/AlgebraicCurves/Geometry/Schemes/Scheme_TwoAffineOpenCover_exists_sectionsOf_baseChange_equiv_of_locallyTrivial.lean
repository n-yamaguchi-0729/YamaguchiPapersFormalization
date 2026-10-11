/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial

/-!
# Base change of sections on two affine charts

A locally trivial module has scalar-extension equivalences for sections on the two
affine charts and their overlap, compatible with restrictions and adjunction units.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace SectionsBCDatum
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)
variable (A : Type u) [CommRing A] [Algebra R A]

theorem unit_res {U U' : X.Opens} (h : U' ≤ U)
    (h' : (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U' ≤ (Limits.pullback.fst c (specMap R A))
        ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst c (specMap R
        A))).unit.app M).app U'
        (M.presheaf.map (homOfLE h).op m)
      = ((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M).presheaf.map
          (homOfLE h').op
          (show Γ((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M,
              (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst c (specMap R
                A))).unit.app M).app U m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst c (specMap R A))).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map (Limits.pullback.fst c (specMap R A)).base).map (homOfLE
      h)) = homOfLE h' :=
    Subsingleton.elim _ _
  change (((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M).presheaf.map
    ((TopologicalSpace.Opens.map (Limits.pullback.fst c (specMap R A)).base).map (homOfLE
        h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {N : Type u} [AddCommGroup N] [Module R N] (a : A) (n : N) :
    a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.SectionsBCDatum

open AlgebraicGeometry.Scheme.TwoAffineOpenCover.SectionsBCDatum in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
theorem exists_sectionsOf_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : A ⊗[R] (𝒱.sectionsOf c M).M0 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
              R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap
                R A))).obj M)).M0)
      (e1 : A ⊗[R] (𝒱.sectionsOf c M).M1 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
              R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap
                R A))).obj M)).M1)
      (e01 : A ⊗[R] (𝒱.sectionsOf c M).M01 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap
              R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap
                R A))).obj M)).M01),
      (∀ x, e01 (((𝒱.sectionsOf c M).r0.baseChange A) x) =
        ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R
              A))).obj M)).r0
            (e0 x)) ∧
      (∀ x, e01 (((𝒱.sectionsOf c M).r1.baseChange A) x) =
        ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R
              A))).obj M)).r1
            (e1 x)) ∧
      (∀ m : (𝒱.sectionsOf c M).M0, e0 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
              𝒱.U0).hom m) ∧
      (∀ m : (𝒱.sectionsOf c M).M1, e1 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
              𝒱.U1).hom m) ∧
      (∀ m : (𝒱.sectionsOf c M).M01, e01 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app (𝒱.U0
              ⊓ 𝒱.U1)).hom m) := by
  obtain ⟨e0, he0⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    c M htriv 𝒱.U0 𝒱.isAffineOpen_U0 A
  obtain ⟨e1, he1⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    c M htriv 𝒱.U1 𝒱.isAffineOpen_U1 A
  obtain ⟨e01, he01⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    c M htriv (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf A
  let S := 𝒱.sectionsOf c M
  let T := (𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A))
    ((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M)
  let E0 : A ⊗[R] S.M0 ≃ₗ[A] T.M0 := e0
  let E1 : A ⊗[R] S.M1 ≃ₗ[A] T.M1 := e1
  let E01 : A ⊗[R] S.M01 ≃ₗ[A] T.M01 := e01
  refine ⟨E0, E1, E01, ?_, ?_, he0, he1, he01⟩
  · intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul
          (R := R) A a m,
        map_smul, map_smul, map_smul]
      congr 1
      erw [he0, he01]
      exact unit_res c M A inf_le_left _ m
  · intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul
          (R := R) A a m,
        map_smul, map_smul, map_smul]
      congr 1
      erw [he1, he01]
      exact unit_res c M A inf_le_right _ m
end Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
