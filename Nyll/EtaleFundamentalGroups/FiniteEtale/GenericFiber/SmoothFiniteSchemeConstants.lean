/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.SmoothFiniteCoverConstants
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.ArithmeticFunctionField
import Nyll.SchemeTheory.FunctionFields.Functoriality
import Nyll.SchemeTheory.Normalization.Normal
import Nyll.SchemeTheory.RingTheory.SeparableConstantsTensor
import Mathlib.Algebra.CharZero.AddMonoidHom
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Constant fields of smooth finite arithmetic schemes

A finite affine cover and its inverse image supply the rings and maps in the
arithmetic constants theorem. Normality extends integral constants on every
chart, and the actual covering of `Spec ℤ` supplies faithful flatness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct NumberField

namespace EtaleFundamentalGroups

/-- A dominant arithmetic integral scheme has characteristic-zero function
field, via the actual map from the fraction field of the integers. -/
theorem charZero_functionField_of_dominant_integers
    {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℤ)) [IsDominant p] :
    CharZero X.functionField := by
  have : IsFractionRing ℤ (Spec (CommRingCat.of ℤ)).functionField := by
    convert! functionField_isFractionRing_of_affine (CommRingCat.of ℤ) using 1
    exact Subsingleton.elim _ _
  let z : ℤ →+* X.functionField := (p.functionFieldMap p.denseRange).comp
    (algebraMap ℤ (Spec (CommRingCat.of ℤ)).functionField)
  exact CharZero.of_addMonoidHom z.toAddMonoidHom z.map_one
    ((p.functionFieldMap_injective p.denseRange).comp
      (IsFractionRing.injective ℤ (Spec (CommRingCat.of ℤ)).functionField))

private theorem smooth_int_sections
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℤ)) [Smooth p]
    (U : X.Opens) (hU : IsAffineOpen U) : Algebra.Smooth ℤ Γ(X, U) := by
  have heq : Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(X, U))) =
      hU.fromSpec ≫ p := specZIsTerminal.hom_ext _ _
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(X, U)))) := by
    rw [heq]
    infer_instance
  exact RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)

/-- A finite surjective arithmetic cover that is smooth and normal admits no
nontrivial constant number field disjoint from the base function field. -/
theorem numberField_finrank_eq_one_of_smooth_finite_scheme_cover
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsNormalIntegral X]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (p : Y ⟶ Spec (CommRingCat.of ℤ)) [QuasiCompact p] [Surjective p]
    [Smooth (f ≫ p)] [CharZero Y.functionField] [CharZero X.functionField]
    (K : Type) [Field K] [NumberField K]
    [IsDomain (Y.functionField ⊗[ℚ] K)] (g : K →ₐ[ℚ] X.functionField) :
    Module.finrank ℚ K = 1 := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  choose U hU hxU htop using fun y : Y ↦
    exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) trivial
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : Y ↦ (U y : Set Y)) (fun y ↦ (U y).isOpen)
    (fun y _ ↦ Set.mem_iUnion.mpr ⟨y, hxU y⟩)
  let B (i : s) : Type := Γ(Y, U i.1)
  let A (i : s) : Type := Γ(X, f ⁻¹ᵁ U i.1)
  have (i : s) : Nonempty (U i.1) := ⟨i.1, hxU i.1⟩
  have (i : s) : Nonempty (f ⁻¹ᵁ U i.1) := by
    obtain ⟨x, hx⟩ := f.surjective i.1
    exact ⟨x, show f x ∈ U i.1 by rw [hx]; exact hxU i.1⟩
  have (i : s) : IsDomain (B i) := inferInstance
  have (i : s) : IsDomain (A i) := inferInstance
  have (i : s) : IsIntegrallyClosed (A i) :=
    IsNormalIntegral.affine_isIntegrallyClosed (f ⁻¹ᵁ U i.1) ((hU i.1).preimage f)
  let (i : s) : Algebra (B i) (A i) := (f.app (U i.1)).hom.toAlgebra
  have (i : s) : Module.Finite (B i) (A i) := f.finite_app (U i.1) (hU i.1)
  have (i : s) : Module.Flat (B i) (A i) := by
    have hf := f.flat_appLE (hU i.1) ((hU i.1).preimage f) le_rfl
    rw [Scheme.Hom.appLE_eq_app] at hf
    exact hf
  have (i : s) : FaithfulSMul (B i) (A i) := inferInstance
  have (i : s) : Algebra.Smooth ℤ (A i) :=
    smooth_int_sections (f ≫ p) _ ((hU i.1).preimage f)
  have (i : s) : IsFractionRing (B i) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (U i.1) (hU i.1)
  have (i : s) : IsFractionRing (A i) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U i.1)
      ((hU i.1).preimage f)
  apply numberField_finrank_eq_one_of_smooth_finite_arithmetic_cover
    B A Y.functionField K X.functionField g
  intro q
  obtain ⟨y, hy⟩ := p.surjective q
  obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  let j : s := ⟨i, hi⟩
  let r : PrimeSpectrum (B j) := (hU i).primeIdealOf ⟨y, hiy⟩
  refine ⟨j, r, ?_⟩
  have heq : Spec.map (CommRingCat.ofHom (algebraMap ℤ (B j))) =
      (hU i).fromSpec ≫ p := specZIsTerminal.hom_ext _ _
  change (Spec.map (CommRingCat.ofHom (algebraMap ℤ (B j)))) r = q
  rw [heq]
  change p ((hU i).fromSpec ((hU i).primeIdealOf ⟨y, hiy⟩)) = q
  rw [(hU i).fromSpec_primeIdealOf]
  exact hy

/-- After extension to the algebraic closure of the rational constants, the
function field of the smooth finite arithmetic cover is still a field. -/
theorem isField_tensor_algebraicClosure_of_smooth_finite_scheme_cover
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsNormalIntegral X]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (p : Y ⟶ Spec (CommRingCat.of ℤ)) [QuasiCompact p] [Surjective p]
    [Smooth (f ≫ p)] [CharZero Y.functionField] [CharZero X.functionField]
    [GeometricallyIntegral
      (p.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ))))] :
    IsField (X.functionField ⊗[ℚ] AlgebraicClosure ℚ) := by
  apply Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
    ℚ X.functionField (AlgebraicClosure ℚ)
  intro y hy
  let K : IntermediateField ℚ X.functionField := IntermediateField.adjoin ℚ {y}
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hy.isIntegral
  have : NumberField K := {}
  have : IsDomain (Y.functionField ⊗[ℚ] K) :=
    isDomain_functionField_ratTensor_of_arithmetic_genericFiber p K
  have hdim : Module.finrank ℚ K = 1 :=
    numberField_finrank_eq_one_of_smooth_finite_scheme_cover f p K K.val
  exact IntermediateField.mem_bot.mp
    (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hdim)

end EtaleFundamentalGroups
