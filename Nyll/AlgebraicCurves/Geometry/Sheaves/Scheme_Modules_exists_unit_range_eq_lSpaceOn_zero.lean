/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Models.Range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Function-field sections of the unit module

The unit module embeds in the function field of a smooth integral curve. On each
affine open, its image is the Riemann-Roch space for the zero divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace UnitFF
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry
open AlgebraicCurve TopologicalSpace Opposite

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

/-- The structure sheaf viewed as the tensor unit of sheaves of modules on `X`. -/
noncomputable abbrev OU (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
omit [IsIntegral X] in
theorem smul_eq (U : X.Opens) (a : Γ(X, U)) (m : Γ(OU X, U)) :
    (show Γ(X, U) from a • m) = a * (show Γ(X, U) from m) := rfl
omit [IsIntegral X] in
theorem map_eq {U V : X.Opens} (h : V ≤ U) (m : Γ(OU X, U)) :
    (show Γ(X, V) from (OU X).presheaf.map (homOfLE h).op m) = X.presheaf.map (homOfLE h).op
        (show Γ(X, U) from m) :=
  rfl

/-- The germ of a unit section in the function field, extended by zero on the empty open. -/
noncomputable def φ (U : X.Opens) : Γ(OU X, U) →+ (X.functionField : Type u) :=
  open Classical in
  if _h : Nonempty U then
    { toFun := fun m => (X.germToFunctionField U).hom (show Γ(X, U) from m)
      map_zero' := map_zero (X.germToFunctionField U).hom
      map_add' := fun m m' => map_add (X.germToFunctionField U).hom (show Γ(X, U) from m) (show
          Γ(X, U) from m') }
  else 0

theorem φ_apply (U : X.Opens) [h : Nonempty U] (m : Γ(OU X, U)) :
    φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m) := by
  simp only [φ, dite_eq_left h]
  rfl

theorem φ_nat {U V : X.Opens} (h : V ≤ U) [Nonempty U] [Nonempty V] (m : Γ(OU X, U)) :
    φ V ((OU X).presheaf.map (homOfLE h).op m) = φ U m := by
  rw [φ_apply, φ_apply, map_eq]
  change (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField V).hom _ = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

theorem φ_smul (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(OU X, U)) :
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m := by
  rw [φ_apply, φ_apply, smul_eq, map_mul]
  rfl

theorem φ_injective (U : X.Opens) [Nonempty U] : Function.Injective (φ (X := X) U) := by
  intro m m' h
  rw [φ_apply, φ_apply] at h
  exact Scheme.germToFunctionField_injective X U h

theorem range_φ [SmoothOfRelativeDimension 1 x] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    Set.range (φ (X := X) U) = (lSpaceOn (placesOf x U) (0 : Divisor K X.functionField) : Set
        X.functionField) := by
  let := (baseToFunctionField x).toAlgebra
  have hsec := range_algebraMap_functionField_eq_iInf_of_isAffineOpen x U hU
  ext f
  have h1 : f ∈ Set.range (φ (X := X) U) ↔ f ∈ (algebraMap Γ(X, U) X.functionField).range := by
    simp only [Set.mem_range, RingHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨show Γ(X, U) from m, by rw [φ_apply]; rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨show Γ(OU X, U) from a, by rw [φ_apply]; rfl⟩
  rw [h1, hsec, SetLike.mem_coe, mem_lSpaceOn_iff]
  simp only [Subring.mem_iInf, Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  constructor
  · intro hf v hv
    exact (Place.mem_iff_adicValuation_le_one v).mp (hf v hv)
  · intro hf v hv
    exact (Place.mem_iff_adicValuation_le_one v).mpr (hf v hv)

end AlgebraicGeometry.Scheme.Modules.UnitFF

noncomputable local instance nativeUnitSectionsModule (X : Scheme.{u}) (U : X.Opens) :
    Module Γ(X, U) Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) :=
  ((SheafOfModules.unit X.ringCatSheaf : X.Modules).val.obj (Opposite.op U)).isModule

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
open scoped AlgebraicGeometry in
with_weak_namespace AlgebraicGeometry
open scoped Scheme in
with_weak_namespace Scheme
open scoped Modules in
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
open AlgebraicGeometry.Scheme.Modules.UnitFF in
theorem AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+
        (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map
                (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf :
          X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) := by
  let := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  refine ⟨fun U => φ U, fun U _ m => φ_apply U m, ?_, fun U _ a m => φ_smul U a m,
    fun U hU => by
      have := hU
      exact φ_injective U, fun U hU hne => by
      have := hne
      exact range_φ x U hU⟩
  intro U V h hV m
  have := hV
  have : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
  exact φ_nat h m

open AlgebraicGeometry.Scheme.Modules.UnitFF in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+
        (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map
                (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf :
          X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) :=
  AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero' x
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
end ProofImplementation
