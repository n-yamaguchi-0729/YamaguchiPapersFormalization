/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.TwoChartCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
The dimension of a Cech kernel after base change is unchanged by a field extension.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace TwoChartCech_finrank_ker_baseChange_eq_of_field_extension

noncomputable section

universe u

open scoped TensorProduct

namespace TwoChartCech
open _root_.TwoChartCech
open _root_.TwoChartCech

theorem kerBaseChangeHom_bijective_of_flat {R : Type u} [CommRing R] {C0 C1 : Type u}
    [AddCommGroup C0]
    [Module R C0] [AddCommGroup C1] [Module R C1] (d : C0 →ₗ[R] C1) (A : Type u) [CommRing A]
      [Algebra R A]
    [Module.Flat R A] : Function.Bijective (kerBaseChangeHom d A) := by
  constructor
  · intro x y h
    have h' := congrArg Subtype.val h
    rw [kerBaseChangeHom_apply_coe, kerBaseChangeHom_apply_coe] at h'
    have hinj : Function.Injective ((LinearMap.ker d).subtype.baseChange A) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker d).subtype_injective
    exact hinj h'
  · rintro ⟨y, hy⟩
    have hex := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map d)
    have hy' : (d.lTensor A) y = 0 := by rw [← LinearMap.baseChange_eq_ltensor]; exact hy
    obtain ⟨x, hx⟩ := (hex y).mp hy'
    refine ⟨x, Subtype.ext ?_⟩
    rw [kerBaseChangeHom_apply_coe, LinearMap.baseChange_eq_ltensor]
    exact hx

section ChangeField

variable {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup
  C1]
  [Module R C1] (d : C0 →ₗ[R] C1)
variable (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]

theorem cancelBaseChange_tmul_baseChange (l : L) (x : K ⊗[R] C0) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C1 (l ⊗ₜ[K] (d.baseChange K x))
      = (d.baseChange L) (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0 (l ⊗ₜ[K]
        x)) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, hx, hy, TensorProduct.tmul_add,
    map_add, map_add]
  | tmul k m => simp [LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

theorem cancelBaseChange_baseChange (z : L ⊗[K] (K ⊗[R] C0)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C1 (((d.baseChange K).baseChange L)
      z)
      = (d.baseChange L) (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0 z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul l x => rw [LinearMap.baseChange_tmul]; exact cancelBaseChange_tmul_baseChange d K L l x

theorem map_cancelBaseChange_ker :
    Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).toLinearMap
        (LinearMap.ker ((d.baseChange K).baseChange L))
      = LinearMap.ker (d.baseChange L) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  have hw : w = TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).symm w) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).apply_symm_apply w).symm
  constructor
  · intro h
    rw [hw, ← cancelBaseChange_baseChange, h, map_zero]
  · intro h
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C1).injective
    rw [cancelBaseChange_baseChange, ← hw, h, map_zero]

/--
Identify the kernel after successive field base changes with the kernel after direct base change.
-/
def kerCancelEquiv : LinearMap.ker ((d.baseChange K).baseChange L) ≃ₗ[L] LinearMap.ker
    (d.baseChange L) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R K L L C0).ofSubmodules _ _
    (map_cancelBaseChange_ker d K L)

theorem finrank_ker_baseChange_eq' :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker
      (d.baseChange L)) := by
  have e1 : (L ⊗[K] LinearMap.ker (d.baseChange K)) ≃ₗ[L] LinearMap.ker ((d.baseChange
    K).baseChange L) :=
    LinearEquiv.ofBijective _ (kerBaseChangeHom_bijective_of_flat (d.baseChange K) L)
  let b := Module.Basis.ofVectorSpace K (LinearMap.ker (d.baseChange K))
  have h1 : Module.finrank K (LinearMap.ker (d.baseChange K))
      = Nat.card (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker (d.baseChange K))) :=
    Module.finrank_eq_nat_card_basis b
  have h2 : Module.finrank L (L ⊗[K] LinearMap.ker (d.baseChange K))
      = Nat.card (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker (d.baseChange K))) :=
    Module.finrank_eq_nat_card_basis (Algebra.TensorProduct.basis L b)
  rw [h1, ← h2, e1.finrank_eq, (kerCancelEquiv d K L).finrank_eq]

end ChangeField

end TwoChartCech

theorem _root_.TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1]
      [Module R C1]
    (d : C0 →ₗ[R] C1) (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker
      (d.baseChange L)) :=
  TwoChartCech.finrank_ker_baseChange_eq' d K L

end
end TwoChartCech_finrank_ker_baseChange_eq_of_field_extension
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
