/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.LaurentBaseChange
import Mathlib.RingTheory.LinearDisjoint

/-!
# Intermediate Field is Domain tensor Product of le laurent Series
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IntermediateField_isDomain_tensorProduct_of_le_laurentSeries

open scoped TensorProduct

namespace RegExt

variable (κ k : Type*) [Field κ] [Field k] [Algebra κ k]

theorem algebraMap_laurent (c : κ) :
    algebraMap κ (LaurentSeries k) c = HahnSeries.C (algebraMap κ k c) := by
  have h1 : algebraMap κ (PowerSeries k) c = PowerSeries.C (algebraMap κ k c) :=
    PowerSeries.algebraMap_apply
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

/-- The algebra map on Laurent series induced by extension of the coefficient field. -/
noncomputable def coeffAlgHom : LaurentSeries κ →ₐ[κ] LaurentSeries k :=
  { ModularCurve.coeffMap (algebraMap κ k) with
    commutes' := fun c => by
      change ModularCurve.coeffMap (algebraMap κ k) (algebraMap κ (LaurentSeries κ) c) = algebraMap
        κ (LaurentSeries k) c
      rw [algebraMap_laurent κ κ c, algebraMap_laurent κ k c, Algebra.algebraMap_self,
        RingHom.id_apply,
        HahnSeries.C_apply, HahnSeries.C_apply, ModularCurve.coeffMap_single] }

theorem coeffAlgHom_coeff (x : LaurentSeries κ) (n : ℤ) :
    (coeffAlgHom κ k x).coeff n = algebraMap κ k (x.coeff n) := rfl

/-- The algebra map sending a field element to its constant Laurent series. -/
noncomputable def constAlgHom : k →ₐ[κ] LaurentSeries k :=
  { (HahnSeries.C : k →+* LaurentSeries k) with
    commutes' := fun c => by
      change HahnSeries.C (algebraMap κ k c) = algebraMap κ (LaurentSeries k) c
      rw [algebraMap_laurent] }

theorem constAlgHom_apply (b : k) : constAlgHom κ k b = HahnSeries.C b := rfl

theorem linearDisjoint_range :
    (coeffAlgHom κ k).range.LinearDisjoint (constAlgHom κ k).range := by
  classical
  let b := Module.Basis.ofVectorSpace κ k
  let e : k ≃ₐ[κ] (constAlgHom κ k).range := AlgEquiv.ofInjective (constAlgHom κ k)
    (RingHom.injective _)
  let b' : Module.Basis _ κ (constAlgHom κ k).range := b.map e.toLinearEquiv
  refine Subalgebra.LinearDisjoint.of_basis_right _ _ b' ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hx : ∀ j, ∃ x : LaurentSeries κ, coeffAlgHom κ k x = ((g j : (coeffAlgHom κ k).range) :
    LaurentSeries k) :=
    fun j => (AlgHom.mem_range _).mp (g j).2
  choose x hxg using hx
  have hval : ∀ j, ((constAlgHom κ k).range.val (b' j) : LaurentSeries k) = HahnSeries.C (b j) := by
    intro j
    change (((b.map e.toLinearEquiv) j : (constAlgHom κ k).range) : LaurentSeries k) = HahnSeries.C
      (b j)
    rw [Module.Basis.map_apply]
    change ((e (b j) : (constAlgHom κ k).range) : LaurentSeries k) = _
    rw [AlgEquiv.ofInjective_apply]
    rfl
  have hcoef : ∀ n : ℤ, ∑ j ∈ s, (x j).coeff n • b j = 0 := by
    intro n
    have h := congrArg (fun z : LaurentSeries k => z.coeff n) hsum
    simp only [Function.comp_apply, HahnSeries.coeff_zero] at h
    rw [HahnSeries.coeff_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, hval j, smul_eq_mul, mul_comm, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul,
      ← hxg j, coeffAlgHom_coeff, smul_eq_mul, Algebra.smul_def, mul_comm]
  have hzero : ∀ n : ℤ, (x i).coeff n = 0 := fun n =>
    linearIndependent_iff'.mp b.linearIndependent s (fun j => (x j).coeff n) (hcoef n) i hi
  have hxi : x i = 0 := HahnSeries.ext (funext hzero)
  apply Subtype.ext
  change ((g i : (coeffAlgHom κ k).range) : LaurentSeries k) = 0
  rw [← hxg i, hxi, map_zero]

end RegExt

namespace RegExt

theorem isDomain (κ k : Type*) [Field κ] [Field k] [Algebra κ k] (R : IntermediateField κ
  (LaurentSeries κ)) :
    IsDomain (↥R ⊗[κ] k) := by
  let fa : ↥R →ₐ[κ] LaurentSeries k := (coeffAlgHom κ k).comp R.val
  let fb : k →ₐ[κ] LaurentSeries k := constAlgHom κ k
  have hle : fa.range ≤ (coeffAlgHom κ k).range := by
    rintro _ ⟨r, rfl⟩
    exact ⟨(r : LaurentSeries κ), rfl⟩
  let e : k ≃ₗ[κ] (constAlgHom κ k).range :=
    (AlgEquiv.ofInjective (constAlgHom κ k) (RingHom.injective _)).toLinearEquiv
  let _ : Module.Flat κ (constAlgHom κ k).range := Module.Flat.of_linearEquiv e.symm
  have H : fa.range.LinearDisjoint fb.range := (linearDisjoint_range κ k).of_le_left_of_flat hle
  exact H.isDomain_of_injective fa.injective fb.injective

end RegExt

theorem _root_.IntermediateField.isDomain_tensorProduct_of_le_laurentSeries
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ)) :
    IsDomain (↥R ⊗[κ] k) :=
  RegExt.isDomain κ k R
end IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id
  ModularCurve.coeffMap_single
