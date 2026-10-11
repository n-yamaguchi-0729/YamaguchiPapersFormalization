/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Mumford_bijective_cokerMapBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.MumfordTruncation
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
Bijectivity of cokernel base change in the finite-presentation construction for a Cech
differential.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_bijective_cokerMapBaseChange

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
open _root_.TwoChartCech
namespace Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech

variable {R : Type u} [CommRing R]
variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
variable (A : Type u) [CommRing A] [Algebra R A]

theorem mem_range_subtype_baseChange (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w = 0 ↔ ∃ z, ((K0 d).subtype.baseChange A) z = w := by
  have heqι : ⇑((K0 d).subtype.baseChange A) = ⇑((K0 d).subtype.lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  have heqc : ⇑((d.coprod (lift d)).baseChange A) = ⇑((d.coprod (lift d)).lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  rw [heqc]
  simp only [heqι]
  exact lTensor_exact A (LinearMap.exact_subtype_ker_map _) (surjective_coprod d) w

theorem prodRight_apply_eq_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (w : A ⊗[R] (M × N)) :
    (TensorProduct.prodRight R A A M N) w
      = (((LinearMap.fst R M N).baseChange A) w, ((LinearMap.snd R M N).baseChange A) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a x => simp [TensorProduct.prodRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

theorem prodRight_subtype_baseChange (z : A ⊗[R] K0 d) :
    (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) (((K0 d).subtype.baseChange A) z)
      = (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) := by
  rw [prodRight_apply_eq_baseChange]
  refine Prod.ext ?_ ?_
  · change ((LinearMap.fst R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A)
    z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
  · change ((LinearMap.snd R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A)
    z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl

theorem coprod_baseChange_apply (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w
      = (d.baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1
        + ((lift d).baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).2 := by
  induction w using TensorProduct.inductionOn with
  | tmul a x => simp [TensorProduct.prodRight_tmul, LinearMap.coprod_apply, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]; abel

theorem cokerMapBaseChange_surjective :
    Function.Surjective (cokerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    have hsurj : Function.Surjective ((d.coprod (lift d)).baseChange A) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective A (surjective_coprod d)
    obtain ⟨w, rfl⟩ := hsurj y
    refine ⟨Submodule.Quotient.mk (-((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).2),
      ?_⟩
    change Submodule.Quotient.mk (((ι1 d)).baseChange A _) = _
    rw [ι1_eq, LinearMap.baseChange_neg, LinearMap.neg_apply, map_neg, neg_neg,
      coprod_baseChange_apply,
      Submodule.Quotient.eq]
    refine ⟨-((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1, ?_⟩
    rw [map_neg]; abel

theorem cokerMapBaseChange_injective :
    Function.Injective (cokerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    have hq' : ((ι1 d).baseChange A) v ∈ LinearMap.range (d.baseChange A) := by
      rw [← Submodule.Quotient.mk_eq_zero]; exact hq
    obtain ⟨x, hx⟩ := hq'
    rw [ι1_eq, LinearMap.baseChange_neg, LinearMap.neg_apply] at hx
    set w := (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).symm (x, v) with hwdef
    have hw : ((d.coprod (lift d)).baseChange A) w = 0 := by
      rw [coprod_baseChange_apply, hwdef, LinearEquiv.apply_symm_apply, hx, neg_add_cancel]
    obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w).mp hw
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨z, ?_⟩
    change ((dK d).baseChange A) z = v
    have := congrArg Prod.snd (prodRight_subtype_baseChange d A z)
    rw [hz, hwdef, LinearEquiv.apply_symm_apply] at this
    exact this.symm

end TwoChartCech.Mumford

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.TwoChartCech.Mumford
  TwoChartCech_Mumford_bijective_cokerMapBaseChange.TwoChartCech.Mumford in
theorem _root_.TwoChartCech.Mumford.bijective_cokerMapBaseChange
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.cokerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) :=
  ⟨cokerMapBaseChange_injective d A, cokerMapBaseChange_surjective d A⟩

end
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_bijective_cokerMapBaseChange
end ProofImplementation
