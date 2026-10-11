/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Semilinear
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension

/-!
# Semilinear Aut exists Unique monoid Hom base Aut eq smul algebra Map eq of constant Field
Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearConstantExtension

open AlgebraicCurve

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (S : Type*) [Group S] (galF : S →* SemilinearAut K F) (τ : S →* (K' ≃+* K'))
    (hτ : ∀ (σ : S) (a : K), τ σ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut (galF
      σ) a)) :
    ∃! galF' : S →* SemilinearAut K' F',
      (∀ (σ : S) (c : K'), SemilinearAut.baseAut (galF' σ) c = τ σ c) ∧
      ∀ (σ : S) (y : F), galF' σ • algebraMap F F' y = algebraMap F F' (galF σ • y) := by
  classical
  have H : ∀ σ : S, ∃! g' : SemilinearAut K' F',
      (∀ c : K', SemilinearAut.baseAut g' c = τ σ c) ∧
      ∀ y : F, g' • algebraMap F F' y = algebraMap F F' (galF σ • y) := fun σ =>
    SemilinearAut.existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen (galF σ) (τ σ) (hτ σ)
  let f : S → SemilinearAut K' F' := fun σ => (H σ).exists.choose
  have hf : ∀ σ, (∀ c : K', SemilinearAut.baseAut (f σ) c = τ σ c) ∧
      ∀ y : F, f σ • algebraMap F F' y = algebraMap F F' (galF σ • y) := fun σ => (H
        σ).exists.choose_spec
  have h1 : f 1 = 1 := (H 1).unique (hf 1) ⟨fun c => by simp, fun y => by simp⟩
  have hmul : ∀ σ σ' : S, f (σ * σ') = f σ * f σ' := fun σ σ' =>
    (H (σ * σ')).unique (hf (σ * σ'))
      ⟨fun c => by
        rw [SemilinearAut.baseAut_mul, map_mul, RingAut.mul_apply, RingAut.mul_apply, (hf σ').1,
          (hf σ).1],
       fun y => by
        rw [mul_smul, (hf σ').2, (hf σ).2, map_mul, mul_smul]⟩
  let galF' : S →* SemilinearAut K' F' := { toFun := f, map_one' := h1, map_mul' := hmul }
  refine ⟨galF', ⟨fun σ c => (hf σ).1 c, fun σ y => (hf σ).2 y⟩, ?_⟩
  rintro G ⟨hGb, hGF⟩
  ext σ : 1
  exact (H σ).unique ⟨hGb σ, hGF σ⟩ (hf σ)

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearConstantExtension
end ProofImplementation


open AlgebraicCurve

namespace AlgebraicCurve.SemilinearAut

theorem existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (S : Type*) [Group S] (galF : S →* SemilinearAut K F) (τ : S →* (K' ≃+* K'))
    (hτ : ∀ (σ : S) (a : K), τ σ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut (galF
      σ) a)) :
    ∃! galF' : S →* SemilinearAut K' F',
      (∀ (σ : S) (c : K'), SemilinearAut.baseAut (galF' σ) c = τ σ c) ∧
      ∀ (σ : S) (y : F), galF' σ • algebraMap F F' y = algebraMap F F' (galF σ • y) := by
  exact _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearConstantExtension.solution (K
    := K) (F := F) (K' := K') (F' := F') (hfg := hfg) (hfg' := hfg') (hgen := hgen) (S := S) (galF
    := galF) (τ := τ) (hτ := hτ)

end AlgebraicCurve.SemilinearAut
