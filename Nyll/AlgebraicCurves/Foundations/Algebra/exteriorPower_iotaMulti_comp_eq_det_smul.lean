/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_exteriorPower_iotaMulti_comp_eq_det_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# exterior Power iota Multi comp eq det smul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.exteriorPower_iotaMulti_comp_eq_det_smul

namespace ExteriorPowerDet

lemma alternatingMap_apply_matrix_smul {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] {n : ℕ} (g : M [⋀^Fin n]→ₗ[A] N) (f : Fin n → M)
    (a : Matrix (Fin n) (Fin n) A) :
    g (fun j => ∑ i, a i j • f i) = a.det • g f := by
  classical
  let L : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A f
  let b : Module.Basis (Fin n) A (Fin n → A) := Pi.basisFun A (Fin n)
  have hL : ∀ i, L (b i) = f i := fun i => by
    simp [L, b, Fintype.linearCombination_apply_single]
  have key : g.compLinearMap L = b.det.smulRight (g f) := by
    refine Module.Basis.ext_alternating b fun v hv => ?_
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have h1 : (fun i => L (b (v i))) = f ∘ σ := funext fun i => hL (v i)
    have h2 : (fun i => b (v i)) = b ∘ σ := rfl
    rw [AlternatingMap.compLinearMap_apply, h1, AlternatingMap.map_perm,
      AlternatingMap.smulRight_apply,
      h2, AlternatingMap.map_perm, Module.Basis.det_self]
    simp [Units.smul_def, Int.cast_smul_eq_zsmul]
  have h3 : (fun j => ∑ i, a i j • f i) = fun j => L (a.transpose j) := by
    funext j
    simp [L, Fintype.linearCombination_apply, Matrix.transpose_apply]
  have h4 := congrArg (fun G : (Fin n → A) [⋀^Fin n]→ₗ[A] N => G (fun j => a.transpose j)) key
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smulRight_apply] at h4
  calc
    g (fun j => ∑ i, a i j • f i) = (b.det (fun j => a.transpose j)) • g f :=
      (congrArg g h3).trans h4
    _ = a.transpose.det • g f :=
      congrArg (fun r : A => r • g f) (Pi.basisFun_det_apply (fun j k => a k j))
    _ = a.det • g f := congrArg (fun r : A => r • g f) (Matrix.det_transpose a)

lemma ιMulti_matrix_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    {n : ℕ} (f : Fin n → M) (a : Matrix (Fin n) (Fin n) A) :
    exteriorPower.ιMulti A n (fun j => ∑ i, a i j • f i) = a.det • exteriorPower.ιMulti A n f :=
  alternatingMap_apply_matrix_smul (exteriorPower.ιMulti A n) f a

end ExteriorPowerDet

open ExteriorPowerDet in
theorem _root_.exteriorPower.iotaMulti_comp_eq_det_smul {A : Type*} [CommRing A] {M : Type*}
  [AddCommGroup M]
    [Module A M] {n : ℕ} (b : Module.Basis (Fin n) A M) (f : M →ₗ[A] M) (m : Fin n → M) :
    exteriorPower.ιMulti A n (f ∘ m) = LinearMap.det f • exteriorPower.ιMulti A n m := by
  classical
  let c : Matrix (Fin n) (Fin n) A := fun i j => b.repr (m j) i
  let T : Matrix (Fin n) (Fin n) A := LinearMap.toMatrix b b f
  have hm : (fun j => ∑ i, c i j • b i) = m := by
    funext j
    exact b.sum_repr (m j)
  have hfb : ∀ i, f (b i) = ∑ k, T k i • b k := by
    intro i
    have h := b.sum_repr (f (b i))
    simp only [T, LinearMap.toMatrix_apply]
    exact h.symm
  have hfm : (fun j => ∑ k, (T * c) k j • b k) = f ∘ m := by
    funext j
    have h1 : f (m j) = ∑ i, c i j • f (b i) := by
      have := congrArg f (congrFun hm j)
      rw [map_sum] at this
      simpa only [map_smul] using this.symm
    rw [Function.comp_apply, h1]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfb i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm]
  rw [← hfm, ιMulti_matrix_smul, Matrix.det_mul, ← hm, ιMulti_matrix_smul, smul_smul]
  simp only [T, LinearMap.det_toMatrix]
end AlgebraicCurves.Foundations.Algebra.Proofs.exteriorPower_iotaMulti_comp_eq_det_smul
end ProofImplementation
