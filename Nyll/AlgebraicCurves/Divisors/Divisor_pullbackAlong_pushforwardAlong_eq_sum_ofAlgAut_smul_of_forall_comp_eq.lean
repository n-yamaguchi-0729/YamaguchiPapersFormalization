/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Divisors.Divisor_pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
import Nyll.AlgebraicCurves.Divisors.Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
import Nyll.AlgebraicCurves.FunctionFields.FinrankAlong_id
import Nyll.AlgebraicCurves.FunctionFields.FinrankAlong_comp

/-!
# Divisor pullback Along pushforward Along eq sum of Alg Aut smul of forall comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq

open AlgebraicCurve
open scoped TensorProduct

namespace Ws45
namespace PullPushGal

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem isIntegral_id : (AlgHom.id K F').toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ Function.surjective_id

theorem isIntegral_algEquiv (σ : F' ≃ₐ[K] F') : ((σ : F' →ₐ[K] F') : F' →ₐ[K]
  F').toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ σ.surjective

theorem finiteAlong_algEquiv (σ : F' ≃ₐ[K] F') : FiniteAlong K (σ : F' →ₐ[K] F') :=
  RingHom.Finite.of_surjective ((σ : F' →ₐ[K] F') : F' →ₐ[K] F').toRingHom σ.surjective

theorem finiteAlong_id : FiniteAlong K (AlgHom.id K F') :=
  RingHom.Finite.of_surjective (AlgHom.id K F').toRingHom Function.surjective_id

theorem finrankAlong_algEquiv (σ : F' ≃ₐ[K] F') : finrankAlong K (σ : F' →ₐ[K] F') = 1 := by
  have h := AlgebraicCurve.finrankAlong_comp (σ : F' →ₐ[K] F') (σ.symm : F' →ₐ[K] F')
  rw [show ((σ.symm : F' →ₐ[K] F')).comp (σ : F' →ₐ[K] F') = AlgHom.id K F' from AlgEquiv.symm_comp
    σ,
    AlgebraicCurve.finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

theorem restrictAlong_id (h : (AlgHom.id K F').toRingHom.IsIntegral) (w : Place K F') :
    w.restrictAlong (AlgHom.id K F') h = w := by
  apply Place.ext
  ext x
  exact Iff.rfl

theorem inertiaDegAlong_id (h : (AlgHom.id K F').toRingHom.IsIntegral) (w : Place K F') :
    Place.inertiaDegAlong (AlgHom.id K F') h w = 1 := by
  let := AlgebraicCurve.algebraAlong (AlgHom.id K F')
  have := AlgebraicCurve.isScalarTower_along (AlgHom.id K F')
  have : Algebra.IsIntegral F' F' := AlgebraicCurve.isIntegral_along _ h
  change Module.finrank (w.restrict F').ResidueField w.ResidueField = 1
  have hsurj : Function.Surjective (algebraMap (w.restrict F').ResidueField w.ResidueField) := by
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    refine ⟨IsLocalRing.residue _ ⟨(a : F'), a.2⟩, ?_⟩
    rw [Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue]
    rfl
  have e := LinearEquiv.ofBijective (Algebra.linearMap (w.restrict F').ResidueField w.ResidueField)
    ⟨(algebraMap (w.restrict F').ResidueField w.ResidueField).injective, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_self]

theorem pushforwardAlong_id [HasPrincipalDivisors K F'] (h : (AlgHom.id K F').toRingHom.IsIntegral)
    (D : Divisor K F') :
    Divisor.pushforwardAlong (AlgHom.id K F') h D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
    rw [map_add, ih, Divisor.pushforwardAlong_single, restrictAlong_id, inertiaDegAlong_id,
      Nat.cast_one, mul_one]

end Ws45.PullPushGal

end Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
end AlgebraicCurves.Divisors.Proofs

namespace AlgebraicCurve.Divisor

open scoped TensorProduct in
open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq in
open Ws45.PullPushGal in
theorem pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
    {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero K]
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K φ)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n)
    (σ : Fin n → (F' ≃ₐ[K] F')) (hσ : ∀ i, ((σ i : F' ≃ₐ[K] F') : F' →ₐ[K] F').comp φ = φ)
    (hinj : Function.Injective σ)
    (D : AlgebraicCurve.Divisor K F') :
    AlgebraicCurve.Divisor.pullbackAlong φ hφ (AlgebraicCurve.Divisor.pushforwardAlong φ hφ D) =
      ∑ i, AlgebraicCurve.SemilinearAut.ofAlgAut (σ i) • D := by
  classical
  have hσφ : ∀ (i : Fin n) (x : F), σ i (φ x) = φ x := fun i x => by
    have := congrArg (fun f : F →ₐ[K] F' => f x) (hσ i); simpa using this
  have key := AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_sum_of_decomposition
    (K := K) (F := F) (F₁ := F') (F₂ := F') φ φ hφ hφ hfin hfin n (fun _ => F')
    (fun _ => AlgHom.id K F') (fun i => (σ i : F' →ₐ[K] F'))
    (fun i => by rw [AlgHom.id_comp, hσ i])
    (fun _ => isIntegral_id) (fun i => isIntegral_algEquiv (σ i))
    (fun _ => finiteAlong_id) (fun i => finiteAlong_algEquiv (σ i))
    (fun i => eq_top_iff.2 fun x _ => IntermediateField.subset_adjoin _ _ (Or.inl ⟨x, rfl⟩))
    (by rw [hn, Finset.sum_congr rfl fun i _ => finrankAlong_algEquiv (σ i)]; simp)
    (by
      intro i j hij
      have hne : σ i ≠ σ j := fun h => hij (hinj h)
      obtain ⟨b, hb⟩ : ∃ b : F', σ i b ≠ σ j b := by
        by_contra h
        push Not at h
        exact hne (AlgEquiv.ext h)
      refine ⟨σ i b ⊗ₜ[K] 1 - 1 ⊗ₜ[K] b, ?_, ?_⟩
      · simp [Algebra.TensorProduct.productMap_apply_tmul]
      · simp [Algebra.TensorProduct.productMap_apply_tmul, sub_eq_zero, hb])
    D
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pushforwardAlong_id, AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul]
end AlgebraicCurve.Divisor
end ProofImplementation
