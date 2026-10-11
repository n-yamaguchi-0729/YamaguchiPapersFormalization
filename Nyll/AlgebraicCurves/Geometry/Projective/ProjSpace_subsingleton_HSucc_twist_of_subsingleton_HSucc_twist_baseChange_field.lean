/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Cohomology.Sheaves.ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback

/-!
# Proj Space subsingleton HSucc twist of subsingleton HSucc twist base Change field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace RM6aSol

section LinAlg

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] {V : Type u} [AddCommGroup V]
  [Module k V]

theorem eq_zero_of_one_tmul_eq_zero (v : V) (h : (1 : K) ⊗ₜ[k] v = 0) : v = 0 := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap k K).injective)
  have h1 : TensorProduct.lid k V (TensorProduct.map ψ LinearMap.id ((1 : K) ⊗ₜ[k] v)) = v := by
    rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
    have : ψ 1 = 1 := by
      have := LinearMap.congr_fun hψ (1 : k)
      simpa using this
    rw [this, one_smul]
  rw [← h1, h, map_zero, map_zero]

theorem mem_of_one_tmul_mem_baseChange (W : Submodule k V) (v : V)
    (h : (1 : K) ⊗ₜ[k] v ∈ W.baseChange K) : v ∈ W := by
  refine (Submodule.Quotient.mk_eq_zero W).mp (eq_zero_of_one_tmul_eq_zero (k := k) K
    (Submodule.Quotient.mk v) ?_)
  have key : ∀ x ∈ W.baseChange K, (W.mkQ.baseChange K) x = 0 := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
        change (W.mkQ.baseChange K) ((1 : K) ⊗ₜ[k] w) = 0
        rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr
          hw, tmul_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have := key _ h
  rw [LinearMap.baseChange_tmul] at this
  exact this

end LinAlg

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem range_baseChange_le (f : M →ₗ[R] N) :
    LinearMap.range (f.baseChange A) ≤ (LinearMap.range f).baseChange A := by
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
      rw [LinearMap.baseChange_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem a (LinearMap.mem_range_self f m)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end RM6aSol

end ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
end AlgebraicCurves.Geometry.Projective.Proofs

namespace AlgebraicGeometry

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Projective.Proofs in
open ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field in
theorem ProjSpace.subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ι]
    (K : Type u) [Field K] [Algebra k K] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π K n) (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom
      (algebraMap k K))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map k K n) (d i : ℕ)
    (hK : Subsingleton ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).HSucc
      (ProjSpace.stdCoverPullback ι') i)) :
    Subsingleton ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).HSucc (ProjSpace.stdCoverPullback ι)
      i) := by
  classical
  obtain ⟨ε, hεd, -⟩ :=
    ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback ι K ι' e hpb hcomp d
  rw [Submodule.Quotient.subsingleton_iff] at hK ⊢
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  rw [LinearMap.mem_ker] at hz
  have hcomm : ∀ (j : ℕ) (t : K ⊗[k] (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).cochain
    (ProjSpace.stdCoverPullback ι) j),
      ε (j + 1) (((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).d (ProjSpace.stdCoverPullback ι)
        j).baseChange K t) = (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).d
        (ProjSpace.stdCoverPullback ι') j (ε j t) := by
    intro j t
    have := LinearMap.congr_fun (hεd j) t
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using this
  have hz' : (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).d (ProjSpace.stdCoverPullback ι') (i +
    1) (ε (i + 1) ((1 : K) ⊗ₜ[k] z)) = 0 := by
    rw [← hcomm, LinearMap.baseChange_tmul, hz, tmul_zero, map_zero]
  have hmem : (⟨ε (i + 1) ((1 : K) ⊗ₜ[k] z), LinearMap.mem_ker.mpr hz'⟩ : LinearMap.ker
    ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).d (ProjSpace.stdCoverPullback ι') (i + 1))) ∈
      (LinearMap.range ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).d (ProjSpace.stdCoverPullback
        ι') i)).comap (LinearMap.ker ((ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).d
        (ProjSpace.stdCoverPullback ι') (i + 1))).subtype := by
    rw [hK]; exact Submodule.mem_top
  rw [Submodule.mem_comap, LinearMap.mem_range] at hmem
  obtain ⟨w', hw'⟩ := hmem
  change (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).d (ProjSpace.stdCoverPullback ι') i w' = ε
    (i + 1) ((1 : K) ⊗ₜ[k] z) at hw'
  obtain ⟨t, rfl⟩ := (ε i).surjective w'
  rw [← hcomm] at hw'
  have h1z : (1 : K) ⊗ₜ[k] z ∈ (LinearMap.range ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).d
    (ProjSpace.stdCoverPullback ι) i)).baseChange K := by
    rw [← (ε (i + 1)).injective hw']
    exact RM6aSol.range_baseChange_le K ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).d
      (ProjSpace.stdCoverPullback ι) i) (LinearMap.mem_range_self _ t)
  have hzr : z ∈ LinearMap.range ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).d
    (ProjSpace.stdCoverPullback ι) i) := RM6aSol.mem_of_one_tmul_mem_baseChange K _ z h1z
  exact Submodule.mem_comap.mpr hzr
end AlgebraicGeometry
end ProofImplementation
