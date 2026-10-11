/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsAdicComplete_of_module_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Is Adic Complete of module finite
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.IsAdicComplete_of_module_finite

universe u v w

namespace M4cP1X1

open IsLocalRing

section Compare

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I J : Ideal R}

theorem smul_top_pow_le_of_le (hIJ : I ≤ J) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

theorem smul_top_pow_mul_le_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) (n : ℕ) :
    (J ^ (N * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
  rw [pow_mul]
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)

theorem isHausdorff_of_le (hIJ : I ≤ J) [h : IsHausdorff J M] : IsHausdorff I M :=
  ⟨fun x hx => h.haus x fun n => (hx n).mono (smul_top_pow_le_of_le hIJ n)⟩

theorem isHausdorff_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) [h : IsHausdorff I M] :
    IsHausdorff J M :=
  ⟨fun x hx => h.haus x fun n => (hx (N * n)).mono (smul_top_pow_mul_le_of_pow_le hJI n)⟩

theorem isPrecomplete_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete I M] : IsPrecomplete J M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := fun n => f (N' * n)) fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left N' hmn)).mono (smul_top_pow_mul_le_of_pow_le hJI' m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans ((hL n).mono (smul_top_pow_le_of_le hIJ n))

theorem isPrecomplete_of_pow_le_of_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete J M] : IsPrecomplete I M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := f) fun {m n} hmn => (hf hmn).mono (smul_top_pow_le_of_le hIJ m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans
    ((hL (N' * n)).mono (smul_top_pow_mul_le_of_pow_le hJI' n))

theorem isAdicComplete_iff_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  constructor
  · intro h
    have := isHausdorff_of_pow_le (M := M) hJI
    have := isPrecomplete_of_le_of_pow_le (M := M) hIJ hJI
    exact ⟨⟩
  · intro h
    have := isHausdorff_of_le (M := M) hIJ
    have := isPrecomplete_of_pow_le_of_le (M := M) hIJ hJI
    exact ⟨⟩

end Compare

section ModuleFinite

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

open AdicCompletion

theorem isPrecomplete_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [IsPrecomplete I M] : IsPrecomplete I N := by
  rw [← of_surjective_iff]
  intro z
  obtain ⟨w, rfl⟩ := map_surjective I hf z
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M w
  exact ⟨f x, (map_of I f x).symm⟩

theorem isPrecomplete_pi (ι : Type*) [Finite ι] [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [← of_surjective_iff]
  intro z
  choose x hx using fun j =>
    AdicCompletion.of_surjective I R (piEquivOfFintype I (fun _ : ι => R) z j)
  refine ⟨x, (piEquivOfFintype I (fun _ : ι => R)).injective ?_⟩
  funext j
  rw [piEquivOfFintype_apply, ← hx j]
  change map I (LinearMap.proj j) (of I (ι → R) x) = _
  rw [map_of]
  rfl

theorem isPrecomplete_of_module_finite [IsPrecomplete I R] [Module.Finite R M] :
    IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have := isPrecomplete_pi I (Fin n)
  exact isPrecomplete_of_surjective I f hf

theorem isAdicComplete_of_module_finite [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : IsAdicComplete I M :=
  haveI := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  haveI := isPrecomplete_of_module_finite I (M := M)
  ⟨⟩

end ModuleFinite

section Local

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing T] [Algebra 𝒪 T]
  [Module.Finite 𝒪 T] [IsLocalRing T]

theorem exists_maximalIdeal_pow_le_map :
    ∃ N, maximalIdeal T ^ N ≤ (maximalIdeal 𝒪).map (algebraMap 𝒪 T) := by
  let : Field (𝒪 ⧸ maximalIdeal 𝒪) := Ideal.Quotient.field _
  have : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  have : IsArtinianRing (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    IsArtinianRing.of_finite (𝒪 ⧸ maximalIdeal 𝒪) _
  exact exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _

theorem isAdicComplete_maximalIdeal_of_module_finite [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [IsLocalHom (algebraMap 𝒪 T)] :
    IsAdicComplete (maximalIdeal T) T := by
  have h1 : IsAdicComplete (maximalIdeal 𝒪) T := isAdicComplete_of_module_finite _
  have h2 : IsAdicComplete ((maximalIdeal 𝒪).map (algebraMap 𝒪 T)) T :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal 𝒪) T).mpr h1
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map (𝒪 := 𝒪) (T := T)
  exact (isAdicComplete_iff_of_le_of_pow_le (map_maximalIdeal_le (algebraMap 𝒪 T)) hN).mp h2

end Local

end M4cP1X1

theorem _root_.IsAdicComplete.of_module_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M :=
  M4cP1X1.isAdicComplete_of_module_finite I
end AlgebraicCurves.Foundations.Algebra.Proofs.IsAdicComplete_of_module_finite
end ProofImplementation
