/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPowerSeries_isNoetherianRing_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Data.Finsupp.Option
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Mv Power Series is Noetherian Ring of finite
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace MvPowerSeries_isNoetherianRing_of_finite

universe u v w

noncomputable section

namespace M4cP1PS

open Finsupp Finset

section Equiv

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Regroup a power series in an optional variable as a power series in one variable with
multivariable power-series coefficients. -/
def optFun (φ : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n => fun d => MvPowerSeries.coeff (d.optionElim n) φ

/-- Recover a power series in an optional variable from its coefficients as a power series in
one variable. -/
def optInv (ψ : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun m => MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ)
@[scoped simp]
theorem coeff_coeff_optFun (φ : MvPowerSeries (Option σ) R) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optFun φ)) = MvPowerSeries.coeff (d.optionElim n) φ
      := by
  exact congrArg (MvPowerSeries.coeff d)
    (PowerSeries.coeff_mk n
      (fun k => (fun m => MvPowerSeries.coeff (m.optionElim k) φ : MvPowerSeries σ R)))
@[scoped simp]
theorem coeff_optInv (ψ : PowerSeries (MvPowerSeries σ R)) (m : Option σ →₀ ℕ) :
    MvPowerSeries.coeff m (optInv ψ) = MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ) :=
  rfl

theorem optInv_optFun (φ : MvPowerSeries (Option σ) R) : optInv (optFun φ) = φ := by
  ext m
  rw [coeff_optInv, coeff_coeff_optFun, optionElim_some]

theorem optFun_optInv (ψ : PowerSeries (MvPowerSeries σ R)) : optFun (optInv ψ) = ψ := by
  ext n d
  rw [coeff_coeff_optFun, coeff_optInv, some_optionElim, optionElim_apply_none]

theorem optFun_add (φ ψ : MvPowerSeries (Option σ) R) : optFun (φ + ψ) = optFun φ + optFun ψ := by
  ext n d
  simp only [map_add, coeff_coeff_optFun]

theorem optFun_mul (φ ψ : MvPowerSeries (Option σ) R) : optFun (φ * ψ) = optFun φ * optFun ψ := by
  classical
  ext n d
  rw [coeff_coeff_optFun, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp_rw [MvPowerSeries.coeff_mul, coeff_coeff_optFun]
  rw [← sum_product']
  refine sum_nbij' (fun p => ((p.1 none, p.2 none), (p.1.some, p.2.some)))
    (fun q => (q.2.1.optionElim q.1.1, q.2.2.optionElim q.1.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_antidiagonal] at hp
    rw [mem_product, mem_antidiagonal, mem_antidiagonal, ← Finsupp.add_apply, hp, ← some_add, hp,
      optionElim_apply_none, some_optionElim]
    exact ⟨rfl, rfl⟩
  · intro q hq
    rw [mem_product, mem_antidiagonal, mem_antidiagonal] at hq
    rw [mem_antidiagonal, ← optionElim_add, hq.1, hq.2]
  · intro p _
    simp only [optionElim_some]
  · intro q _
    simp only [some_optionElim, optionElim_apply_none, Prod.mk.eta]
  · intro p _
    simp only [optionElim_some]

/-- The ring equivalence between power series in an optional variable and iterated power series. -/
def optRingEquiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := optFun
  invFun := optInv
  left_inv := optInv_optFun
  right_inv := optFun_optInv
  map_mul' := optFun_mul
  map_add' := optFun_add

end Equiv

section Noetherian

variable (R : Type*) [CommRing R] [IsNoetherianRing R]

theorem isNoetherianRing_fin : ∀ n : ℕ, IsNoetherianRing (MvPowerSeries (Fin n) R)
  | 0 => isNoetherianRing_of_surjective R _ MvPowerSeries.C MvPowerSeries.C_surjective
  | n + 1 => by
    have := isNoetherianRing_fin n
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) R))
      (optRingEquiv.symm.trans (MvPowerSeries.renameEquiv R (finSuccEquiv n).symm).toRingEquiv)

theorem isNoetherianRing_of_finite (σ : Type*) [Finite σ] : IsNoetherianRing (MvPowerSeries σ R) :=
  by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have := isNoetherianRing_fin R n
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin n) R)
    (MvPowerSeries.renameEquiv R e.symm).toRingEquiv

end Noetherian

end M4cP1PS

end

theorem _root_.MvPowerSeries.isNoetherianRing_of_finite {σ : Type u} {R : Type v} [Finite σ]
  [CommRing R]
    [IsNoetherianRing R] : IsNoetherianRing (MvPowerSeries σ R) :=
  M4cP1PS.isNoetherianRing_of_finite R σ
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.MvPowerSeries_isNoetherianRing_of_finite
end ProofImplementation
