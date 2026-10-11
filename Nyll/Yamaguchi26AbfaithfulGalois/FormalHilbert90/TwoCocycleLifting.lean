/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteH1Surjectivity
import Nyll.GaloisCohomology.Topology.FiniteCocycleLifting

/-! # Formal Hilbert 90 from prime-field H² vanishing -/

namespace Yamaguchi26AbfaithfulGalois
universe u
variable {p : ℕ} [Fact p.Prime]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Prime-field H² vanishing supplies successive lifts of finite twisted cocycles. -/
theorem exists_finiteCocycle_lift_succ_of_twoCocycles
    (θ : Orientation p G) (H : Subgroup G)
    (hθ : ∀ g : G, PadicInt.toZModPow 1 (θ g : PadicInt p) = 1)
    (hH2 : ∀ z : H → H → ZMod p,
      (∀ σ τ υ : H, z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ) →
      IsLocallyConstant (fun x : H × H => z x.1 x.2) →
      ∃ d : H → ZMod p, IsLocallyConstant d ∧
        ∀ σ τ : H, d τ - d (σ * τ) + d σ = z σ τ)
    (n : ℕ) (c : FiniteCocycle θ H n) :
    ∃ d : FiniteCocycle θ H (n + 1), ∀ g : H,
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
        (d.toFun g) = c.toFun g := by
  let θH : H →ₜ* (PadicInt p)ˣ :=
    θ.comp ⟨H.subtype, continuous_subtype_val⟩
  let θn : H →ₜ* (ZMod (p ^ (n + 1)))ˣ :=
    { toMonoidHom := (Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom).comp
        θH.toMonoidHom
      continuous_toFun := ((PadicInt.continuous_toZModPow (n + 1)).units_map
        (PadicInt.toZModPow (n + 1)).toMonoidHom).comp θH.continuous }
  have hθn (g : H) :
      ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
        (θn g : ZMod (p ^ (n + 1))) = 1 := by
    have h := RingHom.congr_fun
      (PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
      (θ (g : G) : PadicInt p)
    have hh := h.trans (hθ g)
    change ZMod.castHom (pow_dvd_pow p (Nat.succ_le_succ (Nat.zero_le n)))
      (ZMod (p ^ 1)) (PadicInt.toZModPow (n + 1) (θ (g : G) : PadicInt p)) = 1 at hh
    change ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
      (PadicInt.toZModPow (n + 1) (θ (g : G) : PadicInt p)) = 1
    have hh' := congrArg (ZMod.castHom (show p ∣ p ^ 1 by rw [pow_one]) (ZMod p)) hh
    rw [map_one] at hh'
    have hcomp := RingHom.congr_fun
      (ZMod.castHom_comp (show p ∣ p ^ 1 by rw [pow_one])
        (pow_dvd_pow p (Nat.succ_le_succ (Nat.zero_le n))))
      (PadicInt.toZModPow (n + 1) (θ (g : G) : PadicInt p))
    exact hcomp.symm.trans hh'
  have hc (σ τ : H) : c.toFun (σ * τ) = c.toFun σ +
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
        (θn σ : ZMod (p ^ (n + 1))) * c.toFun τ := by
    rw [c.cocycle]
    congr 1
    congr 1
    exact (RingHom.congr_fun
      (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n))
      (θ (σ : G) : PadicInt p)).symm
  obtain ⟨d, hdcont, hd, hred⟩ :=
    GaloisCohomology.exists_lift_crossed_cocycle_succ hH2 n θn hθn
      c.toFun c.continuous_toFun hc
  exact ⟨⟨d, hdcont, hd⟩, hred⟩

/-- Vanishing of prime-field H² on open subgroups proves the actual formal
Hilbert 90 reduction maps for orientations trivial modulo the prime. -/
theorem formalHilbert90_of_twoCocycles
    (θ : Orientation p G)
    (hθ : ∀ g : G, PadicInt.toZModPow 1 (θ g : PadicInt p) = 1)
    (hH2 : ∀ H : OpenSubgroup G, ∀ z : ↥(H : Subgroup G) → ↥(H : Subgroup G) → ZMod p,
      (∀ σ τ υ : (H : Subgroup G),
        z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ) →
      IsLocallyConstant (fun x : ↥(H : Subgroup G) × ↥(H : Subgroup G) => z x.1 x.2) →
      ∃ d : ↥(H : Subgroup G) → ZMod p, IsLocallyConstant d ∧
        ∀ σ τ : (H : Subgroup G), d τ - d (σ * τ) + d σ = z σ τ) :
    FormalHilbert90 θ := by
  intro H n hn
  apply h1_reduction_surjective_of_finiteCocycle_lifting
  intro c
  cases n with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      refine ⟨c, ?_⟩
      intro g
      rw [ZMod.castHom_self]
      rfl
    | succ k ih =>
      obtain ⟨d, hd⟩ := ih (by omega)
      obtain ⟨e, he⟩ := exists_finiteCocycle_lift_succ_of_twoCocycles
        θ H hθ (hH2 H) (k + 1) d
      refine ⟨e, ?_⟩
      intro g
      have hcast := RingHom.congr_fun
        (ZMod.castHom_comp (pow_dvd_pow p (show 1 ≤ k + 1 by omega))
          (pow_dvd_pow p (Nat.le_succ (k + 1)))) (e.toFun g)
      exact hcast.symm.trans ((congrArg
        (ZMod.castHom (pow_dvd_pow p (show 1 ≤ k + 1 by omega)) (ZMod (p ^ 1)))
        (he g)).trans (hd g))

end Yamaguchi26AbfaithfulGalois
