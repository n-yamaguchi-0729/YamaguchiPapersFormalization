/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummer
import GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummerNaturality
import GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Mathlib.Topology.Instances.ZMod

/-!
# Kummer criterion for a trivial mod-n action

Equation `eq:kummer-trivial` in Section 3. The left side says that
conjugation is trivial on `G_Kᵃᵇ/n`, using its exact character-dual
description: every continuous `ZMod n`-valued character is fixed.
The right side says `τ(x)/x^a` is an `n`-th power for every unit `x`.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory

universe u

/-- If `τ` acts by the `a`-th power on `μ_n`, its action on the mod-`n`
abelianization is trivial exactly when `τ(x)/x^a` is an `n`-th power
for every nonzero `x`. -/
theorem kummer_trivial_action_criterion
    (K : Type u) [Field K]
    (n : ℕ+) [NeZero ((n : ℕ) : K)]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (τ : K ≃+* K) (a : ℕ)
    (hpower : ∀ ξ : K, ξ ^ (n : ℕ) = 1 → τ ξ = ξ ^ a) :
    (∀ (χ : Gal(AlgebraicClosure K/K) →ₜ*
          Multiplicative (ZMod (n : ℕ)))
        (σ : Gal(AlgebraicClosure K/K)),
        χ (absoluteGaloisConjugate τ σ) = χ σ) ↔
      ∀ x : Kˣ,
        ((Units.map τ.toMonoidHom x : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) =
          (x : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ^ a := by
  let e : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      (Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod (n : ℕ))) :=
    ClassFieldTower.Martinet.Shafarevich.separableAbsoluteKummerContinuousZModCharacterEquiv
      K n hmu
  have hnat (x : Kˣ) (σ : Gal(AlgebraicClosure K/K)) :
      e ((Units.map τ.toMonoidHom x : Kˣ) :
          Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
          (absoluteGaloisConjugate τ σ) =
        e (x : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ ^ a :=
    (open _root_.ClassFieldTower.Martinet.Shafarevich in
      separableAbsoluteKummerContinuousZModCharacterEquiv_naturality_of_pow_roots
        K n hmu τ a hpower x σ)
  constructor
  · intro h x
    apply e.injective
    apply ContinuousMonoidHom.ext
    intro σ
    rw [map_pow, ContinuousMonoidHom.pow_apply]
    exact (h (e ((Units.map τ.toMonoidHom x : Kˣ) :
      Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)) σ).symm.trans (hnat x σ)
  · intro h χ σ
    obtain ⟨z, rfl⟩ := e.surjective χ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range z
    let y : Kˣ := Units.map τ.symm.toMonoidHom x
    have hy : Units.map τ.toMonoidHom y = x := by
      apply Units.ext
      exact τ.apply_symm_apply (x : K)
    have hx : (x : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) =
        (y : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) ^ a := by
      rw [← hy]
      exact h y
    have hn := hnat y σ
    rw [hy] at hn
    refine hn.trans ?_
    change e (y : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ ^ a =
      e (x : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) σ
    rw [hx, map_pow, ContinuousMonoidHom.pow_apply]

end Yamaguchi26AbfaithfulGalois
