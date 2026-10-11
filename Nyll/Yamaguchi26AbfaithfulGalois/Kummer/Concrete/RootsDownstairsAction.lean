/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.RootsDownstairs
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ProCGroups.ProP.ContinuousH1

/-!
# Roots downstairs and the canonical actions

The moved classes constructed from eigenunits detect the genuine relative
Galois action on H¹ and the canonical action on topological abelianization.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ClassFieldTower.ProP

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

attribute [local instance] discreteZModTopology discreteZMod

/-- Every nonidentity relative automorphism acts nontrivially on continuous H¹
at the last prime-power root level. -/
theorem rootsDownstairs_h1_action_ne_one
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L))
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) L).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) L).Nonempty → m ≤ s) ∧
      relativeGaloisH1Action (n := p ^ s) K L τ ≠ 1 := by
  obtain ⟨s, hs, hμs, hmax, c, σ, hσ⟩ :=
    rootsDownstairs_exists_moved_h1 hp hdeg hμ hfinite hdown τ⁻¹ (inv_ne_one.mpr hτ)
  refine ⟨s, hs, hμs, hmax, ?_⟩
  intro heq
  have hvalue := congrArg
    (fun a : Multiplicative
      (AddAut (ContinuousH1ZMod (p := p ^ s) (G := Field.absoluteGaloisGroup L))) =>
      a.toAdd c (Additive.ofMul (σ : Field.absoluteGaloisGroup L))) heq
  rw [relativeGaloisH1Action_apply] at hvalue
  exact hσ hvalue

/-- The last prime-power root level gives a faithful relative Galois action
on continuous degree-one classes. Maximality makes this level uniform in `τ`. -/
theorem rootsDownstairs_faithful_h1_action
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L)) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) L).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) L).Nonempty → m ≤ s) ∧
      Function.Injective (relativeGaloisH1Action (n := p ^ s) K L) := by
  obtain ⟨s, hs, hμs, hmax, _τ, _hτ, _c, _σ, _hσ⟩ :=
    rootsDownstairs_nontrivial_h1 hp hdeg hμ hfinite hdown
  refine ⟨s, hs, hμs, hmax, (injective_iff_map_eq_one
    (relativeGaloisH1Action (n := p ^ s) K L)).mpr ?_⟩
  intro τ hτ
  by_contra hne
  obtain ⟨t, _ht, hμt, hmaxt, hdetect⟩ :=
    rootsDownstairs_h1_action_ne_one hp hdeg hμ hfinite hdown τ hne
  have ht : t = s := Nat.le_antisymm (hmax t hμt) (hmaxt s hμs)
  subst t
  exact hdetect hτ

/-- Roots downstairs detect the canonical automorphism of the abelianized
absolute Galois group, with no chosen-lift assumption. -/
theorem rootsDownstairs_abelianization_action_ne_one
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L))
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    absoluteGaloisAbelianizationAction τ.toRingEquiv ≠ 1 := by
  obtain ⟨s, _hs, _hμs, _hmax, c, σ, hσ⟩ :=
    rootsDownstairs_exists_moved_h1 hp hdeg hμ hfinite hdown τ hτ
  apply absoluteGaloisAbelianizationAction_ne_one_of_character_ne
    τ.toRingEquiv (characterOfH1 c) (σ := σ)
  intro heq
  exact hσ (congrArg Multiplicative.toAdd heq)

end ClassFieldTower.Martinet.Shafarevich
