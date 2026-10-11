/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.TorsorCharacter

/-!
# Change of coefficients for torsor displacement characters

An equivariant map of torsors compatible with a coefficient homomorphism
carries displacement to the image displacement. This is the group-theoretic
naturality needed to prove additivity of the étale H¹ comparison.
-/

noncomputable section

universe u v w

namespace EtaleFundamentalGroups.Cohomology

/-- An additive coefficient homomorphism, viewed as a continuous homomorphism
between the associated discrete multiplicative groups. -/
abbrev discreteCoefficientHom {A : Type v} {B : Type w}
    [AddCommGroup A] [AddCommGroup B] (α : A →+ B) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : TopologicalSpace (Multiplicative B) := ⊥
    Multiplicative A →ₜ* Multiplicative B := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact ⟨α.toMultiplicative, continuous_of_discreteTopology⟩

/-- Displacement commutes with a change of coefficients when the actual torsor
map preserves both actions. No bijectivity of that map is required. -/
theorem torsorCharacter_comp
    {G : Type u} [Group G] [TopologicalSpace G]
    {A : Type v} [CommGroup A] [TopologicalSpace A]
    {B : Type w} [CommGroup B] [TopologicalSpace B]
    {P Q : Type*} [Torsor A P] [Torsor B Q]
    [MulAction G P] [SMulCommClass G A P]
    [MulAction G Q] [SMulCommClass G B Q]
    [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
    [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]
    (α : A →ₜ* B) (f : P → Q)
    (hf : ∀ a : A, ∀ p : P, f (a • p) = α a • f p)
    (hg : ∀ g : G, ∀ p : P, f (g • p) = g • f p) (p : P) :
    α.comp (torsorCharacter (G := G) p) = torsorCharacter (f p) := by
  apply ContinuousMonoidHom.ext
  intro g
  change α ((g • p) /ₛ p) = (g • f p) /ₛ f p
  calc
    α ((g • p) /ₛ p) = (α ((g • p) /ₛ p) • f p) /ₛ f p := (smul_sdiv _ _).symm
    _ = f ((((g • p) /ₛ p) : A) • p) /ₛ f p := congrArg (· /ₛ f p) (hf _ p).symm
    _ = (g • f p) /ₛ f p := by rw [sdiv_smul, hg]

end EtaleFundamentalGroups.Cohomology
