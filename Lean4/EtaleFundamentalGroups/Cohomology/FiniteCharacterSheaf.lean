/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteCharacterExtension
import EtaleFundamentalGroups.Cohomology.FiniteAbelianExact
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# An actual finite étale sheaf extension constructed from a character

The triangular representation on `A × End(A)` descends to a short exact
sequence of actual étale abelian sheaves. The two end terms have trivial
monodromy; the middle term retains the given character. All exactness
statements follow from the explicit inclusion and projection.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- The trivial action on an additive group, with the original additive structure. -/
abbrev trivialAdditiveAction (G M : Type*) [Monoid G] [AddMonoid M] :
    DistribMulAction G M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The kernel inclusion followed by the quotient projection is zero. -/
theorem characterExtension_inclusion_projection_zero (A : Type u) [AddCommGroup A] :
    AddCommGrpCat.ofHom (AddMonoidHom.inl A (A →+ A)) ≫
      AddCommGrpCat.ofHom (AddMonoidHom.snd A (A →+ A)) = 0 := rfl

/-- The original inclusion and projection form a short exact sequence of abelian groups. -/
theorem characterExtension_inclusion_projection_shortExact (A : Type u) [AddCommGroup A] :
    (ShortComplex.mk (AddCommGrpCat.ofHom (AddMonoidHom.inl A (A →+ A)))
      (AddCommGrpCat.ofHom (AddMonoidHom.snd A (A →+ A)))
      (characterExtension_inclusion_projection_zero A)).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · apply (ShortComplex.ab_exact_iff _).mpr
    intro x hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩
  · apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro a b hab
    exact congrArg Prod.fst hab
  · apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro f
    exact ⟨(0, f), rfl⟩

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (A : Type u) [AddCommGroup A] [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A)

/-- The finite sheaf sequence obtained by descending the explicit triangular
representation, together with its proved short exactness. The same local
actions and topologies are shared by the construction and its proof. -/
def finiteCharacterSheafSequence :
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) // S.ShortExact} := by
  let : DistribMulAction (Aut (FiniteEtale.fiber ξ)) A :=
    trivialAdditiveAction (Aut (FiniteEtale.fiber ξ)) A
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) A := ⟨continuous_snd⟩
  have : Finite (A →+ A) := Finite.of_injective
    (fun f : A →+ A => (f : A → A)) DFunLike.coe_injective
  let : Fintype (A →+ A) := Fintype.ofFinite _
  let : TopologicalSpace (A →+ A) := ⊥
  have : DiscreteTopology (A →+ A) := ⟨rfl⟩
  let : DistribMulAction (Aut (FiniteEtale.fiber ξ)) (A →+ A) :=
    trivialAdditiveAction (Aut (FiniteEtale.fiber ξ)) (A →+ A)
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (A →+ A) := ⟨continuous_snd⟩
  let : TopologicalSpace (A × (A →+ A)) := ⊥
  have : DiscreteTopology (A × (A →+ A)) := ⟨rfl⟩
  let extensionAction : DistribMulAction (Aut (FiniteEtale.fiber ξ)) (A × (A →+ A)) :=
    characterExtensionAction χ
  let : SMul (Aut (FiniteEtale.fiber ξ)) (A × (A →+ A)) := extensionAction.toSMul
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) (A × (A →+ A)) :=
    characterExtensionAction_continuous χ
  let S := finiteAbelianMonodromyComplex ξ A (A × (A →+ A)) (A →+ A)
    (AddMonoidHom.inl A (A →+ A)) (AddMonoidHom.snd A (A →+ A))
    (fun g a => (characterExtensionAction_inclusion χ g a).symm)
    (fun _ _ => rfl) (characterExtension_inclusion_projection_zero A)
  exact ⟨S, finiteAbelianMonodromyComplex_shortExact ξ A (A × (A →+ A)) (A →+ A)
    (AddMonoidHom.inl A (A →+ A)) (AddMonoidHom.snd A (A →+ A))
    (fun g a => (characterExtensionAction_inclusion χ g a).symm)
    (fun _ _ => rfl) (characterExtension_inclusion_projection_zero A)
    (characterExtension_inclusion_projection_shortExact A)⟩

end EtaleFundamentalGroups.Cohomology
