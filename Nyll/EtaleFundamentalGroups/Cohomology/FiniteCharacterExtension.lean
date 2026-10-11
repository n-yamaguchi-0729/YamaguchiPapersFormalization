/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# A finite linear extension constructed from a character

For an additive abelian group `A`, a character acts on `A × End(A)` by
`g • (a, f) = (a + f(χ(g)), f)`. Thus both the kernel `A` and the quotient
`End(A)` have trivial action. The inverse image of the identity endomorphism
has displacement exactly `χ`. If `A` is finite, this whole extension is finite;
no choice of an exponent or an invertibility hypothesis is required.
-/

noncomputable section

universe u v

namespace EtaleFundamentalGroups.Cohomology

variable {G : Type v} [Group G] [TopologicalSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A]
  (χ : G →ₜ* Multiplicative A)

/-- The triangular action constructed from a continuous character. -/
abbrev characterExtensionAction : DistribMulAction G (A × (A →+ A)) where
  smul g x := (x.1 + x.2 (χ g).toAdd, x.2)
  one_smul x := by
    apply Prod.ext
    · change x.1 + x.2 (χ 1).toAdd = x.1
      rw [map_one]
      exact (congrArg (x.1 + ·) x.2.map_zero).trans (add_zero x.1)
    · rfl
  mul_smul g h x := by
    apply Prod.ext
    · change x.1 + x.2 (χ (g * h)).toAdd =
        (x.1 + x.2 (χ h).toAdd) + x.2 (χ g).toAdd
      rw [map_mul]
      change x.1 + x.2 ((χ g).toAdd + (χ h).toAdd) = _
      rw [map_add, add_comm (x.2 (χ g).toAdd), add_assoc]
    · rfl
  smul_zero g := by
    apply Prod.ext
    · exact add_zero 0
    · rfl
  smul_add g x y := by
    apply Prod.ext
    · change (x.1 + y.1) + (x.2 (χ g).toAdd + y.2 (χ g).toAdd) =
        (x.1 + x.2 (χ g).toAdd) + (y.1 + y.2 (χ g).toAdd)
      exact add_add_add_comm _ _ _ _
    · rfl

/-- The triangular action is continuous on the discrete extension group. -/
theorem characterExtensionAction_continuous [DiscreteTopology A] :
    let : TopologicalSpace (A × (A →+ A)) := ⊥
    let : DistribMulAction G (A × (A →+ A)) := characterExtensionAction χ
    ContinuousSMul G (A × (A →+ A)) := by
  let : TopologicalSpace (A × (A →+ A)) := ⊥
  have : DiscreteTopology (A × (A →+ A)) := ⟨rfl⟩
  let : DistribMulAction G (A × (A →+ A)) := characterExtensionAction χ
  constructor
  apply continuous_prod_of_discrete_right.mpr
  intro x
  exact (continuous_of_discreteTopology
    (f := fun a : Multiplicative A => (x.1 + x.2 a.toAdd, x.2))).comp χ.continuous

/-- The included coefficient group has trivial monodromy. -/
theorem characterExtensionAction_inclusion (g : G) (a : A) :
    let : DistribMulAction G (A × (A →+ A)) := characterExtensionAction χ
    g • (a, (0 : A →+ A)) = (a, 0) := by
  exact Prod.ext (add_zero a) rfl

/-- Projection to the endomorphism group has trivial monodromy. -/
theorem characterExtensionAction_projection (g : G) (x : A × (A →+ A)) :
    let : DistribMulAction G (A × (A →+ A)) := characterExtensionAction χ
    (g • x).2 = x.2 := rfl

/-- The fiber of the identity endomorphism recovers the original character. -/
theorem characterExtensionAction_identityFiber (g : G) :
    let : DistribMulAction G (A × (A →+ A)) := characterExtensionAction χ
    g • (0, AddMonoidHom.id A) = ((χ g).toAdd, AddMonoidHom.id A) := by
  exact Prod.ext (zero_add (χ g).toAdd) rfl

end EtaleFundamentalGroups.Cohomology
