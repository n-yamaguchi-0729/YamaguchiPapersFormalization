/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Torsor.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Characters obtained from monodromy on abelian torsors

A continuous action on a discrete abelian torsor, commuting with translation,
determines a continuous character. Its value is displacement of any chosen
point; commutativity makes the answer independent of that point. This is the
group-theoretic part of the degree-one étale cohomology comparison.
-/

noncomputable section

universe u v w

namespace EtaleFundamentalGroups.Cohomology

variable {G : Type u} [Group G] [TopologicalSpace G]
  {A : Type v} [CommGroup A] [TopologicalSpace A]
  {P : Type w} [Torsor A P] [MulAction G P] [SMulCommClass G A P]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

/-- Monodromy displacement in a discrete abelian torsor is a continuous character. -/
def torsorCharacter (p : P) : G →ₜ* A where
  toFun g := (g • p) /ₛ p
  map_one' := by rw [one_smul, sdiv_self]
  map_mul' g h := by
    conv_lhs =>
      rw [mul_smul, ← sdiv_smul (h • p) p, smul_comm, smul_sdiv_assoc]
    exact mul_comm _ _
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous (fun q : P => q /ₛ p)).comp
      (continuous_id.smul continuous_const)

/-- For abelian coefficients the character is independent of the point in the torsor. -/
theorem torsorCharacter_eq (p q : P) : torsorCharacter (G := G) p = torsorCharacter q := by
  apply ContinuousMonoidHom.ext
  intro g
  change ((g • p) /ₛ p : A) = (g • q) /ₛ q
  conv_rhs => rw [← sdiv_smul q p]
  rw [smul_comm, smul_sdiv_smul_cancel_left]

/-- The character is trivial exactly when one, equivalently every, point is fixed. -/
theorem torsorCharacter_eq_one_iff (p : P) :
    torsorCharacter (G := G) p = 1 ↔ ∀ g : G, g • p = p := by
  constructor
  · intro h g
    apply sdiv_eq_one_iff_eq.mp
    exact congrArg (fun f : G →ₜ* A => f g) h
  · intro h
    apply ContinuousMonoidHom.ext
    intro g
    change ((g • p) /ₛ p : A) = 1
    rw [h g, sdiv_self]

/-- An equivariant map preserving coefficient translations preserves the
displacement character. No choice of torsor point enters this compatibility. -/
theorem torsorCharacter_map
    {Q : Type*} [Torsor A Q] [MulAction G Q] [SMulCommClass G A Q]
    [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]
    (f : P → Q) (hf : ∀ a : A, ∀ p : P, f (a • p) = a • f p)
    (hg : ∀ g : G, ∀ p : P, f (g • p) = g • f p) (p : P) :
    torsorCharacter (G := G) p = torsorCharacter (f p) := by
  apply ContinuousMonoidHom.ext
  intro g
  change ((g • p) /ₛ p : A) = (g • f p) /ₛ f p
  calc
    ((g • p) /ₛ p : A) = (((g • p) /ₛ p) • f p) /ₛ f p :=
      (smul_sdiv _ _).symm
    _ = f ((((g • p) /ₛ p) : A) • p) /ₛ f p := congrArg (· /ₛ f p) (hf _ p).symm
    _ = (g • f p) /ₛ f p := by rw [sdiv_smul, hg]

/-- The character on the topological abelianization uses the actual quotient
by the closed commutator subgroup. -/
def torsorAbelianCharacter [IsTopologicalGroup G] [T1Space A] (p : P) :
    TopologicalAbelianization G →ₜ* A :=
  ProCGroups.Abelian.TopologicalAbelianization.lift (torsorCharacter (G := G) p)

/-- Evaluating the descended character on a quotient class gives the original
monodromy displacement. -/
theorem torsorAbelianCharacter_apply_mk [IsTopologicalGroup G] [T1Space A]
    (p : P) (g : G) :
    torsorAbelianCharacter p (ProCGroups.Abelian.TopologicalAbelianization.mk G g) =
      (g • p) /ₛ p :=
  ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk _ _

end EtaleFundamentalGroups.Cohomology
