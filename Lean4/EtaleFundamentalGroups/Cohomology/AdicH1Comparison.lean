/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import EtaleCohomology.Classical.Adic

/-!
# Classical ℓ-adic H¹ and compatible finite characters

The finite-coefficient comparison is compatible with reduction. It therefore
identifies classical ℓ-adic H¹, defined on the ordinary étale site, with
compatible systems of continuous characters into `ℤ/ℓ^(n+1)ℤ`. Neither
pro-étale cohomology nor an unproved limit comparison is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- Continuous finite cyclic characters, with the character group written additively. -/
abbrev finiteLevelCharacters (ℓ n : ℕ) : Type (u + 1) :=
  let : TopologicalSpace (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⊥
  Additive (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative (ellPowerCoefficients.{u} ℓ n))

/-- Pointwise addition uses the same discrete topology on finite coefficients. -/
instance finiteLevelCharactersAddCommGroup (ℓ n : ℕ) :
    AddCommGroup (finiteLevelCharacters ξ ℓ n) := by
  let : TopologicalSpace (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⊥
  have : DiscreteTopology (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⟨rfl⟩
  exact inferInstanceAs (AddCommGroup (Additive
    (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative (ellPowerCoefficients.{u} ℓ n))))

/-- Reduction of the values of a finite continuous character. -/
def finiteLevelCharacterReduction (ℓ n : ℕ) :
    finiteLevelCharacters ξ ℓ (n + 1) →+ finiteLevelCharacters ξ ℓ n := by
  let : TopologicalSpace (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⊥
  let : TopologicalSpace (Multiplicative (ellPowerCoefficients.{u} ℓ (n + 1))) := ⊥
  have : DiscreteTopology (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⟨rfl⟩
  have : DiscreteTopology (Multiplicative (ellPowerCoefficients.{u} ℓ (n + 1))) := ⟨rfl⟩
  let r := discreteCoefficientHom (ellPowerReduction.{u} ℓ n)
  refine
    { toFun := fun χ => Additive.ofMul (r.comp χ.toMul)
      map_zero' := ?_
      map_add' := ?_ }
  · apply ContinuousMonoidHom.ext
    intro g
    exact r.map_one
  · intro χ ψ
    apply ContinuousMonoidHom.ext
    intro g
    exact r.map_mul (χ.toMul g) (ψ.toMul g)

/-- Compatible families of actual finite continuous characters. -/
def compatibleFiniteCharacters (ℓ : ℕ) :
    AddSubgroup (∀ n, finiteLevelCharacters ξ ℓ n) :=
  sequentialLimit (fun n => finiteLevelCharacters ξ ℓ n)
    (fun n => finiteLevelCharacterReduction ξ ℓ n)

variable (ℓ : ℕ) [Fact ℓ.Prime]

private def levelEquiv (n : ℕ) :
    finiteLevelCohomology X ℓ n 1 ≃+ finiteLevelCharacters ξ ℓ n := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact finiteH1CharacterEquiv (ellPowerCoefficients ℓ n) ξ

private theorem levelEquiv_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 1) :
    finiteLevelCharacterReduction ξ ℓ n (levelEquiv ξ ℓ (n + 1) a) =
      levelEquiv ξ ℓ n (finiteLevelReduction X ℓ n 1 a) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact finiteH1CharacterEquiv_naturality (ellPowerCoefficients ℓ (n + 1)) ξ
    (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) a

/-- Classical ℓ-adic H¹ is canonically the group of compatible finite
continuous fundamental-group characters. The compatibility is proved from
the original maps of constant coefficient sheaves. -/
def ellAdicH1CompatibleCharacterEquiv :
    ellAdicCohomology X ℓ 1 ≃+ compatibleFiniteCharacters ξ ℓ where
  toFun a := ⟨fun n => levelEquiv ξ ℓ n (a.val n), fun n =>
    (levelEquiv_reduction ξ ℓ n (a.val (n + 1))).trans
      (congrArg (levelEquiv ξ ℓ n) (a.property n))⟩
  invFun χ := ⟨fun n => (levelEquiv ξ ℓ n).symm (χ.val n), fun n => by
    apply (levelEquiv ξ ℓ n).injective
    exact (levelEquiv_reduction ξ ℓ n
      ((levelEquiv ξ ℓ (n + 1)).symm (χ.val (n + 1)))).symm.trans
        ((congrArg (finiteLevelCharacterReduction ξ ℓ n)
          ((levelEquiv ξ ℓ (n + 1)).apply_symm_apply (χ.val (n + 1)))).trans
            ((χ.property n).trans ((levelEquiv ξ ℓ n).apply_symm_apply (χ.val n)).symm))⟩
  left_inv a := Subtype.ext (funext fun n => (levelEquiv ξ ℓ n).symm_apply_apply (a.val n))
  right_inv χ := Subtype.ext (funext fun n => (levelEquiv ξ ℓ n).apply_symm_apply (χ.val n))
  map_add' a b := Subtype.ext (funext fun n => (levelEquiv ξ ℓ n).map_add (a.val n) (b.val n))

end EtaleFundamentalGroups.Cohomology
