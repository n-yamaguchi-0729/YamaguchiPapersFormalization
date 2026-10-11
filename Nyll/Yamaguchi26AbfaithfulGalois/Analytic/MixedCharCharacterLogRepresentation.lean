/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogRepresentation
import Nyll.ValuedFieldTheory.LocalField.Analytic.RepresentationCharacterTwist
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Invariants

/-!
# The character subspace of the actual principal-unit logarithm image

The range carries its inherited p-adic module structure. Twisting its actual
representation and taking subgroup invariants constructs the character
subspace. Normality supplies stability under the full group action; it is
not needed for the field inclusion, eigenvector criterion, or saturation.
No p-adic module structure is registered on the ambient field.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u w

variable {K : Type u} [Field K] [CharZero K]
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
  [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
  (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]

/-- The actual logarithm image, with the module structure inherited from its range. -/
abbrev PrincipalUnitLogImageOfMixedChar : Type u :=
  ↥(@LinearMap.range ℤ_[p] ℤ_[p]
    (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) K
    _ _ _ _ (principalUnitPadicModuleOfMixedChar v p)
    (padicIntToFieldOfMixedChar v p).toModule (RingHom.id ℤ_[p]) inferInstance
    (principalUnitLogLinearMapOfMixedChar v p))

section ImageAction

variable {Γ : Type w} [Monoid Γ]
  (σ : Γ →* (K ≃+* K)) (hval : ∀ (g : Γ) (x : K), v (σ g x) = v x)

/-- Logarithm equivariance supplies the action on its actual range. -/
def principalUnitLogImageRepresentationOfMixedChar :
    Representation ℤ_[p] Γ (PrincipalUnitLogImageOfMixedChar v p) :=
  @Subrepresentation.toRepresentation ℤ_[p] Γ K _ _ _
    (padicIntToFieldOfMixedChar v p).toModule
    (fieldRepresentationOfMixedChar v p σ hval)
    (@Representation.IntertwiningMap.range ℤ_[p] Γ
      (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) K
      _ _ _ _ (principalUnitPadicModuleOfMixedChar v p)
      (padicIntToFieldOfMixedChar v p).toModule
      (principalUnitRepresentationOfMixedChar v p σ hval)
      (fieldRepresentationOfMixedChar v p σ hval)
      (principalUnitLogIntertwinerOfMixedChar v p σ hval))

end ImageAction

section CharacterSpace

variable {Γ : Type w} [Group Γ]
  (σ : Γ →* (K ≃+* K)) (hval : ∀ (g : Γ) (x : K), v (σ g x) = v x)
  (χ : Γ →* ℤ_[p]ˣ) (Δ : Subgroup Γ)

/-- The actual character submodule of the logarithm image. -/
def characterLogSubmoduleOfMixedChar :
    Submodule ℤ_[p] (PrincipalUnitLogImageOfMixedChar v p) :=
  Representation.invariants ((inverseCharacterTwist χ
    (principalUnitLogImageRepresentationOfMixedChar v p σ hval)).comp Δ.subtype)

/-- The character log space uses the existing submodule carrier and its module. -/
abbrev CharacterLogSpaceOfMixedChar : Type u :=
  ↥(characterLogSubmoduleOfMixedChar v p σ hval χ Δ)

/-- The original field value of a vector in the character log space. -/
def characterLogInclusionOfMixedChar :
    CharacterLogSpaceOfMixedChar v p σ hval χ Δ →+ K where
  toFun x := ((x : PrincipalUnitLogImageOfMixedChar v p) : K)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Passing to the original field loses no information. -/
theorem characterLogInclusionOfMixedChar_injective :
    Function.Injective (characterLogInclusionOfMixedChar v p σ hval χ Δ) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

/-- Every character log vector retains a preimage under the original logarithm. -/
theorem exists_principalUnit_log_eq_characterLogInclusion
    (x : CharacterLogSpaceOfMixedChar v p σ hval χ Δ) :
    ∃ a : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      (principalUnitLogOfMixedChar v p a).toAdd =
        characterLogInclusionOfMixedChar v p σ hval χ Δ x := by
  obtain ⟨a, ha⟩ := x.val.property
  exact ⟨Additive.toMul a, ha⟩

/-- Membership is the actual character eigenvector equation in the field. -/
theorem mem_characterLogSubmoduleOfMixedChar_iff
    (x : PrincipalUnitLogImageOfMixedChar v p) :
    x ∈ characterLogSubmoduleOfMixedChar v p σ hval χ Δ ↔
      ∀ δ : Δ, σ (δ : Γ) (x : K) =
        padicIntToFieldOfMixedChar v p (χ (δ : Γ) : ℤ_[p]) * (x : K) := by
  change x ∈ (inverseCharacterTwist (χ.comp Δ.subtype)
    ((principalUnitLogImageRepresentationOfMixedChar v p σ hval).comp Δ.subtype)).invariants ↔ _
  rw [inverseCharacterTwist_mem_invariants_iff]
  constructor
  · intro hx δ
    exact congrArg (fun y : PrincipalUnitLogImageOfMixedChar v p => (y : K)) (hx δ)
  · intro hx δ
    exact Subtype.ext (hx δ)

/-- The character condition is saturated inside the actual log image for nonzero
natural multiples. Characteristic zero is inherited from the original field. -/
theorem mem_characterLogSubmoduleOfMixedChar_of_nsmul_mem
    (n : ℕ) (hn : n ≠ 0) (x : PrincipalUnitLogImageOfMixedChar v p)
    (hx : n • x ∈ characterLogSubmoduleOfMixedChar v p σ hval χ Δ) :
    x ∈ characterLogSubmoduleOfMixedChar v p σ hval χ Δ := by
  apply (mem_characterLogSubmoduleOfMixedChar_iff v p σ hval χ Δ x).mpr
  intro δ
  have hδ := (mem_characterLogSubmoduleOfMixedChar_iff v p σ hval χ Δ (n • x)).mp hx δ
  change σ (δ : Γ) (n • (x : K)) =
    padicIntToFieldOfMixedChar v p (χ (δ : Γ) : ℤ_[p]) * (n • (x : K)) at hδ
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn : (n : K) ≠ 0)
  simpa only [nsmul_eq_mul, _root_.map_mul, _root_.map_natCast, mul_left_comm] using hδ

variable [Δ.Normal]

/-- Normality constructs the full group action on the character log space. -/
def characterLogRepresentationOfMixedChar :
    Representation ℤ_[p] Γ (CharacterLogSpaceOfMixedChar v p σ hval χ Δ) :=
  (inverseCharacterTwist χ
    (principalUnitLogImageRepresentationOfMixedChar v p σ hval)).toInvariants Δ

/-- The constructed action is exactly the inverse-character-twisted field action. -/
theorem characterLogInclusionOfMixedChar_action
    (g : Γ) (x : CharacterLogSpaceOfMixedChar v p σ hval χ Δ) :
    characterLogInclusionOfMixedChar v p σ hval χ Δ
        (characterLogRepresentationOfMixedChar v p σ hval χ Δ g x) =
      padicIntToFieldOfMixedChar v p (((χ g)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
        σ g (characterLogInclusionOfMixedChar v p σ hval χ Δ x) := rfl

end CharacterSpace

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
