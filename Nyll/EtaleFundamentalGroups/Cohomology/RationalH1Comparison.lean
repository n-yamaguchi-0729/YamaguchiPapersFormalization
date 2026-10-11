/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.LinearAdicH1Comparison
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ValuedFieldTheory.LocalField.Padic.CompactDenominator
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Classical rational ℓ-adic H¹ and continuous characters

Compactness of the actual étale fundamental group gives a common integral
denominator for each continuous Qℓ-valued character. Consequently its module
of continuous Qℓ-valued characters is the scalar extension of its integral
character module. This identifies ordinary rational ℓ-adic H¹ with actual
continuous Qℓ-valued characters, without a pro-étale definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]
  (ξ : Spec (.of Ω) ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Continuous characters into the additive group of the actual p-adic field. -/
abbrev rationalPadicCharacters : Type (u + 1) :=
  Additive (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative ℚ_[ℓ])

private def scaleRationalCharacter (c : ℚ_[ℓ]) (χ : rationalPadicCharacters ξ ℓ) :
    rationalPadicCharacters ξ ℓ := Additive.ofMul
  { toFun := fun g => Multiplicative.ofAdd (c * (χ.toMul g).toAdd)
    map_one' := (congrArg (fun z : Multiplicative ℚ_[ℓ] =>
      Multiplicative.ofAdd (c * z.toAdd)) (map_one χ.toMul)).trans
        (congrArg Multiplicative.ofAdd (mul_zero c))
    map_mul' g h := (congrArg (fun z : Multiplicative ℚ_[ℓ] =>
      Multiplicative.ofAdd (c * z.toAdd)) (map_mul χ.toMul g h)).trans
        (congrArg Multiplicative.ofAdd (mul_add c (χ.toMul g).toAdd (χ.toMul h).toAdd))
    continuous_toFun := continuous_ofAdd.comp
      (continuous_const.mul (continuous_toAdd.comp χ.toMul.continuous)) }

/-- Rational scalars act on continuous characters by pointwise multiplication. -/
instance rationalPadicCharactersModule : Module ℚ_[ℓ] (rationalPadicCharacters ξ ℓ) where
  smul := scaleRationalCharacter ξ ℓ
  one_smul χ := ContinuousMonoidHom.ext fun g =>
    congrArg Multiplicative.ofAdd (one_mul (χ.toMul g).toAdd)
  mul_smul c d χ := ContinuousMonoidHom.ext fun g =>
    congrArg Multiplicative.ofAdd (mul_assoc c d (χ.toMul g).toAdd)
  smul_zero c := ContinuousMonoidHom.ext fun _ =>
    congrArg Multiplicative.ofAdd (mul_zero c)
  smul_add c χ ψ := ContinuousMonoidHom.ext fun g =>
    congrArg Multiplicative.ofAdd (mul_add c (χ.toMul g).toAdd (ψ.toMul g).toAdd)
  add_smul c d χ := ContinuousMonoidHom.ext fun g =>
    congrArg Multiplicative.ofAdd (add_mul c d (χ.toMul g).toAdd)
  zero_smul χ := ContinuousMonoidHom.ext fun g =>
    congrArg Multiplicative.ofAdd (zero_mul (χ.toMul g).toAdd)

/-- Integral scalars use the canonical inclusion of p-adic integers into their field. -/
instance rationalPadicCharactersIntegralModule :
    Module ℤ_[ℓ] (rationalPadicCharacters ξ ℓ) :=
  Module.compHom (rationalPadicCharacters ξ ℓ) (algebraMap ℤ_[ℓ] ℚ_[ℓ])

/-- The integral and rational actions use the same scalar multiplication. -/
instance rationalPadicCharactersScalarTower :
    IsScalarTower ℤ_[ℓ] ℚ_[ℓ] (rationalPadicCharacters ξ ℓ) where
  smul_assoc c d χ := ContinuousMonoidHom.ext fun g =>
    congrArg Multiplicative.ofAdd (mul_assoc (c : ℚ_[ℓ]) d (χ.toMul g).toAdd)

/-- Inclusion of integral characters into rational characters, with the actual scalar actions. -/
def integralCharacterInclusion :
    padicCharacters ξ ℓ →ₗ[ℤ_[ℓ]] rationalPadicCharacters ξ ℓ where
  toFun χ := Additive.ofMul
    { toFun := fun g => Multiplicative.ofAdd ((χ.toMul g).toAdd : ℚ_[ℓ])
      map_one' := congrArg (fun z : Multiplicative ℤ_[ℓ] =>
        Multiplicative.ofAdd (z.toAdd : ℚ_[ℓ])) (map_one χ.toMul)
      map_mul' g h := congrArg (fun z : Multiplicative ℤ_[ℓ] =>
        Multiplicative.ofAdd (z.toAdd : ℚ_[ℓ])) (map_mul χ.toMul g h)
      continuous_toFun := continuous_ofAdd.comp
        (continuous_subtype_val.comp (continuous_toAdd.comp χ.toMul.continuous)) }
  map_add' _ _ := ContinuousMonoidHom.ext fun _ => rfl
  map_smul' _ _ := ContinuousMonoidHom.ext fun _ => rfl

/-- Inclusion of integral continuous characters is injective. -/
theorem integralCharacterInclusion_injective :
    Function.Injective (integralCharacterInclusion ξ ℓ) := by
  intro χ ψ h
  apply ContinuousMonoidHom.ext
  intro g
  exact congrArg Multiplicative.ofAdd (PadicInt.ext
    (congrArg (fun η : rationalPadicCharacters ξ ℓ => (η.toMul g).toAdd) h))

private def integralMultiple (χ : rationalPadicCharacters ξ ℓ) (n : ℕ)
    (hn : ∀ g, ‖(ℓ : ℚ_[ℓ]) ^ n * (χ.toMul g).toAdd‖ ≤ 1) :
    padicCharacters ξ ℓ := Additive.ofMul
  { toFun := fun g => Multiplicative.ofAdd ⟨(ℓ : ℚ_[ℓ]) ^ n * (χ.toMul g).toAdd, hn g⟩
    map_one' := by
      apply congrArg Multiplicative.ofAdd
      apply PadicInt.ext
      exact (congrArg (fun z : Multiplicative ℚ_[ℓ] => (ℓ : ℚ_[ℓ]) ^ n * z.toAdd)
        (map_one χ.toMul)).trans (mul_zero _)
    map_mul' g h := by
      apply congrArg Multiplicative.ofAdd
      apply PadicInt.ext
      exact (congrArg (fun z : Multiplicative ℚ_[ℓ] => (ℓ : ℚ_[ℓ]) ^ n * z.toAdd)
        (map_mul χ.toMul g h)).trans (mul_add _ _ _)
    continuous_toFun := continuous_ofAdd.comp
      ((continuous_const.mul (continuous_toAdd.comp χ.toMul.continuous)).subtype_mk hn) }

/-- Every rational continuous character has a common integral denominator. -/
theorem rationalCharacter_has_integral_multiple (χ : rationalPadicCharacters ξ ℓ) :
    ∃ n : ℕ, ∃ ψ : padicCharacters ξ ℓ,
      ((ℓ : ℤ_[ℓ]) ^ n) • χ = integralCharacterInclusion ξ ℓ ψ := by
  obtain ⟨n, hn⟩ := LocalFieldTheory.exists_pow_mul_norm_le_one ℓ
    (fun g => (χ.toMul g).toAdd) (continuous_toAdd.comp χ.toMul.continuous)
  exact ⟨n, integralMultiple ξ ℓ χ n hn, ContinuousMonoidHom.ext fun _ => rfl⟩

/-- Rational continuous characters are the localization of integral continuous characters. -/
instance integralCharacterInclusion_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) (integralCharacterInclusion ξ ℓ) where
  map_units s := by
    rw [← (Algebra.lsmul ℤ_[ℓ] (A := ℚ_[ℓ]) ℤ_[ℓ]
      (rationalPadicCharacters ξ ℓ)).commutes]
    exact (IsLocalization.map_units ℚ_[ℓ] s).map _
  surj χ := by
    obtain ⟨n, ψ, hψ⟩ := rationalCharacter_has_integral_multiple ξ ℓ χ
    have hℓ : (ℓ : ℤ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
    exact ⟨(ψ, ⟨(ℓ : ℤ_[ℓ]) ^ n,
      mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hℓ)⟩), hψ⟩
  exists_of_eq h := by
    have h' := integralCharacterInclusion_injective ξ ℓ h
    exact ⟨1, congrArg (fun χ : padicCharacters ξ ℓ => (1 : ℤ_[ℓ]) • χ) h'⟩

/-- Scalar extension of integral characters is the module of actual rational continuous
characters; surjectivity follows from compactness, not an extra boundedness hypothesis. -/
def rationalCharacterTensorEquiv :
    TensorProduct ℤ_[ℓ] ℚ_[ℓ] (padicCharacters ξ ℓ) ≃ₗ[ℚ_[ℓ]]
      rationalPadicCharacters ξ ℓ :=
  (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ_[ℓ]) ℚ_[ℓ]
    (integralCharacterInclusion ξ ℓ)).equiv

/-- The tensor comparison sends a pure tensor to the corresponding scalar multiple
of the included integral character. -/
theorem rationalCharacterTensorEquiv_tmul (c : ℚ_[ℓ]) (χ : padicCharacters ξ ℓ) :
    rationalCharacterTensorEquiv ξ ℓ (c ⊗ₜ[ℤ_[ℓ]] χ) =
      c • integralCharacterInclusion ξ ℓ χ :=
  (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ_[ℓ]) ℚ_[ℓ]
    (integralCharacterInclusion ξ ℓ)).equiv_tmul c χ

/-- Rational characters of the actual closed-commutator quotient are exactly
the rational characters of the fundamental group. -/
def rationalAbelianCharacterEquiv :
    Additive (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
      Multiplicative ℚ_[ℓ]) ≃+ rationalPadicCharacters ξ ℓ where
  toFun χ := Additive.ofMul (χ.toMul.comp
    (ProCGroups.Abelian.TopologicalAbelianization.mkₜ _))
  invFun χ := Additive.ofMul (ProCGroups.Abelian.TopologicalAbelianization.lift χ.toMul)
  left_inv χ := by
    apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
    intro g
    rfl
  right_inv χ := ContinuousMonoidHom.ext fun _ => rfl
  map_add' χ ψ := ContinuousMonoidHom.ext fun _ => rfl

variable [ConnectedSpace X] [IsSepClosed Ω]

/-- Ordinary rational ℓ-adic H¹ of a connected scheme is its continuous Qℓ-valued
character module. No smoothness, properness, noetherian, or characteristic hypothesis is needed. -/
def rationalEllAdicH1CharacterEquiv :
    rationalEllAdicCohomology ℓ X 1 ≃ₗ[ℚ_[ℓ]] rationalPadicCharacters ξ ℓ :=
  (rationalEllAdicH1TensorCharacterEquiv ξ ℓ).trans (rationalCharacterTensorEquiv ξ ℓ)

/-- Ordinary rational ℓ-adic H¹ is the continuous rational character group of
the actual topological abelianization. This statement does not assert that
rational characters recover the torsion of that abelianization. -/
def rationalEllAdicH1AbelianCharacterEquiv :
    rationalEllAdicCohomology ℓ X 1 ≃+
      Additive (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
        Multiplicative ℚ_[ℓ]) :=
  (rationalEllAdicH1CharacterEquiv ξ ℓ).toAddEquiv.trans
    (rationalAbelianCharacterEquiv ξ ℓ).symm

end EtaleFundamentalGroups.Cohomology
