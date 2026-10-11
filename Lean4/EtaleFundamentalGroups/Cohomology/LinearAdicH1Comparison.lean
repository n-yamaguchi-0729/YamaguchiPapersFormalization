/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.PadicH1Comparison
import EtaleCohomology.Classical.RationalAdic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Linearity of the classical integral ℓ-adic H¹ comparison

The character group carries pointwise p-adic scalar multiplication. The
comparison respects this actual action because finite-coefficient H¹ is
natural for the scalar endomorphisms of its constant coefficient sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]
  (ξ : Spec (.of Ω) ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]

private def scalePadicCharacter (c : ℤ_[ℓ]) (χ : padicCharacters ξ ℓ) :
    padicCharacters ξ ℓ := Additive.ofMul
  { toFun := fun g => Multiplicative.ofAdd (c * (χ.toMul g).toAdd)
    map_one' := (congrArg (fun z : Multiplicative ℤ_[ℓ] =>
      Multiplicative.ofAdd (c * z.toAdd)) (map_one χ.toMul)).trans
        (congrArg Multiplicative.ofAdd (mul_zero c))
    map_mul' g h := (congrArg (fun z : Multiplicative ℤ_[ℓ] =>
      Multiplicative.ofAdd (c * z.toAdd)) (map_mul χ.toMul g h)).trans
        (congrArg Multiplicative.ofAdd (mul_add c (χ.toMul g).toAdd (χ.toMul h).toAdd))
    continuous_toFun := continuous_ofAdd.comp
      (continuous_const.mul (continuous_toAdd.comp χ.toMul.continuous)) }

/-- The canonical p-adic module structure on characters is pointwise multiplication. -/
instance padicCharactersModule : Module ℤ_[ℓ] (padicCharacters ξ ℓ) where
  smul := scalePadicCharacter ξ ℓ
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

/-- The scalar action on characters agrees with multiplication of their values. -/
theorem padicCharacters_smul_apply (c : ℤ_[ℓ]) (χ : padicCharacters ξ ℓ)
    (g : Aut (FiniteEtale.fiber ξ)) :
    ((c • χ).toMul g).toAdd = c * (χ.toMul g).toAdd := rfl

variable [ConnectedSpace X] [IsSepClosed Ω]

attribute [local instance] finiteCoefficientTopology finiteCoefficientDiscrete

private theorem finiteComparison_smul (n : ℕ) (c : ℤ_[ℓ])
    (a : finiteLevelCohomology X ℓ n 1) (g : Aut (FiniteEtale.fiber ξ)) :
    ((finiteH1CharacterEquiv (ellPowerCoefficients ℓ n) ξ (c • a)).toMul g).toAdd.down =
      PadicInt.toZModPow (n + 1) c *
        ((finiteH1CharacterEquiv (ellPowerCoefficients ℓ n) ξ a).toMul g).toAdd.down := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
  have h := finiteH1CharacterEquiv_naturality (ellPowerCoefficients ℓ n) ξ
    (AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients ℓ n) c)) a
  exact (congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ*
    Multiplicative (ellPowerCoefficients ℓ n) => (χ g).toAdd.down) h).symm

/-- Reduction of the integral comparison is the original finite-coefficient comparison. -/
theorem ellAdicH1PadicCharacterEquiv_reduction (a : ellAdicCohomology X ℓ 1)
    (n : ℕ) (g : Aut (FiniteEtale.fiber ξ)) :
    PadicInt.toZModPow (n + 1) ((ellAdicH1PadicCharacterEquiv ξ ℓ a).toMul g).toAdd =
      ((finiteH1CharacterEquiv (ellPowerCoefficients ℓ n) ξ (a.val n)).toMul g).toAdd.down := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact congrArg (fun χ : compatibleFiniteCharacters ξ ℓ =>
    ((χ.val n).toMul g).toAdd.down)
      ((padicCompatibleCharacterEquiv ξ ℓ).apply_symm_apply
        (ellAdicH1CompatibleCharacterEquiv ξ ℓ a))

/-- The integral H¹ comparison respects the actual coefficient-induced p-adic action. -/
theorem ellAdicH1PadicCharacterEquiv_smul (c : ℤ_[ℓ]) (a : ellAdicCohomology X ℓ 1) :
    ellAdicH1PadicCharacterEquiv ξ ℓ (c • a) = c • ellAdicH1PadicCharacterEquiv ξ ℓ a := by
  apply ContinuousMonoidHom.ext
  intro g
  have he : ((ellAdicH1PadicCharacterEquiv ξ ℓ (c • a)).toMul g).toAdd =
      c * ((ellAdicH1PadicCharacterEquiv ξ ℓ a).toMul g).toAdd := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
    | succ n =>
      exact (ellAdicH1PadicCharacterEquiv_reduction ξ ℓ (c • a) n g).trans
        ((finiteComparison_smul ξ ℓ n c (a.val n) g).trans
          ((congrArg (PadicInt.toZModPow (n + 1) c * ·)
            (ellAdicH1PadicCharacterEquiv_reduction ξ ℓ a n g).symm).trans
              ((PadicInt.toZModPow (n + 1)).map_mul c
                ((ellAdicH1PadicCharacterEquiv ξ ℓ a).toMul g).toAdd).symm))
  exact congrArg Multiplicative.ofAdd he

/-- Classical integral ℓ-adic H¹ and continuous p-adic characters are canonically
isomorphic as modules over the actual p-adic integer ring. -/
def ellAdicH1PadicCharacterLinearEquiv :
    ellAdicCohomology X ℓ 1 ≃ₗ[ℤ_[ℓ]] padicCharacters ξ ℓ where
  __ := ellAdicH1PadicCharacterEquiv ξ ℓ
  map_smul' := ellAdicH1PadicCharacterEquiv_smul ξ ℓ

/-- Rational classical H¹ is the scalar extension of the actual integral
continuous character module. This does not discard integral torsion in order
to claim reconstruction of the full profinite abelianization. -/
def rationalEllAdicH1TensorCharacterEquiv :
    rationalEllAdicCohomology ℓ X 1 ≃ₗ[ℚ_[ℓ]]
      TensorProduct ℤ_[ℓ] ℚ_[ℓ] (padicCharacters ξ ℓ) :=
  (ellAdicH1PadicCharacterLinearEquiv ξ ℓ).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (ellAdicCohomology X ℓ 1) (padicCharacters ξ ℓ)

end EtaleFundamentalGroups.Cohomology
