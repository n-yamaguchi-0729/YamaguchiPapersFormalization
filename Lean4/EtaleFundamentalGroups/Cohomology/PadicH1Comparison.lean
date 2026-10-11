/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.AdicH1Comparison
import ProCGroups.Abelian.TopologicalAbelianization
import ValuedFieldTheory.LocalField.Padic.ResidueInverseLimit
import Mathlib.Topology.Constructions

/-!
# Classical integral ℓ-adic H¹ and p-adic continuous characters

Compatible finite characters determine actual p-adic integers, whose topology
is detected by reduction at every level. Consequently their pointwise limit
is continuous. Combined with the finite-coefficient étale H¹ comparison this
identifies classical integral ℓ-adic H¹ with continuous p-adic characters of
the actual étale fundamental group. Connectedness and a geometric point are
the only geometric assumptions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical
open LocalFieldTheory.PadicResidues
open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)
  (ℓ : ℕ) [Fact ℓ.Prime]

local instance finiteCoefficientTopology (n : ℕ) :
    TopologicalSpace (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⊥
local instance finiteCoefficientDiscrete (n : ℕ) :
    DiscreteTopology (Multiplicative (ellPowerCoefficients.{u} ℓ n)) := ⟨rfl⟩
local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod (ℓ ^ n)) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod (ℓ ^ n)) := ⟨rfl⟩

/-- Continuous characters into the actual additive p-adic integers. -/
abbrev padicCharacters : Type (u + 1) :=
  Additive (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative ℤ_[ℓ])

private def characterResidues (χ : compatibleFiniteCharacters ξ ℓ)
    (g : Aut (FiniteEtale.fiber ξ)) : compatibleResidues ℓ := by
  let a : ∀ n : ℕ, ZMod (ℓ ^ n)
    | 0 => 0
    | n + 1 => ((χ.val n).toMul g).toAdd.down
  refine ⟨a, compatibleResidues_of_adjacent ℓ a ?_⟩
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
    exact Subsingleton.elim _ _
  | succ n =>
    exact congrArg (fun ψ : finiteLevelCharacters ξ ℓ n => (ψ.toMul g).toAdd.down)
      (χ.property n)

private def characterLimit (χ : compatibleFiniteCharacters ξ ℓ)
    (g : Aut (FiniteEtale.fiber ξ)) : ℤ_[ℓ] :=
  residueLimit ℓ (characterResidues ξ ℓ χ g)

private theorem characterLimit_spec (χ : compatibleFiniteCharacters ξ ℓ)
    (g : Aut (FiniteEtale.fiber ξ)) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (characterLimit ξ ℓ χ g) =
      ((χ.val n).toMul g).toAdd.down :=
  residueLimit_spec ℓ (characterResidues ξ ℓ χ g) (n + 1)

private theorem padic_ext_positive {a b : ℤ_[ℓ]}
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
    exact Subsingleton.elim _ _
  | succ n => exact h n

private theorem characterLimit_mul (χ : compatibleFiniteCharacters ξ ℓ)
    (g h : Aut (FiniteEtale.fiber ξ)) :
    characterLimit ξ ℓ χ (g * h) = characterLimit ξ ℓ χ g + characterLimit ξ ℓ χ h := by
  apply padic_ext_positive ℓ
  intro n
  rw [map_add, characterLimit_spec, characterLimit_spec, characterLimit_spec]
  exact congrArg (fun z : Multiplicative (ellPowerCoefficients ℓ n) => z.toAdd.down)
    ((χ.val n).toMul.map_mul g h)

private theorem characterLimit_one (χ : compatibleFiniteCharacters ξ ℓ) :
    characterLimit ξ ℓ χ 1 = 0 := by
  apply padic_ext_positive ℓ
  intro n
  rw [map_zero, characterLimit_spec]
  exact congrArg (fun z : Multiplicative (ellPowerCoefficients ℓ n) => z.toAdd.down)
    (χ.val n).toMul.map_one

private theorem continuous_characterLimit (χ : compatibleFiniteCharacters ξ ℓ) :
    Continuous (characterLimit ξ ℓ χ) := by
  apply (continuous_iff_residues ℓ _).mpr
  intro n
  cases n with
  | zero =>
    have he : (fun g => PadicInt.toZModPow 0 (characterLimit ξ ℓ χ g)) =
        (fun _ : Aut (FiniteEtale.fiber ξ) => (0 : ZMod (ℓ ^ 0))) :=
      funext fun _ => by
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    rw [he]
    exact continuous_const
  | succ n =>
    have he := funext fun g => characterLimit_spec ξ ℓ χ g n
    rw [he]
    exact (continuous_of_discreteTopology : Continuous
      (fun z : Multiplicative (ellPowerCoefficients ℓ n) => z.toAdd.down)).comp
        (χ.val n).toMul.continuous

/-- The continuous p-adic character obtained by taking actual residue limits. -/
def compatibleCharacterLimit (χ : compatibleFiniteCharacters ξ ℓ) : padicCharacters ξ ℓ :=
  Additive.ofMul
    { toFun := fun g => Multiplicative.ofAdd (characterLimit ξ ℓ χ g)
      map_one' := congrArg Multiplicative.ofAdd (characterLimit_one ξ ℓ χ)
      map_mul' g h := congrArg Multiplicative.ofAdd (characterLimit_mul ξ ℓ χ g h)
      continuous_toFun := continuous_ofAdd.comp
        (continuous_characterLimit ξ ℓ χ) }

/-- Reduction of a continuous p-adic character at a positive finite level. -/
def padicCharacterReduction (n : ℕ) (χ : padicCharacters ξ ℓ) :
    finiteLevelCharacters ξ ℓ n := by
  refine Additive.ofMul
    { toFun := fun g => Multiplicative.ofAdd (ULift.up
        (PadicInt.toZModPow (n + 1) (χ.toMul g).toAdd))
      map_one' := ?_
      map_mul' := ?_
      continuous_toFun := ?_ }
  · exact (congrArg (fun z : Multiplicative ℤ_[ℓ] => Multiplicative.ofAdd
      (ULift.up (PadicInt.toZModPow (n + 1) z.toAdd))) (map_one χ.toMul)).trans
        (congrArg (fun z => Multiplicative.ofAdd (ULift.up z))
          (PadicInt.toZModPow (n + 1)).map_zero)
  · intro g h
    exact (congrArg (fun z : Multiplicative ℤ_[ℓ] => Multiplicative.ofAdd
      (ULift.up (PadicInt.toZModPow (n + 1) z.toAdd))) (map_mul χ.toMul g h)).trans
        (congrArg (fun z => Multiplicative.ofAdd (ULift.up z))
          ((PadicInt.toZModPow (n + 1)).map_add (χ.toMul g).toAdd (χ.toMul h).toAdd))
  · exact (continuous_of_discreteTopology : Continuous (fun z : ZMod (ℓ ^ (n + 1)) =>
      Multiplicative.ofAdd (ULift.up.{u} z))).comp
        ((continuous_padicIntToZModPow ℓ (n + 1)).comp
          (continuous_toAdd.comp χ.toMul.continuous))

/-- Simultaneous finite reductions of a p-adic character, as an additive homomorphism. -/
def padicCharacterResidues : padicCharacters ξ ℓ →+ compatibleFiniteCharacters ξ ℓ where
  toFun χ := ⟨fun n => padicCharacterReduction ξ ℓ n χ, fun n => by
    apply ContinuousMonoidHom.ext
    intro g
    exact congrArg (fun z => Multiplicative.ofAdd (ULift.up.{u} z))
      (congrArg (fun f : ℤ_[ℓ] →+* ZMod (ℓ ^ (n + 1)) => f (χ.toMul g).toAdd)
        (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1))))⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    apply ContinuousMonoidHom.ext
    intro g
    exact congrArg (fun z => Multiplicative.ofAdd (ULift.up.{u} z))
      (PadicInt.toZModPow (n + 1)).map_zero
  map_add' χ ψ := by
    apply Subtype.ext
    funext n
    apply ContinuousMonoidHom.ext
    intro g
    exact congrArg (fun z => Multiplicative.ofAdd (ULift.up.{u} z))
      ((PadicInt.toZModPow (n + 1)).map_add (χ.toMul g).toAdd (ψ.toMul g).toAdd)

private theorem padicCharacterResidues_injective :
    Function.Injective (padicCharacterResidues ξ ℓ) := by
  intro χ ψ h
  apply ContinuousMonoidHom.ext
  intro g
  apply congrArg Multiplicative.ofAdd
  apply padic_ext_positive ℓ
  intro n
  exact congrArg (fun a : compatibleFiniteCharacters ξ ℓ =>
    ((a.val n).toMul g).toAdd.down) h

private theorem padicCharacterResidues_limit (χ : compatibleFiniteCharacters ξ ℓ) :
    padicCharacterResidues ξ ℓ (compatibleCharacterLimit ξ ℓ χ) = χ := by
  apply Subtype.ext
  funext n
  apply ContinuousMonoidHom.ext
  intro g
  exact congrArg (fun z => Multiplicative.ofAdd (ULift.up.{u} z))
    (characterLimit_spec ξ ℓ χ g n)

/-- Actual continuous p-adic characters are exactly compatible finite characters. -/
def padicCompatibleCharacterEquiv :
    padicCharacters ξ ℓ ≃+ compatibleFiniteCharacters ξ ℓ :=
  AddEquiv.ofBijective (padicCharacterResidues ξ ℓ)
    ⟨padicCharacterResidues_injective ξ ℓ, fun χ =>
      ⟨compatibleCharacterLimit ξ ℓ χ, padicCharacterResidues_limit ξ ℓ χ⟩⟩

/-- Classical integral ℓ-adic H¹ of any connected scheme is the additive group
of continuous ℤℓ-valued characters of its étale fundamental group. -/
def ellAdicH1PadicCharacterEquiv [ConnectedSpace X] [IsSepClosed Ω] :
    ellAdicCohomology X ℓ 1 ≃+ padicCharacters ξ ℓ :=
  (ellAdicH1CompatibleCharacterEquiv ξ ℓ).trans (padicCompatibleCharacterEquiv ξ ℓ).symm

/-- Restriction along the closed-commutator quotient identifies p-adic characters
of the actual topological abelianization with fundamental-group characters. -/
def padicAbelianCharacterEquiv :
    Additive (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
      Multiplicative ℤ_[ℓ]) ≃+ padicCharacters ξ ℓ where
  toFun χ := Additive.ofMul (χ.toMul.comp
    (ProCGroups.Abelian.TopologicalAbelianization.mkₜ _))
  invFun χ := Additive.ofMul (ProCGroups.Abelian.TopologicalAbelianization.lift χ.toMul)
  left_inv χ := by
    apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
    intro g
    rfl
  right_inv χ := ContinuousMonoidHom.ext fun _ => rfl
  map_add' χ ψ := ContinuousMonoidHom.ext fun _ => rfl

/-- Classical integral ℓ-adic H¹ is the group of continuous p-adic characters
of the fundamental group's quotient by its closed commutator subgroup. -/
def ellAdicH1AbelianPadicCharacterEquiv [ConnectedSpace X] [IsSepClosed Ω] :
    ellAdicCohomology X ℓ 1 ≃+
      Additive (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
        Multiplicative ℤ_[ℓ]) :=
  (ellAdicH1PadicCharacterEquiv ξ ℓ).trans (padicAbelianCharacterEquiv ξ ℓ).symm

end EtaleFundamentalGroups.Cohomology
