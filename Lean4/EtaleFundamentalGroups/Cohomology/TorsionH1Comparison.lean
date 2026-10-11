/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import EtaleFundamentalGroups.Cohomology.H1Character
import EtaleFundamentalGroups.Cohomology.H1CharacterPullback
import EtaleFundamentalGroups.Cohomology.FiniteTorsionPullback
import EtaleFundamentalGroups.GaloisCategories.FiberIso
import ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.Colimit.DirectLimit
import EtaleCohomology.Classical.FiniteTorsion
import ProCGroups.Abelian.ProfiniteBidual
import ProCGroups.ProC.Quotients.ClosedNormal

/-!
# Finite-torsion étale H¹ and the full abelian fundamental group

The direct limit of actual finite-coefficient étale H¹ is the discrete
Pontryagin character group of the actual topological abelianization.
Factorization through finite quotients proves surjectivity. Thus finite
torsion is retained, unlike a comparison using only rational ℓ-adic values.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical
open ProCGroups.ProC

universe u v

namespace EtaleFundamentalGroups.Cohomology

local instance coefficientTopology (n : ℕ) :
    TopologicalSpace (Multiplicative (finiteTorsionCoefficients.{u} n)) := ⊥
local instance coefficientDiscrete (n : ℕ) :
    DiscreteTopology (Multiplicative (finiteTorsionCoefficients.{u} n)) := ⟨rfl⟩

private def coefficientCircle (n : ℕ) :
    Multiplicative (finiteTorsionCoefficients.{u} n) →ₜ* Circle where
  toFun a := a.toAdd.down.toMul.val
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

private theorem coefficientCircle_injective (n : ℕ) :
    Function.Injective (coefficientCircle.{u} n) := by
  intro a b h
  apply congrArg Multiplicative.ofAdd
  apply ULift.ext
  exact congrArg Additive.ofMul (Subtype.ext h)

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private abbrev P := TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))

private instance : TotallyDisconnectedSpace (P ξ) :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (Subgroup.closedCommutator (Aut (FiniteEtale.fiber ξ)))
    (Subgroup.isClosed_closedCommutator _)

/-- The finite H¹ comparison followed by the actual inclusion into the circle. -/
def finiteTorsionStageCharacter (n : ℕ) :
    finiteTorsionLevel X 1 n →+ Additive (PontryaginDual (P ξ)) where
  toFun a := Additive.ofMul ((coefficientCircle n).comp
    (finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ a).toMul)
  map_zero' := by
    apply ContinuousMonoidHom.ext
    intro g
    change coefficientCircle n
      ((finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ 0).toMul g) = 1
    rw [map_zero]
    exact (coefficientCircle.{u} n).map_one
  map_add' a b := by
    apply ContinuousMonoidHom.ext
    intro g
    change coefficientCircle n
      ((finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ (a + b)).toMul g) = _
    exact (congrArg (fun χ : Additive (P ξ →ₜ*
      Multiplicative (finiteTorsionCoefficients n)) => coefficientCircle n (χ.toMul g))
        ((finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ).map_add a b)).trans
      ((coefficientCircle n).map_mul _ _)

private theorem stageCharacter_injective (n : ℕ) :
    Function.Injective (finiteTorsionStageCharacter ξ n) := by
  intro a b h
  apply (finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ).injective
  apply ContinuousMonoidHom.ext
  intro g
  apply coefficientCircle_injective n
  exact congrArg (fun χ : Additive (PontryaginDual (P ξ)) => χ.toMul g) h

private theorem stageCharacter_compatible (m n : ℕ) (h : m ≤ n)
    (a : finiteTorsionLevel X 1 m) :
    finiteTorsionStageCharacter ξ m a =
      finiteTorsionStageCharacter ξ n (finiteTorsionTransition X 1 m n h a) := by
  apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
  intro g
  change coefficientCircle m
    (h1AbelianCharacter (finiteTorsionCoefficients m) ξ a
      (ProCGroups.Abelian.TopologicalAbelianization.mk _ g)) =
    coefficientCircle n
      (h1AbelianCharacter (finiteTorsionCoefficients n) ξ
        (finiteTorsionTransition X 1 m n h a)
        (ProCGroups.Abelian.TopologicalAbelianization.mk _ g))
  exact (congrArg (coefficientCircle m)
    (h1AbelianCharacter_apply_mk (finiteTorsionCoefficients m) ξ a g)).trans
    ((congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ*
      Multiplicative (finiteTorsionCoefficients n) => coefficientCircle n (χ g))
        (finiteH1CharacterEquiv_naturality (finiteTorsionCoefficients m) ξ
          (AddCommGrpCat.ofHom (finiteTorsionInclusion m n h)) a)).trans
      (congrArg (coefficientCircle n)
        (h1AbelianCharacter_apply_mk (finiteTorsionCoefficients n) ξ
          (finiteTorsionTransition X 1 m n h a) g)).symm)

private def directLimitAddHom (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (f : ∀ m n, m ≤ n → G m →+ G n) [DirectedSystem G (f · · ·)]
    {A : Type v} [AddCommGroup A] (g : ∀ n, G n →+ A)
    (h : ∀ m n h a, g m a = g n (f m n h a)) : DirectLimit G f →+ A where
  toFun := DirectLimit.lift f (fun n => g n) h
  map_zero' := DirectLimit.lift_zero g h
  map_add' := DirectLimit.lift_add g h

/-- The character of a finite-coefficient direct-limit étale H¹ class. -/
def finiteTorsionH1Character :
    finiteTorsionCohomology X 1 →+ Additive (PontryaginDual (P ξ)) :=
  directLimitAddHom (fun n => finiteTorsionLevel X 1 n) (finiteTorsionTransition X 1)
    (finiteTorsionStageCharacter ξ) (stageCharacter_compatible ξ)

/-- The character comparison on the direct limit is injective. -/
theorem finiteTorsionH1Character_injective :
    Function.Injective (finiteTorsionH1Character ξ) :=
  DirectLimit.lift_injective (finiteTorsionTransition X 1)
    (fun n => finiteTorsionStageCharacter ξ n) (stageCharacter_compatible ξ)
    (stageCharacter_injective ξ)

private def quotientCoefficientCharacter (χ : PontryaginDual (P ξ))
    (U : OpenNormalSubgroup (P ξ)) (hU : (U : Subgroup (P ξ)) ≤ χ.toMonoidHom.ker) :
    (P ξ ⧸ (U : Subgroup (P ξ))) →ₜ*
      Multiplicative (finiteTorsionCoefficients.{u} (Nat.card (P ξ ⧸ (U : Subgroup (P ξ))))) := by
  let Q := P ξ ⧸ (U : Subgroup (P ξ))
  let χQ : PontryaginDual Q := ProCGroups.QuotientGroup.liftₜ (U : Subgroup (P ξ)) χ hU
  have hp (q : Q) : χQ q ∈ factorialRoots (Nat.card Q) := by
    change (χQ q) ^ Nat.factorial (Nat.card Q + 1) = 1
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.card_pos (α := Q)) (Nat.le_succ (Nat.card Q))
    rw [hk, pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]
  exact
    { toFun := fun q => Multiplicative.ofAdd (ULift.up (Additive.ofMul ⟨χQ q, hp q⟩))
      map_one' := congrArg (fun z : factorialRoots (Nat.card Q) =>
        Multiplicative.ofAdd (ULift.up (Additive.ofMul z))) (Subtype.ext (map_one χQ))
      map_mul' q r := congrArg (fun z : factorialRoots (Nat.card Q) =>
        Multiplicative.ofAdd (ULift.up (Additive.ofMul z))) (Subtype.ext (map_mul χQ q r))
      continuous_toFun := continuous_of_discreteTopology }

/-- Every circle character comes from actual finite-coefficient étale H¹. -/
theorem finiteTorsionH1Character_surjective :
    Function.Surjective (finiteTorsionH1Character ξ) := by
  intro χ
  obtain ⟨U, hU⟩ := ProCGroups.Duality.exists_openNormal_le_character_ker χ.toMul
  let n := Nat.card (P ξ ⧸ (U : Subgroup (P ξ)))
  let ψ := (quotientCoefficientCharacter ξ χ.toMul U hU).comp
    (OpenNormalSubgroup.quotientProj U)
  let a := (finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ).symm
    (Additive.ofMul ψ)
  refine ⟨finiteTorsionClass X 1 n a, ?_⟩
  change Additive.ofMul ((coefficientCircle n).comp
    (finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ a).toMul) = χ
  rw [show finiteH1AbelianCharacterEquiv (finiteTorsionCoefficients n) ξ a =
    Additive.ofMul ψ from (finiteH1AbelianCharacterEquiv _ ξ).apply_symm_apply _]
  exact ContinuousMonoidHom.ext fun _ => rfl

/-- Actual finite-torsion étale H¹ is the full character group of the actual
topological abelianization, including torsion characters. -/
def finiteTorsionH1CharacterEquiv :
    finiteTorsionCohomology X 1 ≃+ Additive (PontryaginDual (P ξ)) :=
  AddEquiv.ofBijective (finiteTorsionH1Character ξ)
    ⟨finiteTorsionH1Character_injective ξ, finiteTorsionH1Character_surjective ξ⟩


/-- Base-point transport preserves the monodromy pairing on the actual
finite-coefficient direct limit. This uses finite-level derived H¹, not
cohomology of an infinite constant sheaf. -/
theorem finiteTorsionH1Character_basePoint
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (η : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber η)
    (a : finiteTorsionCohomology X 1) :
    (finiteTorsionH1Character η a).toMul.comp
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (ContinuousMonoidHom.toContinuousMonoidHom
            (PreGaloisCategory.continuousConjAut τ))) =
      (finiteTorsionH1Character ξ a).toMul := by
  apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
  intro g
  induction a using DirectLimit.induction with
  | _ n a =>
    change coefficientCircle n
        (h1AbelianCharacter (finiteTorsionCoefficients n) η a
          (ProCGroups.Abelian.TopologicalAbelianization.mk _
            (PreGaloisCategory.continuousConjAut τ g))) =
      coefficientCircle n
        (h1AbelianCharacter (finiteTorsionCoefficients n) ξ a
          (ProCGroups.Abelian.TopologicalAbelianization.mk _ g))
    exact (congrArg (coefficientCircle n)
      (h1AbelianCharacter_apply_mk (finiteTorsionCoefficients n) η a
        (PreGaloisCategory.continuousConjAut τ g))).trans
      ((congrArg (coefficientCircle n)
        (congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ*
          Multiplicative (finiteTorsionCoefficients n) => χ g)
          (h1Character_basePoint (finiteTorsionCoefficients n) ξ η τ a))).trans
        (congrArg (coefficientCircle n)
          (h1AbelianCharacter_apply_mk (finiteTorsionCoefficients n) ξ a g)).symm)


/-- Geometric inverse image of the actual finite-coefficient direct limit is
dual to the actual induced map on topological abelianizations. -/
theorem finiteTorsionH1Character_schemePullback
    {Y : Scheme.{u}} [ConnectedSpace Y] (f : X ⟶ Y)
    (a : finiteTorsionCohomology Y 1) :
    (finiteTorsionH1Character ξ (finiteTorsionCohomologyPullback f 1 a)).toMul =
      (finiteTorsionH1Character (ξ ≫ f) a).toMul.comp
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (FiniteEtale.fundamentalGroupHom f ξ)) := by
  apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
  intro g
  induction a using DirectLimit.induction with
  | _ n a =>
    change coefficientCircle n
        (h1AbelianCharacter (finiteTorsionCoefficients n) ξ
          (constantCohomologyPullback f (finiteTorsionCoefficients n) 1 a)
          (ProCGroups.Abelian.TopologicalAbelianization.mk _ g)) =
      coefficientCircle n
        (h1AbelianCharacter (finiteTorsionCoefficients n) (ξ ≫ f) a
          (ProCGroups.Abelian.TopologicalAbelianization.mk _
            (FiniteEtale.fundamentalGroupHom f ξ g)))
    exact (congrArg (coefficientCircle n)
      (h1AbelianCharacter_apply_mk (finiteTorsionCoefficients n) ξ
        (constantCohomologyPullback f (finiteTorsionCoefficients n) 1 a) g)).trans
      ((congrArg (coefficientCircle n)
        (congrArg
          (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ*
            Multiplicative (finiteTorsionCoefficients n) => χ g)
          (h1Character_schemePullback f (finiteTorsionCoefficients n) ξ a).symm)).trans
        (congrArg (coefficientCircle n)
          (h1AbelianCharacter_apply_mk (finiteTorsionCoefficients n) (ξ ≫ f) a
            (FiniteEtale.fundamentalGroupHom f ξ g))).symm)

end EtaleFundamentalGroups.Cohomology
