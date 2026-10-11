/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.Adic
import EtaleCohomology.Classical.AdditiveCoefficientAction
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Rational classical ℓ-adic cohomology

The actual finite coefficients carry the action of `ℤ_[ℓ]` by reduction.
This induces actions on their ordinary étale cohomology groups. The transition
maps are linear, so the inverse limit carries the same scalar action.
Rational coefficients are then obtained by tensoring with `ℚ_[ℓ]` over `ℤ_[ℓ]`.

This is the classical inverse-limit and scalar-extension construction, not
cohomology of a discrete constant `ℚ_[ℓ]` sheaf or of a pro-étale site.
See Stacks Project, Section 64.18, https://stacks.math.columbia.edu/tag/03UL.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology.Classical

private def linearSequentialLimit (R : Type*) [Semiring R]
    (M : ℕ → Type u) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (r : ∀ n, M (n + 1) →ₗ[R] M n) : Submodule R (∀ n, M n) where
  carrier := {a | ∀ n, r n (a (n + 1)) = a n}
  zero_mem' := fun n => map_zero (r n)
  add_mem' ha hb n := (map_add (r n) _ _).trans (congrArg₂ (· + ·) (ha n) (hb n))
  smul_mem' c _ ha n := (map_smul (r n) c _).trans (congrArg (c • ·) (ha n))

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Finite coefficients retain the scalar action given by the actual reduction
map from the ℓ-adic integers. -/
abbrev ellPowerPadicModule (n : ℕ) : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) :=
  Module.compHom (ellPowerCoefficients.{u} ℓ n) (PadicInt.toZModPow (n + 1))

private theorem ellPowerReduction_smul (n : ℕ) (c : ℤ_[ℓ])
    (a : ellPowerCoefficients.{u} ℓ (n + 1)) :
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ (n + 1)) := ellPowerPadicModule ℓ (n + 1)
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
    ellPowerReduction ℓ n (c • a) = c • ellPowerReduction ℓ n a := by
  change ULift.up ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
      (ZMod (ℓ ^ (n + 1)))) (PadicInt.toZModPow (n + 2) c * a.down)) =
    ULift.up (PadicInt.toZModPow (n + 1) c * (ellPowerReduction ℓ n a).down)
  apply congrArg ULift.up
  rw [map_mul]
  exact congrArg (fun b => b * (ellPowerReduction ℓ n a).down)
    (congrArg (fun f : ℤ_[ℓ] →+* ZMod (ℓ ^ (n + 1)) => f c)
      (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1))))

/-- The coefficient action on the actual finite-level derived étale cohomology. -/
instance finiteLevelPadicModule (X : Scheme.{u}) (n i : ℕ) :
    Module ℤ_[ℓ] (finiteLevelCohomology X ℓ n i) :=
  let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
  additiveCoefficientModule
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      Sheaf.functorH X.smallEtaleTopology i) ℤ_[ℓ] (ellPowerCoefficients ℓ n)

/-- The original finite-level transition is linear over the ℓ-adic integers. -/
def finiteLevelReductionLinear (X : Scheme.{u}) (n i : ℕ) :
    finiteLevelCohomology X ℓ (n + 1) i →ₗ[ℤ_[ℓ]] finiteLevelCohomology X ℓ n i where
  toAddHom := finiteLevelReduction X ℓ n i
  map_smul' c a := by
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ (n + 1)) := ellPowerPadicModule ℓ (n + 1)
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
    exact additiveCoefficient_map_smul
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        Sheaf.functorH X.smallEtaleTopology i) ℤ_[ℓ]
      (ellPowerCoefficients ℓ (n + 1)) (ellPowerCoefficients ℓ n)
      (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) (ellPowerReduction_smul ℓ n) c a

/-- The inverse limit carries the scalar action induced at every finite level. -/
instance ellAdicModule (X : Scheme.{u}) (i : ℕ) :
    Module ℤ_[ℓ] (ellAdicCohomology X ℓ i) :=
  inferInstanceAs (Module ℤ_[ℓ]
    (linearSequentialLimit ℤ_[ℓ] (fun n => finiteLevelCohomology X ℓ n i)
      (fun n => finiteLevelReductionLinear ℓ X n i)))

/-- Classical rational ℓ-adic cohomology, obtained from the integral inverse
limit by scalar extension to the field of ℓ-adic numbers. -/
def rationalEllAdicCohomology (X : Scheme.{u}) (i : ℕ) : ModuleCat.{u} ℚ_[ℓ] :=
  ModuleCat.of ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (ellAdicCohomology X ℓ i))

end EtaleCohomology.Classical
