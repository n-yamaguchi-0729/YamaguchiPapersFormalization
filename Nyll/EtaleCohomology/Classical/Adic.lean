/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Nyll.EtaleCohomology.Classical.SequentialLimit

/-!
# Classical ℓ-adic cohomology on the ordinary étale site

The finite levels are the existing derived cohomology of the constant
`ℤ/ℓ^(n+1)ℤ` sheaves on the small étale site. Coefficient reduction gives the
transition maps. Classical integral ℓ-adic cohomology is the group of compatible
families, that is, the inverse limit of these actual finite-level groups.

This construction uses no pro-étale site. It does not identify an inverse limit
of cohomology groups with the cohomology of a derived inverse limit; any such
comparison needs its own hypotheses and proof.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology.Classical

/-- The finite cyclic coefficient group, lifted to the scheme universe. -/
abbrev ellPowerCoefficients (ℓ n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))

/-- Reduction between consecutive finite coefficient groups. -/
def ellPowerReduction (ℓ n : ℕ) :
    ellPowerCoefficients.{u} ℓ (n + 1) →+ ellPowerCoefficients.{u} ℓ n where
  toFun a := ULift.up
    (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1))) a.down)
  map_zero' := congrArg ULift.up (map_zero _)
  map_add' a b := congrArg ULift.up (map_add _ a.down b.down)

/-- Ordinary étale cohomology with finite cyclic constant coefficients, bundled
with its original additive-group structure once at each level. -/
def finiteLevelCohomology (X : Scheme.{u}) (ℓ n i : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (ellPowerCoefficients ℓ n)) i)

/-- The cohomological transition is induced by actual coefficient reduction. -/
def finiteLevelReduction (X : Scheme.{u}) (ℓ n i : ℕ) :
    finiteLevelCohomology X ℓ (n + 1) i →+ finiteLevelCohomology X ℓ n i :=
  Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom (ellPowerReduction ℓ n))) i

/-- The inverse limit subgroup of the finite-level cohomology groups. -/
def compatibleCohomology (X : Scheme.{u}) (ℓ i : ℕ) :
    AddSubgroup (∀ n : ℕ, finiteLevelCohomology X ℓ n i) :=
  sequentialLimit (fun n => finiteLevelCohomology X ℓ n i)
    (fun n => finiteLevelReduction X ℓ n i)

/-- Classical integral ℓ-adic cohomology: the inverse limit of ordinary
étale cohomology with coefficients `ℤ/ℓ^(n+1)ℤ`. No geometric finiteness
hypothesis is imposed merely to define this group. -/
abbrev ellAdicCohomology (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) : Type u :=
  compatibleCohomology X ℓ i

/-- Evaluation at a finite level is an additive homomorphism. -/
def ellAdicProjection (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (i n : ℕ) :
    ellAdicCohomology X ℓ i →+ finiteLevelCohomology X ℓ n i :=
  sequentialLimitProjection (fun n => finiteLevelCohomology X ℓ n i)
    (fun n => finiteLevelReduction X ℓ n i) n

/-- Finite-level projections satisfy the original cohomological transitions. -/
theorem ellAdicProjection_compatible (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (i n : ℕ) (a : ellAdicCohomology X ℓ i) :
    finiteLevelReduction X ℓ n i (ellAdicProjection X ℓ i (n + 1) a) =
      ellAdicProjection X ℓ i n a :=
  a.property n

/-- Equality in classical ℓ-adic cohomology is detected at every finite level. -/
theorem ellAdicCohomology_ext (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (i : ℕ) {a b : ellAdicCohomology X ℓ i}
    (h : ∀ n, ellAdicProjection X ℓ i n a = ellAdicProjection X ℓ i n b) : a = b :=
  Subtype.ext (funext h)

end EtaleCohomology.Classical
