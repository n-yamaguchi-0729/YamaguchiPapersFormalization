/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
import Nyll.EtaleCohomology.Classical.FiniteTorsion
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Actual pullback on finite-coefficient direct-limit cohomology

The map is induced level by level by the derived cohomology inverse image.
Compatibility with the original finite coefficient inclusions follows from
coefficient naturality, independently of fundamental-group characters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (i : ℕ)

private def finiteTorsionStagePullback (n : ℕ) :
    finiteTorsionLevel Y i n →+ finiteTorsionCohomology X i :=
  (finiteTorsionClass X i n).comp
    (constantCohomologyPullback f (finiteTorsionCoefficients n) i)

private theorem finiteTorsionStagePullback_compatible (m n : ℕ) (h : m ≤ n)
    (a : finiteTorsionLevel Y i m) :
    finiteTorsionStagePullback f i m a =
      finiteTorsionStagePullback f i n (finiteTorsionTransition Y i m n h a) := by
  have hn := constantCohomologyPullback_naturality f
    (finiteTorsionCoefficients m) (finiteTorsionCoefficients n)
    (AddCommGrpCat.ofHom (finiteTorsionInclusion m n h)) i a
  change finiteTorsionTransition X i m n h
      (constantCohomologyPullback f (finiteTorsionCoefficients m) i a) =
    constantCohomologyPullback f (finiteTorsionCoefficients n) i
      (finiteTorsionTransition Y i m n h a) at hn
  change finiteTorsionClass X i m
      (constantCohomologyPullback f (finiteTorsionCoefficients m) i a) =
    finiteTorsionClass X i n
      (constantCohomologyPullback f (finiteTorsionCoefficients n) i
        (finiteTorsionTransition Y i m n h a))
  rw [← hn]
  exact DirectLimit.eq_of_le (F := fun n => finiteTorsionLevel X i n)
    (f := finiteTorsionTransition X i)
    ⟨m, constantCohomologyPullback f (finiteTorsionCoefficients m) i a⟩ n h

/-- Inverse image on the direct limit of actual finite-coefficient cohomology. -/
def finiteTorsionCohomologyPullback :
    finiteTorsionCohomology Y i →+ finiteTorsionCohomology X i where
  toFun := DirectLimit.lift (finiteTorsionTransition Y i)
    (fun n => finiteTorsionStagePullback f i n)
    (finiteTorsionStagePullback_compatible f i)
  map_zero' := DirectLimit.lift_zero (fun n => finiteTorsionStagePullback f i n)
    (finiteTorsionStagePullback_compatible f i)
  map_add' := DirectLimit.lift_add (fun n => finiteTorsionStagePullback f i n)
    (finiteTorsionStagePullback_compatible f i)

/-- On an original finite stage, this is exactly the derived cohomology pullback. -/
theorem finiteTorsionCohomologyPullback_class (n : ℕ) (a : finiteTorsionLevel Y i n) :
    finiteTorsionCohomologyPullback f i (finiteTorsionClass Y i n a) =
      finiteTorsionClass X i n
        (constantCohomologyPullback f (finiteTorsionCoefficients n) i a) := rfl

end EtaleFundamentalGroups.Cohomology
