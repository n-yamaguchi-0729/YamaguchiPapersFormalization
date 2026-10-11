/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Compatible families in a sequence of abelian groups

The inverse limit is a subgroup of the product. Keeping its group operations
independent of the concrete Ext groups avoids unfolding cohomology constructions
when checking the elementary compatibility equations.
-/

namespace EtaleCohomology.Classical

universe u

/-- The inverse limit subgroup for a sequence of additive transition maps. -/
def sequentialLimit (M : ℕ → Type u) [∀ n, AddCommGroup (M n)]
    (r : ∀ n, M (n + 1) →+ M n) : AddSubgroup (∀ n, M n) where
  carrier := {a | ∀ n, r n (a (n + 1)) = a n}
  zero_mem' := fun n => map_zero (r n)
  add_mem' ha hb n := (map_add (r n) _ _).trans (congrArg₂ (· + ·) (ha n) (hb n))
  neg_mem' ha n := (map_neg (r n) _).trans (congrArg Neg.neg (ha n))

/-- Evaluation of a compatible family at one level. -/
def sequentialLimitProjection (M : ℕ → Type u) [∀ n, AddCommGroup (M n)]
    (r : ∀ n, M (n + 1) →+ M n) (n : ℕ) : sequentialLimit M r →+ M n where
  toFun a := a.val n
  map_zero' := rfl
  map_add' _ _ := rfl

end EtaleCohomology.Classical
