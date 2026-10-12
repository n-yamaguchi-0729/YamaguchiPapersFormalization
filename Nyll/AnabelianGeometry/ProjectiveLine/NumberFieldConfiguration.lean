/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.EmbeddedMultiplicativeRigidity
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Multiplicative configuration reconstruction over number fields

Two cyclic multiplicative subgroups recover a normalized parameter up to
an explicit quadratic exception. The same data for one chosen square root
eliminates that exception. These statements concern actual field elements;
recovering their cyclic subgroups from a fundamental group is a separate step.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Over a number field, the parameter and complementary cyclic subgroups
leave only the quadratic exceptional locus. -/
theorem units_eq_or_sq_sub_add_one_eq_zero
    {x y c d : Kˣ}
    (hc : (x : K) + (c : K) = 1) (hd : (y : K) + (d : K) = 1)
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y)
    (hcd : Subgroup.zpowers c = Subgroup.zpowers d) :
    x = y ∨ (x : K) ^ 2 - (x : K) + 1 = 0 := by
  obtain ⟨e⟩ := (inferInstance : Nonempty (K →+* ℂ))
  exact units_eq_or_sq_sub_add_one_eq_zero_of_embedding e hc hd hxy hcd

/-- Cyclic subgroup data for a parameter and one square-root lift recovers
the parameter without an exceptional-locus restriction. -/
theorem units_eq_of_cyclic_data_and_square_roots
    {x y c d t u v w : Kˣ}
    (hc : (x : K) + (c : K) = 1) (hd : (y : K) + (d : K) = 1)
    (hv : (t : K) + (v : K) = 1) (hw : (u : K) + (w : K) = 1)
    (ht : (t : K) ^ 2 = (x : K)) (hu : (u : K) ^ 2 = (y : K))
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y)
    (hcd : Subgroup.zpowers c = Subgroup.zpowers d)
    (htu : Subgroup.zpowers t = Subgroup.zpowers u)
    (hvw : Subgroup.zpowers v = Subgroup.zpowers w) : x = y := by
  rcases units_eq_or_sq_sub_add_one_eq_zero hc hd hxy hcd with h | he
  · exact h
  · have hte : (t : K) ^ 2 - (t : K) + 1 ≠ 0 :=
      sq_sub_add_one_ne_zero_of_sq_eq (by norm_num) he ht
    rcases units_eq_or_sq_sub_add_one_eq_zero hv hw htu hvw with h | he'
    · apply Units.ext
      calc
        (x : K) = (t : K) ^ 2 := ht.symm
        _ = (u : K) ^ 2 := congrArg (fun z : Kˣ => (z : K) ^ 2) h
        _ = (y : K) := hu
    · exact False.elim (hte he')

end AnabelianGeometry.ProjectiveLine
