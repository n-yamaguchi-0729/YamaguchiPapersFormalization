/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Integers
import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import Mathlib.CategoryTheory.Galois.Decomposition

/-!
# Example 1.4 (1): the fundamental group of the integers

The etale fundamental group of `Spec ℤ` is trivial for every geometric base point.
The proof uses Minkowski's discriminant bound to show that every connected finite
etale cover of `Spec ℤ` is trivial, then tests automorphisms on Galois objects.

Only the assertion about `Spec ℤ` is in scope. The projective-space and affine-space
assertions in the same item, items (2) and (3), and Corollary 2.7 are not formalized.

Source: `SolvableCoverings.tex`, `ex:section1_1`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale

namespace Yamaguchi26SolvableCoverings

/-- Example 1.4 (1) (`ex:section1_1`)：任意の幾何点を基点として、
整数環のスペクトルの étale 基本群は自明である。 -/
theorem fundamental_group_integers_1_4
    (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ)) :
    Subsingleton π₁ᵉᵗ(ξ) := by
  constructor
  intro a b
  apply Iso.ext
  apply PreGaloisCategory.natTrans_ext_of_isGalois (fiber ξ)
  intro Y _
  let _ : ConnectedSpace Y.left := connectedSpace_left_of_isConnected Y
  let _ : Subsingleton ((fiber ξ).obj Y) :=
    subsingleton_fiber_of_connected_over_integers Ω ξ Y
  ext x
  exact Subsingleton.elim _ _

end Yamaguchi26SolvableCoverings
