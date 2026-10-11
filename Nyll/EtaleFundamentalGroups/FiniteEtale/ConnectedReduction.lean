/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Galois.Decomposition
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected

/-!
# Reducing essential surjectivity to connected finite-etale covers

A finite-etale cover of a connected scheme is a finite coproduct of connected
covers.  Since pullback preserves finite coproducts, extending every connected
cover is therefore enough to extend an arbitrary (possibly disconnected)
cover.  This file records that categorical reduction for the actual
finite-etale categories of schemes.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Pullback along `f` is essentially surjective once every connected
finite-etale cover of the connected source of `f` is in its essential image.

The conclusion includes disconnected covers: they are reconstructed as the
finite coproduct of their connected summands. -/
theorem pullback_essSurj_of_connected
    {X Y : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Y)
    (h : ∀ Z : FiniteEtale X, IsConnected Z →
      ∃ W : FiniteEtale Y, Nonempty ((pullback f).obj W ≅ Z)) :
    (pullback f).EssSurj := by
  constructor
  intro Z
  obtain ⟨ι, hι, C, eZ, hC⟩ := has_decomp_connected_components' Z
  let W (i : ι) : FiniteEtale Y :=
    Classical.choose (h (C i) (hC i))
  let e (i : ι) : (pullback f).obj (W i) ≅ C i :=
    Classical.choice (Classical.choose_spec (h (C i) (hC i)))
  let : Finite ι := hι
  refine ⟨colimit (Discrete.functor W), ⟨?_⟩⟩
  exact PreservesCoproduct.iso (pullback f) W ≪≫
    Sigma.mapIso e ≪≫ eZ

end AlgebraicGeometry.FiniteEtale

end
