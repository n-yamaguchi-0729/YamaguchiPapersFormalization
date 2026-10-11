/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Galois.Decomposition
import EtaleFundamentalGroups.FiniteEtale.Connected

/-!
# Domination by finite-etale Galois covers

Every connected finite-etale cover of a connected scheme is dominated by a
Galois object.  This file specializes the abstract Galois-category theorem
to finite-etale schemes, choosing a geometric fiber functor canonically from
an arbitrary point of the base.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- A connected finite-etale cover is dominated by a finite-etale Galois
cover. -/
lemma exists_galois_domination (W : FiniteEtale X)
    [ConnectedSpace W.left] :
    ∃ (A : FiniteEtale X) (_ : A ⟶ W), IsGalois A := by
  let : IsConnected W := isConnected_of_connectedSpace_left W
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let k : Type u := X.residueField x
  let Ω : Type u := AlgebraicClosure k
  let ξ : Spec (.of Ω) ⟶ X :=
    Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫
      X.fromSpecResidueField x
  exact exists_hom_from_galois_of_connected (fiber ξ) W

end AlgebraicGeometry.FiniteEtale
