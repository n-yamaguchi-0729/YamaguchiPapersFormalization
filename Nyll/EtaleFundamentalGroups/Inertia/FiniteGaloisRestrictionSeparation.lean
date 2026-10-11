/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionGroupMap
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Normal.Defs

/-!
# Actual finite Galois restrictions separate original automorphisms

Every coefficient belongs to its finite Galois closure. Agreement on all
actual finite restrictions therefore gives agreement on every coefficient.
-/

namespace EtaleFundamentalGroups.Inertia

universe v w

/-- Joint faithfulness is derived from the actual finite Galois closures. -/
theorem finiteGaloisRestrictionGroupMap_jointly_injective
    (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (σ τ : Gal(L/K))
    (h : ∀ E : FiniteGaloisIntermediateField K L,
      (finiteGaloisRestrictionGroupMap K L E).hom'.toFun σ =
        (finiteGaloisRestrictionGroupMap K L E).hom'.toFun τ) : σ = τ := by
  apply AlgEquiv.ext
  intro x
  let E : FiniteGaloisIntermediateField K L := FiniteGaloisIntermediateField.adjoin K {x}
  have hx : x ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)
  have heval := congrArg (fun g : Gal(E/K) => ((g ⟨x, hx⟩ : E) : L)) (h E)
  exact (AlgEquiv.restrictNormal_commutes σ E ⟨x, hx⟩).symm.trans
    (heval.trans (AlgEquiv.restrictNormal_commutes τ E ⟨x, hx⟩))

end EtaleFundamentalGroups.Inertia
