/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois

/-!
# The actual point action of the supplied Galois comparison

This computation is proved over abstract fields, so callers retain their
original field structures without unfolding the construction of the fiber
automorphism group at those concrete fields.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]

/-- The supplied Galois automorphism acts by its literal spectrum map. -/
theorem suppliedGaloisEquivFundamentalGroup_point
    (σ : Gal(Ω/F)) (X : FiniteEtale (Spec (.of F))) (x : (fib F Ω).obj X) :
    (fiberObjEquivHom (ξ F Ω) X
      ((suppliedGaloisEquivFundamentalGroup F Ω σ).hom.app X x)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (ξ F Ω) X x).left := by
  change (fiberObjEquivHom (ξ F Ω) X (σ • x)).left = _
  rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply, algEquiv_smul_hom]
  rfl

end AlgebraicGeometry.FiniteEtale
