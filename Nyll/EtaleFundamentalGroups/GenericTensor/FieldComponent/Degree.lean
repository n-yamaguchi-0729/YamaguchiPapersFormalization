/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic

/-!
# Degree bounds for selected generic tensor components

A field component selected from `K' tensor[K] L` is a quotient of that
base-changed finite-dimensional algebra.  Its degree over `K'` is therefore
bounded by the original degree of `L / K`.  This supplies one common
factorial exponent for all completed local components.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uK uK' uL

/-- Every selected field component of a finite field extension after base
change has degree at most the original field degree. -/
theorem genericTensorFieldComponent_finrank_le
    {K : Type uK} {K' : Type uK'} {L : Type uL}
    [Field K] [Field K'] [Field L]
    [Algebra K K'] [Algebra K L] [FiniteDimensional K L]
    (m : Ideal (K' ⊗[K] L)) [m.IsMaximal] :
    Module.finrank K' (GenericTensorFieldComponent m) ≤
      Module.finrank K L := by
  have hsurjective : Function.Surjective
      (Ideal.Quotient.mkₐ K' m).toLinearMap :=
    Ideal.Quotient.mk_surjective
  have hle :
      Module.finrank K' (GenericTensorFieldComponent m) ≤
        Module.finrank K' (K' ⊗[K] L) :=
    LinearMap.finrank_le_finrank_of_surjective hsurjective
  simpa only [Module.finrank_baseChange] using hle

end EtaleFundamentalGroups

end
