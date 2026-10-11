/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Normal subgroups acting on field embeddings

For a normal subgroup of the automorphism group of a normal field extension,
fixing an intermediate field is equivalent to fixing every embedding of that
field into the ambient extension. The intermediate field need not be normal
or finite, and the subgroup need not be closed.
-/

namespace EtaleFundamentalGroups

universe u v

variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
  [Normal K E]

/-- A normal subgroup acts trivially on all embeddings of an intermediate
field precisely when it fixes that field pointwise. Embeddings are extended
to ambient automorphisms using normality of the ambient extension, without
any normality assumption on the intermediate field. -/
theorem normalSubgroup_fixes_embeddings_iff_le_fixingSubgroup
    (H : Subgroup (E ≃ₐ[K] E)) [H.Normal] (L : IntermediateField K E) :
    (∀ g ∈ H, ∀ φ : L →ₐ[K] E, g.toAlgHom.comp φ = φ) ↔
      H ≤ L.fixingSubgroup := by
  constructor
  · intro h g hg
    apply (IntermediateField.mem_fixingSubgroup_iff L g).mpr
    intro x hx
    exact DFunLike.congr_fun (h g hg L.val) ⟨x, hx⟩
  · intro h g hg φ
    apply AlgHom.ext
    intro x
    let σ : E ≃ₐ[K] E :=
      AlgEquiv.ofBijective (φ.liftNormal E) (AlgHom.normal_bijective K E E _)
    have hx : (x : E) ∈ MulAction.fixedPoints H E := by
      intro τ
      exact (IntermediateField.mem_fixingSubgroup_iff L τ.val).mp
        (h τ.property) x.val x.property
    have hσ : σ • (x : E) = φ x := by
      change φ.liftNormal E (algebraMap L E x) = φ x
      exact φ.liftNormal_commutes E x
    have hφ : φ x ∈ MulAction.fixedPoints H E :=
      hσ ▸ smul_mem_fixedPoints_of_normal σ hx
    exact hφ ⟨g, hg⟩

end EtaleFundamentalGroups
