/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.PrimaryRootsFiniteness
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Root finiteness in subfields

A finite separable extension of a subfield embeds in a finite extension
of the ambient field. In characteristic zero this descends finiteness of
primary roots of unity to finite extensions of the subfield.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u v w

/-- A finite separable extension of a subfield embeds in a finite extension
of the ambient field, using a primitive generator. -/
theorem finiteExtension_embedding_over_subfield
    (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ T : IntermediateField E (AlgebraicClosure E), FiniteDimensional E T ∧
      Nonempty (L →+* T) := by
  let j : L →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  obtain ⟨x, hx⟩ := Field.exists_primitive_element K L
  let T := IntermediateField.adjoin E ({j x} : Set (AlgebraicClosure E))
  have hfinite : FiniteDimensional E T := IntermediateField.adjoin.finiteDimensional
    ((Algebra.IsIntegral.isIntegral (R := K) x).map j).tower_top
  have hle : j.fieldRange ≤ T.restrictScalars K := by
    have hm : j.fieldRange = IntermediateField.adjoin K ({j x} : Set (AlgebraicClosure E)) := by
      rw [← Set.image_singleton, ← IntermediateField.adjoin_map, hx]
      ext y
      exact ⟨fun ⟨z, hz⟩ => ⟨z, IntermediateField.mem_top, hz⟩,
        fun ⟨z, _, hz⟩ => ⟨z, hz⟩⟩
    rw [hm]
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    exact IntermediateField.subset_adjoin E _ hy
  let f : L →+* T :=
    { toFun := fun y => ⟨j y, hle ⟨y, rfl⟩⟩
      map_zero' := Subtype.ext j.map_zero
      map_one' := Subtype.ext j.map_one
      map_add' := fun a b => Subtype.ext (j.map_add a b)
      map_mul' := fun a b => Subtype.ext (j.map_mul a b) }
  exact ⟨T, hfinite, ⟨f⟩⟩

/-- Root finiteness in finite extensions descends to arbitrary subfields
in characteristic zero. -/
theorem finite_primaryComponent_finiteExtension_of_subfield
    (K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E] [CharZero K]
    (p : ℕ)
    (hRoots : ∀ T : IntermediateField E (AlgebraicClosure E), FiniteDimensional E T →
      Finite (CommGroup.primaryComponent Tˣ p))
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] :
    Finite (CommGroup.primaryComponent Lˣ p) := by
  obtain ⟨T, hT, ⟨f⟩⟩ := finiteExtension_embedding_over_subfield K E L
  have : Finite (CommGroup.primaryComponent Tˣ p) := hRoots T hT
  exact KummerTheory.finite_primaryComponent_of_fieldEmbedding f p

end Yamaguchi26AbfaithfulGalois
