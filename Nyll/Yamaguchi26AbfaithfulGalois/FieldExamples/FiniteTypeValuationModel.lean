/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Finite-type models inside valuation rings

An essentially finite-type extension of a fraction field admits an
integral finite-type model inside any valuation ring containing the base
ring.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u v w

/-- A finitely generated extension of a fraction field admits a finite type
integral model inside any valuation ring containing the base ring. -/
theorem finiteType_model_in_valuation
    (R : Type u) (F : Type v) (E : Type w)
    [CommRing R] [IsDomain R] [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] [Algebra.EssFiniteType F E]
    (V : ValuationSubring E) (hR : ∀ r : R, algebraMap R E r ∈ V) :
    ∃ A : Subalgebra R E, Algebra.FiniteType R A ∧ IsFractionRing A E ∧
      A.toSubring ≤ V.toSubring := by
  classical
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F E
  let f : E → E := fun x => if x ∈ V then x else x⁻¹
  let t := s.image f
  let A := Algebra.adjoin R (t : Set E)
  have hAV : A.toSubring ≤ V.toSubring := by
    let B : Subalgebra R E := { V.toSubring with algebraMap_mem' := hR }
    change A ≤ B
    apply Algebra.adjoin_le_iff.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    change f y ∈ V
    dsimp only [f]
    split_ifs with hyV
    · exact hyV
    · exact (V.mem_or_inv_mem y).resolve_left hyV
  let S := Subfield.closure (A : Set E)
  have hF : ∀ x : F, algebraMap F E x ∈ S := by
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact S.div_mem (Subfield.subset_closure (A.algebraMap_mem a))
      (Subfield.subset_closure (A.algebraMap_mem b))
  let T : IntermediateField F E := { S with algebraMap_mem' := hF }
  have hst : IntermediateField.adjoin F (s : Set E) ≤ T := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    change x ∈ S
    have hfx : f x ∈ S := Subfield.subset_closure
      (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    by_cases hxV : x ∈ V
    · simpa only [f, ite_eq_left hxV] using hfx
    · have hi := S.inv_mem hfx
      simpa only [f, ite_eq_right hxV, inv_inv] using hi
  have htop : T = ⊤ := top_unique (hs ▸ hst)
  refine ⟨A, (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset t), ?_, hAV⟩
  apply IsFractionRing.of_field A E
  intro z
  have hz : z ∈ S := by
    change z ∈ T
    rw [htop]
    exact IntermediateField.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hz
  change a ∈ Subring.closure (A.toSubring : Set E) at ha
  change b ∈ Subring.closure (A.toSubring : Set E) at hb
  rw [Subring.closure_eq] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab.symm⟩

end Yamaguchi26AbfaithfulGalois
