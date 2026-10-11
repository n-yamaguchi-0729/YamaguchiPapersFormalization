/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Idempotents
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian

/-!
# Lifting complete orthogonal idempotents over Henselian quotients

A finite complete family of orthogonal idempotents lifts along a surjective
ring homomorphism whose kernel is a Henselian ideal.  Individual idempotents
lift by Hensel's lemma.  Their lifts are automatically orthogonal because an
idempotent in the Jacobson radical is zero; the same argument makes their sum
equal to one.
-/

noncomputable section

namespace EtaleFundamentalGroups

/-- A finite complete family of orthogonal idempotents lifts along a
surjective ring homomorphism whose kernel is a Henselian ideal. -/
theorem exists_completeOrthogonalIdempotents_lift_of_surjective_henselianRing_ker
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    (f : R →+* S) (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : ι → S) (he : CompleteOrthogonalIdempotents e) :
    ∃ e' : ι → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  classical
  choose e' he'_idem he'_map using fun i ↦
    ValuationTheory.DiscreteValuationField.exists_idempotent_lift_of_surjective_henselianRing_ker
      f hf (e i) (he.idem i)
  have he'_ortho : Pairwise (e' · * e' · = 0) := by
    intro i j hij
    have hij_idem : IsIdempotentElem (e' i * e' j) := by
      rw [IsIdempotentElem]
      calc
        (e' i * e' j) * (e' i * e' j) = (e' i * e' i) * (e' j * e' j) := by
          ring
        _ = e' i * e' j := by rw [(he'_idem i).eq, (he'_idem j).eq]
    have hij_ker : e' i * e' j ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_mul, he'_map i, he'_map j]
      exact he.ortho hij
    have hij_jac : e' i * e' j ∈ Ideal.jacobson (⊥ : Ideal R) :=
      HenselianRing.jac hij_ker
    have hunit : IsUnit (1 - e' i * e' j) := by
      apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
      simpa only [sub_sub_cancel_left] using neg_mem hij_jac
    have hone : 1 - e' i * e' j = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hij_idem.one_sub
    exact sub_eq_self.mp hone
  let horth : OrthogonalIdempotents e' := ⟨he'_idem, he'_ortho⟩
  have hsum_idem : IsIdempotentElem (∑ i, e' i) := by
    simpa using horth.isIdempotentElem_sum (s := Finset.univ)
  have hsum_ker : (∑ i, e' i) - 1 ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_sum, map_one]
    simp only [he'_map, he.complete, sub_self]
  have hsum_jac : (∑ i, e' i) - 1 ∈ Ideal.jacobson (⊥ : Ideal R) :=
    HenselianRing.jac hsum_ker
  have hsum_unit : IsUnit (∑ i, e' i) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hsum_jac
  have hsum : ∑ i, e' i = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit hsum_unit).mp hsum_idem
  refine ⟨e', ⟨⟨he'_idem, he'_ortho⟩, hsum⟩, ?_⟩
  funext i
  exact he'_map i

end EtaleFundamentalGroups
