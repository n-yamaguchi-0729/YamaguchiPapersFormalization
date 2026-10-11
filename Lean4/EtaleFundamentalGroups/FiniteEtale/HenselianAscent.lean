/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.LocalRing.Etale
import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Henselian ascent for finite étale local algebras over a complete base

For the complete-local chosen-factor argument, Noetherianity is not needed to
make a finite étale local factor Henselian.  Such a factor is finite free over
the base.  Adic completion commutes with finite products, so completeness of
the base transfers through a finite basis.  Formal unramifiedness then
identifies the extended base maximal ideal with the target maximal ideal.

This is intentionally a theorem, not a global instance: consumers install the
result only for the chosen local factor in scope.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

/-- A finite free module over an adically complete ring is adically complete,
without a Noetherian hypothesis.

The proof writes the module as a finite product of copies of the base and uses
the canonical equivalence between the completion of a finite product and the
finite product of completions. -/
theorem isAdicComplete_of_moduleFinite_of_moduleFree
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) [StrongRankCondition R]
    [Module.Finite R M] [Module.Free R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let n := Module.finrank R M
  let b : Module.Basis (Fin n) R M := Module.finBasis R M
  have hpi : IsAdicComplete I (Fin n → R) := by
    rw [← AdicCompletion.of_bijective_iff]
    let e : (Fin n → R) ≃ₗ[R] AdicCompletion I (Fin n → R) :=
      (LinearEquiv.piCongrRight
          (fun _ : Fin n ↦ AdicCompletion.ofLinearEquiv I R)).trans
        ((AdicCompletion.piEquivFin I n).symm.restrictScalars R)
    have heq : (e : (Fin n → R) → AdicCompletion I (Fin n → R)) =
        AdicCompletion.of I (Fin n → R) := by
      funext x
      apply (AdicCompletion.piEquivFin I n).injective
      funext i
      calc
        (AdicCompletion.piEquivFin I n (e x)) i =
            AdicCompletion.ofLinearEquiv I R (x i) := by
          simp [e]
        _ = AdicCompletion.of I R (x i) := rfl
        _ = (AdicCompletion.piEquivFin I n
            (AdicCompletion.of I (Fin n → R) x)) i := by
          rw [AdicCompletion.piEquivFin_apply]
          exact (AdicCompletion.map_of I (LinearMap.proj i) x).symm
    rw [← heq]
    exact e.bijective
  let : IsAdicComplete I (Fin n → R) := hpi
  exact
    ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv
      I b.equivFun.symm

/-- A finite étale local algebra over a complete local ring is Henselian local,
without a Noetherian hypothesis.

Localness and local-hom status are primitive inputs.  The latter is exactly
what lets formal unramifiedness identify the extended base maximal ideal with
the target maximal ideal. -/
theorem henselianLocalRing_of_finiteEtale_local_of_isAdicComplete
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite R S] [Algebra.Etale R S] :
    HenselianLocalRing S := by
  let : Module.Free R S := Module.free_of_flat_of_isLocalRing
  have hcomplete :
      IsAdicComplete (IsLocalRing.maximalIdeal R) S :=
    isAdicComplete_of_moduleFinite_of_moduleFree
      (I := IsLocalRing.maximalIdeal R) (M := S)
  have hm :
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
        IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hcompleteMax :
      IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
    rw [← hm]
    exact (ValuationTheory.DiscreteValuationField.isAdicComplete_map_algebraMap_iff
      (R := R) (S := S) (IsLocalRing.maximalIdeal R)).2 hcomplete
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S := hcompleteMax
  let : HenselianRing S (IsLocalRing.maximalIdeal S) := inferInstance
  refine { is_henselian := ?_ }
  intro f hf x hx hderivative
  exact HenselianRing.is_henselian f hf x hx
    (hderivative.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)))

end EtaleFundamentalGroups
