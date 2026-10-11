/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RegularLocalRing.Defs
import EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.MvPowerSeriesNoetherian
import SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleEqualizer

/-!
# Regular local geometry of the maximal-adic completion

The maximal-adic completion of a Noetherian local ring is flat and local,
hence faithfully flat.  Once Noetherianity of the completed ring has been
produced, going down and the explicit description of its maximal ideal show
that completion preserves Krull dimension.  The cotangent-space comparison
then shows that regularity is preserved as well.

The Noetherianity hypothesis on the completed ring is deliberately visible:
Mathlib currently supplies flatness of a Noetherian adic completion, but not
Noetherianity of the completed ring itself.  Separate source-producing results
can discharge that hypothesis without changing these statements.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u v

/-- The maximal-adic completion of a Noetherian local ring is faithfully flat
over the original ring. -/
theorem maximalAdicCompletion_faithfullyFlat
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.FaithfullyFlat R
      (AdicCompletion (maximalIdeal R) R) := by
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Every module over a Noetherian local ring is recovered as the equalizer
of its two pullbacks from the maximal-adic completion to the double
completion.  This is the faithfully-flat equalizer input for formal gluing;
it does not assume that the source ring is complete. -/
noncomputable def maximalAdicCompletionModuleEqualizerEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    M ≃ₗ[R] LinearMap.eqLocus
      (tensorProductDescentLeft
        (R := R) (S := AdicCompletion (maximalIdeal R) R) (M := M))
      (tensorProductDescentRight
        (R := R) (S := AdicCompletion (maximalIdeal R) R) (M := M)) := by
  letI : Module.FaithfullyFlat R
      (AdicCompletion (maximalIdeal R) R) :=
    maximalAdicCompletion_faithfullyFlat R
  exact tensorProductEqualizerEquiv

@[simp]
theorem maximalAdicCompletionModuleEqualizerEquiv_apply
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    (maximalAdicCompletionModuleEqualizerEquiv R M m :
        (AdicCompletion (maximalIdeal R) R) ⊗[R] M) =
      1 ⊗ₜ[R] m :=
  rfl

/-- If the original module is finite, then its explicit maximal-adic
completion equalizer is finite as an `R`-module. -/
theorem maximalAdicCompletionModuleEqualizer_finite
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (LinearMap.eqLocus
      (tensorProductDescentLeft
        (R := R) (S := AdicCompletion (maximalIdeal R) R) (M := M))
      (tensorProductDescentRight
        (R := R) (S := AdicCompletion (maximalIdeal R) R) (M := M))) :=
  Module.Finite.equiv (maximalAdicCompletionModuleEqualizerEquiv R M)

/-- A Noetherian maximal-adic completion has the same Krull dimension as its
source.  The proof uses faithful flatness only through going down; the closed
fibre has height zero because the source maximal ideal maps onto the target
maximal ideal. -/
theorem maximalAdicCompletion_ringKrullDim_eq_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsNoetherianRing (AdicCompletion (maximalIdeal R) R)] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) =
      ringKrullDim R := by
  let Rhat := AdicCompletion (maximalIdeal R) R
  let : Module.FaithfullyFlat R Rhat :=
    maximalAdicCompletion_faithfullyFlat R
  let p : Ideal R := maximalIdeal R
  let P : Ideal Rhat := maximalIdeal Rhat
  let : P.LiesOver p := by
    refine ⟨?_⟩
    exact (IsLocalRing.maximalIdeal_comap (algebraMap R Rhat)).symm
  have hheight : P.height = p.height := by
    have h :=
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
    have hmap : p.map (algebraMap R Rhat) = P := by
      exact AdicCompletion.maximalIdeal_eq_map.symm
    rw [hmap, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
    exact h
  have hheight' :
      (P.height : WithBot ℕ∞) = (p.height : WithBot ℕ∞) :=
    congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hheight
  calc
    ringKrullDim Rhat = P.height :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ = p.height := hheight'
    _ = ringKrullDim R :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- If the maximal-adic completion has been shown Noetherian, regularity of a
Noetherian local source ascends to its completion. -/
theorem maximalAdicCompletion_isRegularLocalRing_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsNoetherianRing (AdicCompletion (maximalIdeal R) R)] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank :
        WithBot ℕ∞) =
        ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
      exact_mod_cast AdicCompletion.spanFinrank_maximalIdeal_eq
    _ = ringKrullDim R :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    _ = ringKrullDim (AdicCompletion (maximalIdeal R) R) :=
      (maximalAdicCompletion_ringKrullDim_eq_of_isNoetherianRing R).symm
    _ ≤ ringKrullDim (AdicCompletion (maximalIdeal R) R) := le_rfl

/-- Maximal-adic completion preserves the Krull dimension of every
Noetherian local ring. -/
theorem maximalAdicCompletion_ringKrullDim_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) =
      ringKrullDim R :=
  maximalAdicCompletion_ringKrullDim_eq_of_isNoetherianRing R

/-- The maximal-adic completion of a regular local ring is regular local. -/
theorem maximalAdicCompletion_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  maximalAdicCompletion_isRegularLocalRing_of_isNoetherianRing R

end EtaleFundamentalGroups

end
