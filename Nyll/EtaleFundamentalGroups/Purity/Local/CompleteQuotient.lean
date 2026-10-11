/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.Quotient
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Quotients of complete local rings

A quotient of a Noetherian complete local ring by an ideal contained in the
maximal ideal is again complete local, hence Henselian.  Completeness is first
proved for the extended maximal ideal; surjectivity of the quotient map then
identifies this ideal with the maximal ideal of the quotient.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open ValuationTheory.DiscreteValuationField

universe u

/-- The quotient of a Noetherian adically complete ring is complete for the
extension of the ideal of definition. -/
theorem isAdicComplete_map_maximalIdeal_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (I : Ideal R) :
    IsAdicComplete
      ((maximalIdeal R).map (algebraMap R (R ⧸ I))) (R ⧸ I) := by
  have hcomplete : IsAdicComplete (maximalIdeal R) (R ⧸ I) :=
    isAdicComplete_of_moduleFinite (I := maximalIdeal R) (M := R ⧸ I)
  exact (IsAdicComplete.map_algebraMap_iff
    (S := R ⧸ I) (maximalIdeal R) (R ⧸ I)).2 hcomplete

/-- A quotient of a Noetherian complete local ring by an ideal contained in
the maximal ideal is Henselian local. -/
theorem henselianLocalRing_quotient_of_isAdicComplete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    HenselianLocalRing (R ⧸ I) := by
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmaximal :
      (maximalIdeal R).map (algebraMap R (R ⧸ I)) =
        maximalIdeal (R ⧸ I) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I) := by
    rw [← hmaximal]
    exact isAdicComplete_map_maximalIdeal_quotient I
  let : HenselianRing (R ⧸ I) (maximalIdeal (R ⧸ I)) :=
    inferInstance
  refine { is_henselian := ?_ }
  intro f hf x hx hderivative
  exact HenselianRing.is_henselian f hf x hx
    (hderivative.map (Ideal.Quotient.mk (maximalIdeal (R ⧸ I))))

end EtaleFundamentalGroups

end
