/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyAnnihilatedGenerators
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyRadical
import EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction
import Mathlib.Data.List.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Top local cohomology of an annihilated coefficient module

A nonzero element of the maximal ideal of a Noetherian local domain can
be completed to a system of parameters.  Lift a system of parameters from
the quotient by that element; regularity gives the required dimension drop.

If this first parameter annihilates the coefficient module, the sharpened
generator bound gives vanishing in the top degree.  This is the coefficient
vanishing input for multiplication on top local cohomology, in every finite
dimension.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- A nonzero nonunit in a local domain of dimension `d + 1` extends to a
list of `d + 1` parameters with maximal radical. -/
theorem exists_parameter_list_radical_eq_maximalIdeal_of_ringKrullDim_eq_succ
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x : R) (hx0 : x ≠ 0) (hxmem : x ∈ maximalIdeal R) :
    ∃ xs : List R, xs.length = d ∧
      (Ideal.ofList (x :: xs)).radical = maximalIdeal R := by
  let I : Ideal R := Ideal.span {x}
  let S := R ⧸ I
  let q : R →+* S := Ideal.Quotient.mk I
  have hIle : I ≤ maximalIdeal R :=
    (maximalIdeal R).span_singleton_le_iff_mem.mpr hxmem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q :=
    IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S q Ideal.Quotient.mk_surjective
  have hdimSsucc : ringKrullDim S + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (IsSMulRegular.of_ne_zero hx0) hxmem
  have hdimS : ringKrullDim S = (d : WithBot ℕ∞) := by
    apply ENat.WithBot.add_one_cancel.mp
    calc
      ringKrullDim S + 1 = ringKrullDim R := hdimSsucc
      _ = ((d + 1 : ℕ) : WithBot ℕ∞) := hdim
      _ = (d : WithBot ℕ∞) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
  obtain ⟨ys, hysLength, hysRadical⟩ :=
    exists_ofList_radical_eq_maximalIdeal_of_ringKrullDim_eq d hdimS
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  obtain ⟨xs, rfl⟩ := List.map_surjective_iff.mpr hq ys
  refine ⟨xs, ?_, ?_⟩
  · simpa only [List.length_map] using hysLength
  · have hcomap : Ideal.comap q (Ideal.ofList (xs.map q)) =
        I ⊔ Ideal.ofList xs := by
      calc
        Ideal.comap q (Ideal.ofList (xs.map q)) =
            Ideal.comap q ((Ideal.ofList xs).map q) := by
              rw [Ideal.map_ofList]
        _ = Ideal.ofList xs ⊔ Ideal.comap q ⊥ :=
          Ideal.comap_map_of_surjective q hq (Ideal.ofList xs)
        _ = I ⊔ Ideal.ofList xs := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          exact sup_comm _ _
    have hradical := congrArg (Ideal.comap q) hysRadical
    rw [Ideal.comap_radical, hcomap,
      IsLocalRing.maximalIdeal_comap q] at hradical
    simpa only [Ideal.ofList_cons, I] using hradical

/-- In every positive finite dimension, a nonzero member of the maximal
ideal annihilating the coefficients forces top local cohomology to vanish. -/
theorem derivedLocalCohomology_maximalIdeal_isZero_succ_of_smul_id_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x : R) (hx0 : x ≠ 0) (hxmem : x ∈ maximalIdeal R)
    (M : ModuleCat.{u} R) (hx : x • 𝟙 M = 0) :
    IsZero (derivedLocalCohomology (maximalIdeal R) M (d + 1)) := by
  obtain ⟨xs, hlength, hradical⟩ :=
    exists_parameter_list_radical_eq_maximalIdeal_of_ringKrullDim_eq_succ
      d hdim x hx0 hxmem
  have hOfList :
      IsZero (derivedLocalCohomology (Ideal.ofList (x :: xs)) M (d + 1)) :=
    derivedLocalCohomology_ofList_cons_isZero_of_smul_id_eq_zero
      x xs M hx (d + 1) (by omega)
  have hRadical :
      (Ideal.ofList (x :: xs)).radical = (maximalIdeal R).radical :=
    hradical.trans (maximalIdeal.isMaximal R).isPrime.isRadical.radical.symm
  exact hOfList.of_iso
    (derivedLocalCohomologyIsoOfSameRadical hRadical M (d + 1)).symm

end EtaleFundamentalGroups

end
