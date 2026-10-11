/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeHeightTwoPrime
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeLocalizedChart
import SchemeTheory.LocalGeometry.HeightTwo.ResidueCharacteristic
import SchemeTheory.Divisors.NormalCrossings.BranchSelection

/-!
# Arithmetic height-two charts for normal-crossings branches

Characteristic zero along every height-one boundary branch and one positive
residue-characteristic specialization produce the complete height-two split
chart used by the finite-quotient Abhyankar argument.  In particular the
height-two prime, localized branch, and residue-characteristic target are
outputs rather than extra inputs.
-/

noncomputable section

open EtaleFundamentalGroups IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- Every height-one branch through the boundary at `x` has characteristic
zero.  This is the local algebraic form of horizontal boundary components. -/
def HasCharacteristicZeroBranchesAt
    (I : X.IdealSheafData) (x : X) : Prop :=
  ∀ (q : Ideal (X.presheaf.stalk x)) (_hq : q.IsPrime),
    q.height = 1 → I.stalkIdeal x ≤ q →
      CharZero (X.presheaf.stalk x ⧸ q)

/-- A positive residue characteristic on one height-one branch produces a
height-two split chart.  Characteristic zero is transported from every
original boundary branch to every active branch of the localized chart. -/
theorem IsStrictNormalCrossings.exists_heightTwo_localSplitChart_of_branch_residueCharacteristic
    (hI : I.IsStrictNormalCrossings)
    (hCharZero : I.HasCharacteristicZeroBranchesAt x)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q)
    {k : Type uk} [CommRing k] [Nontrivial k]
    (phi : (X.presheaf.stalk x ⧸ q) →+* k)
    (p : ℕ) [CharP k p] (hp : p.Prime) :
    let A := X.presheaf.stalk x
    ∃ (P : Ideal A) (_hPprime : P.IsPrime),
      q < P ∧ P.height = 2 ∧
        let V := Localization.AtPrime P
        ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2)
          (_hVdomain : IsDomain V) (_hVregular : IsRegularRing V),
          (I.stalkIdeal x).map (algebraMap A V) =
              Ideal.span {boundaryProduct t r} ∧
            IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r ∧
              i.1 < r ∧
                q.map (algebraMap A V) = Ideal.span {t i} ∧
                  (∀ j : Fin 2, j.1 < r →
                    CharZero (V ⧸ Ideal.span {t j})) ∧
                    CharP (V ⧸ maximalIdeal V) p := by
  dsimp only
  let A := X.presheaf.stalk x
  let : CharZero (A ⧸ q) :=
    hCharZero q inferInstance hqheight hIq
  obtain ⟨P, hPprime, hqP, hPheight, hp_nonunit⟩ :=
    hI.exists_heightTwoPrime_of_branch_residueCharacteristic
      q hqheight hIq phi p hp
  let : P.IsPrime := hPprime
  let V := Localization.AtPrime P
  obtain ⟨r, t, hVdomain, hVregular, hboundary, hNC⟩ :=
    hI.exists_localSplitChart_with_boundaryIdeal
      (x := x) (P := ⟨P, hPprime⟩) hPheight (hIq.trans hqP.le)
  let : IsDomain V := hVdomain
  let qV := q.map (algebraMap A V)
  let : qV.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime P hqP.le
  have hdisjoint : Disjoint ((P.primeCompl : Submonoid A) : Set A) (q : Set A) :=
    Set.disjoint_compl_left_iff_subset.mpr hqP.le
  have hqVheight : qV.height = 1 := by
    rw [IsLocalization.height_map_of_disjoint P.primeCompl q hdisjoint]
    exact hqheight
  have hprod : boundaryProduct t r ∈ qV := by
    apply (Ideal.map_mono hIq)
    rw [hboundary]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨i, hi, hqi⟩ :=
    exists_activeBranch_eq_of_heightOnePrime_mem_boundaryProduct
      hNC.2.2.2.1 qV hqVheight hprod
  have hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
      CharZero (V ⧸ Ideal.span {t j}) := by
    intro j hj
    let qj : Ideal V := Ideal.span {t j}
    let : qj.IsPrime :=
      Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 j hj)
    have hqjheight : qj.height = 1 := by
      exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr
          (hNC.2.2.2.1 j hj).ne_zero)
        (hNC.2.2.2.1 j hj).not_isUnit
    have hprodj : boundaryProduct t r ∈ qj := by
      rw [boundaryProduct, Ideal.IsPrime.prod_mem_iff]
      refine ⟨j, ?_, Ideal.mem_span_singleton_self _⟩
      simp only [boundaryIndices, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hj
    have hmapI_qj : (I.stalkIdeal x).map (algebraMap A V) ≤ qj := by
      rw [hboundary]
      exact Ideal.span_le.mpr fun a ha ↦ by
        simpa only [Set.mem_singleton_iff] using ha ▸ hprodj
    have hIunder : I.stalkIdeal x ≤ qj.under A := by
      exact (Ideal.map_le_iff_le_comap).mp hmapI_qj
    have hqunderHeight : (qj.under A).height = 1 := by
      rw [IsLocalization.height_under P.primeCompl qj]
      exact hqjheight
    let : CharZero (A ⧸ qj.under A) :=
      hCharZero (qj.under A) inferInstance hqunderHeight hIunder
    exact charZero_of_injective_algebraMap
      (Ideal.algebraMap_quotient_injective (R := A) (A := V) (I := qj))
  have hpChar : CharP (V ⧸ maximalIdeal V) p :=
    charP_localizationAtPrime_residue_of_natCast_nonunit P p hp hp_nonunit
  exact ⟨P, hPprime, hqP, hPheight, r, t, i, hVdomain, hVregular,
    hboundary, hNC, hi, hqi, hlocalizedCharZero, hpChar⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
