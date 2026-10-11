/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Scheme
import Nyll.SchemeTheory.Divisors.NormalCrossings.BranchSelection
import Nyll.SchemeTheory.Divisors.NormalCrossings.Transport
import Nyll.EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-!
# Selected divisor branches in local scheme charts

The strict-normal-crossings chart at a height-two point of a local scheme is
compatible with height-one divisor primes in the original stalk.  After the
canonical stalk/localization identification, such a prime is exactly one of
the active parameter ideals.  The final theorem applies this to a prime of a
normalization and produces the `LiesOver` datum consumed by Kummer inertia.
-/

noncomputable section

open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A height-one divisor prime below a height-two prime becomes one of the
active parameter ideals in the canonical localized strict-normal-crossings
chart. -/
theorem IsStrictNormalCrossings.exists_localSplitChart_with_selectedBranch
    (hI : I.IsStrictNormalCrossings)
    (P : AlgebraicGeometry.Spec (X.presheaf.stalk x))
    (hPheight : P.asIdeal.height = 2)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q) (hqP : q ≤ P.asIdeal) :
    letI : P.asIdeal.IsPrime := P.isPrime
    let V := Localization.AtPrime P.asIdeal
    let qV := q.map (algebraMap (X.presheaf.stalk x) V)
    ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2),
      IsDomain V ∧ IsRegularRing V ∧
        EtaleFundamentalGroups.IsSplitStrictNormalCrossingsAt
          (EtaleFundamentalGroups.boundaryProduct t r) t r ∧
        i.1 < r ∧ qV = Ideal.span ({t i} : Set V) := by
  dsimp only
  let A := X.presheaf.stalk x
  let : P.asIdeal.IsPrime := P.isPrime
  let V := Localization.AtPrime P.asIdeal
  let qV := q.map (algebraMap A V)
  have hxI : x ∈ I.support := by
    rw [← X.fromSpecStalk_closedPoint (x := x)]
    apply I.mem_support_fromSpecStalk_of_stalkIdeal_le
    exact hIq.trans
      (IsLocalRing.le_maximalIdeal (inferInstance : q.IsPrime).ne_top)
  obtain ⟨_, _, _, _, _, _, _, hdomainA, _, _⟩ :=
    (hI x hxI).localParameterGeometry
  let : IsDomain A := hdomainA
  let : qV.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime P.asIdeal hqP
  have hdisjoint : Disjoint
      ((P.asIdeal.primeCompl : Submonoid A) : Set A) (q : Set A) :=
    Set.disjoint_compl_left_iff_subset.mpr hqP
  have hqVheight : qV.height = 1 := by
    rw [IsLocalization.height_map_of_disjoint P.asIdeal.primeCompl q hdisjoint]
    exact hqheight
  obtain ⟨r, s, hdomainY, hregularY, hideal, hNC⟩ :=
    hI.localSplitChart_at_fromSpecStalk_of_height_two P hPheight
      (I.mem_support_fromSpecStalk_of_stalkIdeal_le x P (hIq.trans hqP))
  let e := X.stalkFromSpecStalkEquivLocalization x P
  let t : Fin 2 → V := e ∘ s
  let : IsRegularRing
      (X.presheaf.stalk (X.fromSpecStalk x P)) := hregularY
  have hregularV : IsRegularRing V := IsRegularRing.of_ringEquiv e
  have hNCV : EtaleFundamentalGroups.IsSplitStrictNormalCrossingsAt
      (EtaleFundamentalGroups.boundaryProduct t r) t r := by
    simpa only [t, Function.comp_apply,
      EtaleFundamentalGroups.boundaryProduct, map_prod] using
      hNC.map_ringEquiv e
  have hboundaryMem :
      EtaleFundamentalGroups.boundaryProduct t r ∈ qV := by
    have hsI : EtaleFundamentalGroups.boundaryProduct s r ∈
        I.stalkIdeal (X.fromSpecStalk x P) := by
      rw [hideal]
      exact Ideal.mem_span_singleton_self _
    have hsMap : e (EtaleFundamentalGroups.boundaryProduct s r) ∈
        (I.stalkIdeal (X.fromSpecStalk x P)).map e.toRingHom :=
      Ideal.mem_map_of_mem e.toRingHom hsI
    rw [I.map_stalkIdeal_stalkFromSpecStalkEquivLocalization x P] at hsMap
    have hsQV : e (EtaleFundamentalGroups.boundaryProduct s r) ∈ qV :=
      (Ideal.map_mono hIq) hsMap
    simpa only [t, Function.comp_apply,
      EtaleFundamentalGroups.boundaryProduct, map_prod] using hsQV
  obtain ⟨i, hi, hqi⟩ :=
    EtaleFundamentalGroups.exists_activeBranch_eq_of_heightOnePrime_mem_boundary
      hNCV qV hqVheight hboundaryMem
  exact ⟨r, t, i, inferInstance, hregularV, hNCV, hi, hqi⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace EtaleFundamentalGroups.Kummer

universe u

/-- A height-one normalization prime below a height-two point lies over an
active branch in the canonical localized scheme chart. -/
theorem exists_localSplitChart_localizedNormalizationPrime_liesOver_activeBranch
    {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData} {x : X}
    {K L : Type u}
    [IsDomain (X.presheaf.stalk x)]
    [Field K] [Field L]
    [Algebra (X.presheaf.stalk x) K]
    [IsFractionRing (X.presheaf.stalk x) K]
    [Algebra K L] [Algebra (X.presheaf.stalk x) L]
    [IsScalarTower (X.presheaf.stalk x) K L]
    (hI : I.IsStrictNormalCrossings)
    (P : AlgebraicGeometry.Spec (X.presheaf.stalk x))
    (hPheight : P.asIdeal.height = 2)
    (Q : Ideal (integralClosure (X.presheaf.stalk x) L)) [Q.IsPrime]
    (hQheight : (Q.under (X.presheaf.stalk x)).height = 1)
    (hIQ : I.stalkIdeal x ≤ Q.under (X.presheaf.stalk x))
    (hQP : Q.under (X.presheaf.stalk x) ≤ P.asIdeal) :
    letI : P.asIdeal.IsPrime := P.isPrime
    let V := Localization.AtPrime P.asIdeal
    let QP := localizedNormalizationPrime (K := K) (L := L) P.asIdeal Q
    ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2),
      IsDomain V ∧ IsRegularRing V ∧
        IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r ∧
        i.1 < r ∧ QP.LiesOver (Ideal.span ({t i} : Set V)) := by
  dsimp only
  let A := X.presheaf.stalk x
  let : P.asIdeal.IsPrime := P.isPrime
  let V := Localization.AtPrime P.asIdeal
  let QP := localizedNormalizationPrime (K := K) (L := L) P.asIdeal Q
  let q := Q.under A
  let : q.IsPrime :=
    (inferInstance : Q.IsPrime).comap
      (algebraMap A (integralClosure A L))
  obtain ⟨r, t, i, hdomain, hregular, hNC, hi, hqi⟩ :=
    hI.exists_localSplitChart_with_selectedBranch P hPheight q
      hQheight hIQ hQP
  have hQPq : QP.LiesOver
      (q.map (algebraMap A V)) :=
    localizedNormalizationPrime_liesOver_map_under
      (K := K) (L := L) P.asIdeal Q hQP
  have hQPi : QP.LiesOver (Ideal.span ({t i} : Set V)) := by
    rw [← hqi]
    exact hQPq
  exact ⟨r, t, i, hdomain, hregular, hNC, hi, hQPi⟩

end EtaleFundamentalGroups.Kummer

end
