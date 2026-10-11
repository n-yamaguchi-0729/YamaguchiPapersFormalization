/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyRadical
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Reductions for top local-cohomology vanishing

This file isolates two source-level inputs used at the
Hartshorne--Lichtenbaum frontier.

First, a colimit of additive groups vanishes when every object admits a
later transition whose map is zero.  Applied to the ideal-powers Ext
diagram, this reduces derived local-cohomology vanishing to a concrete
pro-zero statement about its transition maps.

Second, in a local ring, a proper ideal whose radical is not the maximal
ideal is contained in a prime strictly below the maximal ideal.  The radical
condition is essential: merely requiring the ideal itself to differ from the
maximal ideal does not exclude ideals with maximal radical.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u v

/-- In a filtered colimit of additive commutative groups, a canonical class
is zero exactly when some later transition kills its representative. -/
theorem colimit_ι_eq_zero_iff_eventually_zero
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ AddCommGrpCat.{u}) [HasColimit D]
    [PreservesColimit D (forget AddCommGrpCat)]
    (j : J) (x : D.obj j) :
    colimit.ι D j x = 0 ↔
      ∃ k : J, ∃ f : j ⟶ k, D.map f x = 0 := by
  constructor
  · intro hx
    have hx' :
        colimit.ι D j x = colimit.ι D j (0 : D.obj j) := by
      simpa using hx
    obtain ⟨k, f, _g, hfg⟩ :=
      (Concrete.colimit_rep_eq_iff_exists D x (0 : D.obj j)).mp hx'
    exact ⟨k, f, by simpa using hfg⟩
  · rintro ⟨k, f, hf⟩
    have hx' :
        colimit.ι D j x = colimit.ι D j (0 : D.obj j) :=
      (Concrete.colimit_rep_eq_iff_exists D x (0 : D.obj j)).mpr
        ⟨k, f, f, by simpa using hf⟩
    simpa using hx'

/-- A colimit of additive groups is zero if every element at every stage is
killed by some later transition. -/
theorem colimit_isZero_of_elementwise_eventually_zero
    {J : Type v} [SmallCategory J] (D : J ⥤ AddCommGrpCat.{u})
    [HasColimit D]
    (hzero : ∀ j : J, ∀ x : D.obj j,
      ∃ k : J, ∃ f : j ⟶ k, D.map f x = 0) :
    IsZero (colimit D) := by
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro j
  rw [Category.comp_id, comp_zero]
  ext x
  obtain ⟨k, f, hf⟩ := hzero j x
  change colimit.ι D j x = 0
  rw [← colimit.w D f]
  change colimit.ι D k (D.map f x) = 0
  rw [hf, map_zero]

/-- A filtered colimit of additive commutative groups is zero exactly when
every representative is killed by some later transition. -/
theorem colimit_isZero_iff_elementwise_eventually_zero
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ AddCommGrpCat.{u}) [HasColimit D]
    [PreservesColimit D (forget AddCommGrpCat)] :
    IsZero (colimit D) ↔
      ∀ j : J, ∀ x : D.obj j,
        ∃ k : J, ∃ f : j ⟶ k, D.map f x = 0 := by
  constructor
  · intro hzero j x
    apply (colimit_ι_eq_zero_iff_eventually_zero D j x).mp
    have hid : (𝟙 (colimit D)) = 0 := hzero.eq_of_src _ _
    change (𝟙 (colimit D)) (colimit.ι D j x) = 0
    rw [hid]
    rfl
  · exact colimit_isZero_of_elementwise_eventually_zero D

/-- A colimit of additive groups is zero if every stage maps trivially to
some later stage.  Individual objects of the diagram need not be zero. -/
theorem colimit_isZero_of_eventually_zero_map
    {J : Type v} [SmallCategory J] (D : J ⥤ AddCommGrpCat.{u})
    [HasColimit D]
    (hzero : ∀ j : J, ∃ k : J, ∃ f : j ⟶ k, D.map f = 0) :
    IsZero (colimit D) := by
  apply colimit_isZero_of_elementwise_eventually_zero D
  intro j x
  obtain ⟨k, f, hf⟩ := hzero j
  refine ⟨k, f, ?_⟩
  rw [hf]
  rfl

/-- The elementwise criterion for a diagram indexed by the double opposite
of the natural numbers. -/
theorem colimit_natDoubleOp_isZero_of_elementwise_eventually_zero
    (D : (ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hzero : ∀ n : ℕ, ∀ x : D.obj (op (op n)),
      ∃ m : ℕ, ∃ hnm : n ≤ m,
        D.map (homOfLE hnm).op.op x = 0) :
    IsZero (colimit D) := by
  apply colimit_isZero_of_elementwise_eventually_zero D
  rintro ⟨⟨n⟩⟩ x
  obtain ⟨m, hnm, hm⟩ := hzero n x
  exact ⟨op (op m), (homOfLE hnm).op.op, hm⟩

/-- A natural-number form of the preceding criterion for the double-opposite
indexing category used by ideal powers. -/
theorem colimit_natDoubleOp_isZero_of_eventually_zero_map
    (D : (ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hzero : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m,
      D.map (homOfLE hnm).op.op = 0) :
    IsZero (colimit D) := by
  apply colimit_isZero_of_eventually_zero_map D
  rintro ⟨⟨n⟩⟩
  obtain ⟨m, hnm, hm⟩ := hzero n
  exact ⟨op (op m), (homOfLE hnm).op.op, hm⟩

/-- Derived local cohomology vanishes if the transition maps in its
ideal-powers derived-Ext diagram are eventually zero. -/
theorem derivedLocalCohomology_isZero_of_eventually_zero_transition
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (hzero : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m,
      (derivedLocalCohomologyPowersDiagram I M i).map
        (homOfLE hnm).op.op = 0) :
    IsZero (derivedLocalCohomology I M i) := by
  exact colimit_natDoubleOp_isZero_of_eventually_zero_map
    (derivedLocalCohomologyPowersDiagram I M i) hzero

/-- It is enough to kill every individual derived-Ext class at a later power
of the support ideal. -/
theorem derivedLocalCohomology_isZero_of_elementwise_eventually_zero_transition
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (hzero : ∀ n : ℕ,
      ∀ x : CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ I ^ n)) M i,
      ∃ m : ℕ, ∃ hnm : n ≤ m,
        (derivedLocalCohomologyPowersDiagram I M i).map
          (homOfLE hnm).op.op x = 0) :
    IsZero (derivedLocalCohomology I M i) := by
  apply colimit_natDoubleOp_isZero_of_elementwise_eventually_zero
    (derivedLocalCohomologyPowersDiagram I M i)
  intro n x
  exact hzero n x

/-- Derived local cohomology is zero exactly when every derived-Ext class at
one ideal power is killed after passing to some later power. -/
theorem derivedLocalCohomology_isZero_iff_elementwise_eventually_zero_transition
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    IsZero (derivedLocalCohomology I M i) ↔
      ∀ n : ℕ,
        ∀ x : CategoryTheory.Abelian.Ext.{u}
          (ModuleCat.of R (R ⧸ I ^ n)) M i,
        ∃ m : ℕ, ∃ hnm : n ≤ m,
          (derivedLocalCohomologyPowersDiagram I M i).map
            (homOfLE hnm).op.op x = 0 := by
  constructor
  · intro hzero n x
    change IsZero
      (colimit (derivedLocalCohomologyPowersDiagram I M i)) at hzero
    let : PreservesFilteredColimitsOfSize.{0, 0}
        (forget AddCommGrpCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨k, f, hf⟩ :=
      (colimit_isZero_iff_elementwise_eventually_zero
        (derivedLocalCohomologyPowersDiagram I M i)).mp hzero
        (op (op n)) x
    rcases k with ⟨⟨m⟩⟩
    let hnm : n ≤ m := f.unop.unop.down.down
    refine ⟨m, hnm, ?_⟩
    have hf' : f = (homOfLE hnm).op.op := Subsingleton.elim _ _
    rw [← hf']
    exact hf
  · exact
      derivedLocalCohomology_isZero_of_elementwise_eventually_zero_transition
        I M i

/-- Nonvanishing of derived local cohomology is equivalently witnessed by
one derived-Ext class which survives every later ideal-power transition. -/
theorem derivedLocalCohomology_not_isZero_iff_exists_persistent_transition
    {R : Type u} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    ¬ IsZero (derivedLocalCohomology I M i) ↔
      ∃ n : ℕ,
        ∃ x : CategoryTheory.Abelian.Ext.{u}
          (ModuleCat.of R (R ⧸ I ^ n)) M i,
        ∀ m : ℕ, ∀ hnm : n ≤ m,
          (derivedLocalCohomologyPowersDiagram I M i).map
            (homOfLE hnm).op.op x ≠ 0 := by
  classical
  simpa only [not_forall, not_exists] using
    not_congr
      (derivedLocalCohomology_isZero_iff_elementwise_eventually_zero_transition
        I M i)

/-- A Noetherian local ring of dimension `d` admits a list of exactly `d`
elements whose generated ideal has maximal radical.  For `d = 0`, the list
is empty and the assertion says that the nilradical is the maximal ideal. -/
theorem exists_ofList_radical_eq_maximalIdeal_of_ringKrullDim_eq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ)
    (hdim : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∃ xs : List R,
      xs.length = d ∧
      (Ideal.ofList xs).radical = IsLocalRing.maximalIdeal R := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hmHeight : m.height = (d : ℕ∞) := by
    apply WithBot.coe_injective
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans hdim
  obtain ⟨J, hJm, hJrank, hJheight⟩ :=
    Ideal.exists_spanRank_eq_and_height_eq m
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hJfg : (J : Submodule R R).FG := IsNoetherian.noetherian J
  have hJrank' := hJrank
  rw [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr hJfg, hmHeight] at hJrank'
  have hJfinrank : J.spanFinrank = d := by
    exact_mod_cast hJrank'
  have hJradical : J.radical = m := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le
        ⟨hJm, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩
    · refine le_sInf ?_
      intro P hP
      let : P.IsPrime := hP.2
      have hPm : P ≤ m := IsLocalRing.le_maximalIdeal_of_isPrime P
      have hPheight : P.height = m.height := by
        apply le_antisymm (Ideal.height_mono hPm)
        calc
          m.height = J.height := hJheight.symm
          _ ≤ P.height := Ideal.height_mono hP.1
      have hPdim : ((P.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
        rw [hPheight]
        exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      have hPmax : P = m :=
        (Ideal.height_eq_ringKrullDim_iff (I := P)).mp hPdim
      exact hPmax.ge
  obtain ⟨s, hscard, hsJ⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hJfg
  refine ⟨s.toList, ?_, ?_⟩
  · simpa only [Finset.length_toList, hJfinrank] using hscard
  · have hofList : Ideal.ofList s.toList = J := by
      unfold Ideal.ofList
      simpa using hsJ
    rw [hofList, hJradical]

/-- In exact dimension `d`, maximal-support derived local cohomology can be
computed using an ideal generated by a list of exactly `d` parameters. -/
theorem exists_derivedLocalCohomology_ofList_iso_maximalIdeal_of_ringKrullDim_eq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ)
    (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (M : ModuleCat.{u} R) :
    ∃ xs : List R,
      xs.length = d ∧
      (Ideal.ofList xs).radical = IsLocalRing.maximalIdeal R ∧
      Nonempty
        (derivedLocalCohomology (Ideal.ofList xs) M d ≅
          derivedLocalCohomology (IsLocalRing.maximalIdeal R) M d) := by
  obtain ⟨xs, hlength, hradical⟩ :=
    exists_ofList_radical_eq_maximalIdeal_of_ringKrullDim_eq d hdim
  have hmaxRadical :
      (IsLocalRing.maximalIdeal R).radical =
        IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime.isRadical.radical
  refine ⟨xs, hlength, hradical, ?_⟩
  exact
    ⟨derivedLocalCohomologyIsoOfSameRadical
      (hradical.trans hmaxRadical.symm) M d⟩

/-- Derived local-cohomology vanishing can be checked after replacing the
support ideal by its radical. -/
theorem derivedLocalCohomology_isZero_iff_radical
    {R : Type u} [CommRing R] [IsNoetherian R R]
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    IsZero (derivedLocalCohomology I M i) ↔
      IsZero (derivedLocalCohomology I.radical M i) :=
  (derivedLocalCohomologyIsoOfSameRadical
    (Ideal.radical_idem I).symm M i).isZero_iff

/-- A proper ideal in a local ring with nonmaximal radical is contained in a
prime ideal strictly below the maximal ideal. -/
theorem exists_prime_over_lt_maximalIdeal_of_radical_ne
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤)
    (hradical : I.radical ≠ IsLocalRing.maximalIdeal R) :
    ∃ P : Ideal R,
      I ≤ P ∧ P.IsPrime ∧ P < IsLocalRing.maximalIdeal R := by
  have hmaxPrime : (IsLocalRing.maximalIdeal R).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have hImax : I ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hI
  by_contra hexists
  have hall : ∀ P : Ideal R, I ≤ P → P.IsPrime →
      P = IsLocalRing.maximalIdeal R := by
    intro P hIP hP
    have hPmax : P ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal_of_isPrime P
    exact le_antisymm hPmax <| by
      by_contra hnotle
      have hne : P ≠ IsLocalRing.maximalIdeal R := by
        intro heq
        exact hnotle heq.ge
      have hlt : P < IsLocalRing.maximalIdeal R :=
        lt_of_le_of_ne hPmax hne
      exact hexists ⟨P, hIP, hP, hlt⟩
  apply hradical
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · exact sInf_le ⟨hImax, hmaxPrime⟩
  · refine le_sInf ?_
    intro P hP
    rw [hall P hP.1 hP.2]

/-- For a proper ideal of a local ring, having nonmaximal radical is
equivalent to the existence of a prime over it strictly below the maximal
ideal. -/
theorem radical_ne_maximalIdeal_iff_exists_prime_over_lt
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) :
    I.radical ≠ IsLocalRing.maximalIdeal R ↔
      ∃ P : Ideal R,
        I ≤ P ∧ P.IsPrime ∧ P < IsLocalRing.maximalIdeal R := by
  constructor
  · exact exists_prime_over_lt_maximalIdeal_of_radical_ne I hI
  · rintro ⟨P, hIP, hP, hPmax⟩ hradical
    have hmaxP : IsLocalRing.maximalIdeal R ≤ P := by
      rw [← hradical]
      exact hP.radical_le_iff.mpr hIP
    exact (not_le_of_gt hPmax) hmaxP

end EtaleFundamentalGroups

end
