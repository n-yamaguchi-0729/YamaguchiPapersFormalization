/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.KrullDimension.Zero
import Nyll.SchemeTheory.LocalGeometry.HeightTwo.RegularParameters

/-!
# An unconstrained regular parameter pair in dimension two

For the finite-normalization argument we do not need to prescribe the first
parameter.  In a two-dimensional regular local domain, lift any basis of the
cotangent space.  The two lifts generate the maximal ideal and form a regular
sequence.

The only delicate point is the second regularity condition.  After quotienting
by the first lift, the maximal ideal is principal.  If its generator were a
zero-divisor, Krull intersection would make it nilpotent and force the quotient
to have dimension zero, contradicting the principal-ideal dimension bound.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open Module
open RingTheory.Sequence

universe u

/-- In a positive-dimensional Noetherian local ring with principal maximal
ideal, a generator of the maximal ideal is a non-zero-divisor. -/
private theorem isSMulRegular_of_span_singleton_eq_maximalIdeal_of_not_krullDimLE_zero
    {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {y : S} (hspan : Ideal.span {y} = maximalIdeal S)
    (hdim : ¬ Ring.KrullDimLE 0 S) :
    IsSMulRegular S y := by
  classical
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  have hya : y * a = 0 := by
    simpa only [smul_eq_mul] using ha
  by_contra ha0
  have hex : ∃ n : ℕ, a ∉ maximalIdeal S ^ n := by
    by_contra hall
    push Not at hall
    have haInf : a ∈ ⨅ n : ℕ, maximalIdeal S ^ n :=
      Ideal.mem_iInf.mpr hall
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing
      (maximalIdeal S) (maximalIdeal.isMaximal S).ne_top] at haInf
    exact ha0 (Ideal.mem_bot.mp haInf)
  let n := Nat.find hex
  have hn : a ∉ maximalIdeal S ^ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hn
    simp [hn0]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have haPow : a ∈ maximalIdeal S ^ k := by
    by_contra hak
    have hnk : n ≤ k := Nat.find_min' hex hak
    omega
  have haDiv : y ^ k ∣ a := by
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hspan]
    exact haPow
  obtain ⟨c, hac⟩ := haDiv
  have hc : c ∉ maximalIdeal S := by
    intro hc
    apply hn
    rw [hk, ← hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [← hspan, Ideal.mem_span_singleton] at hc
    obtain ⟨d, hcd⟩ := hc
    refine ⟨d, ?_⟩
    rw [hac, hcd, pow_succ]
    ac_rfl
  have hcUnit : IsUnit c := by
    rw [IsLocalRing.mem_maximalIdeal] at hc
    exact not_not.mp hc
  have hyPowMul : y ^ (k + 1) * c = 0 := by
    calc
      y ^ (k + 1) * c = y * (y ^ k * c) := by
        rw [pow_succ]
        ac_rfl
      _ = 0 := by simpa only [hac] using hya
  have hyPow : y ^ (k + 1) = 0 := by
    apply hcUnit.mul_right_cancel
    simpa only [zero_mul] using hyPowMul
  have hyNil : IsNilpotent y := ⟨k + 1, hyPow⟩
  have hmax_le_nil : maximalIdeal S ≤ nilradical S := by
    rw [← hspan]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change IsNilpotent y
    exact hyNil
  have hnil : nilradical S = maximalIdeal S :=
    le_antisymm (nilradical_le_prime (maximalIdeal S)) hmax_le_nil
  have hnilMax : (nilradical S).IsMaximal :=
    hnil ▸ maximalIdeal.isMaximal S
  let : (nilradical S).IsMaximal := hnilMax
  exact hdim (Ring.KrullDimLE.of_isMaximal_nilradical S)

/-- In a two-dimensional Noetherian local domain, two minimal generators of
the maximal ideal form a regular sequence. -/
theorem isRegular_pair_of_finrank_cotangentSpace_eq_two_of_span_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    {x y : R}
    (hfin : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (hspan : Ideal.ofList [x, y] = maximalIdeal R) :
    IsRegular R [x, y] := by
  have hxMem : x ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  have hyMem : y ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  have hx : x ≠ 0 := by
    intro hx
    have hprincipal : (maximalIdeal R).IsPrincipal := by
      refine ⟨y, ?_⟩
      change maximalIdeal R = Ideal.span {y}
      simpa [hx] using hspan.symm
    have hle :
        Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 :=
      IsLocalRing.finrank_cotangentSpace_le_one_iff.mpr hprincipal
    omega
  have hxRegular : IsSMulRegular R x := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro a ha
    have hxa : x * a = 0 := by
      simpa only [smul_eq_mul] using ha
    exact (mul_eq_zero.mp hxa).resolve_left hx
  let I : Ideal R := Ideal.span {x}
  let S := R ⧸ I
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact hxMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let ybar : S := Ideal.Quotient.mk I y
  have hspanS : Ideal.span {ybar} = maximalIdeal S := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← hspan, Ideal.map_ofList]
    simp [I, ybar]
    rfl
  have hdimS : ¬ Ring.KrullDimLE 0 S := by
    intro hzero
    have hzero' : ringKrullDim S = 0 :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hzero
    have hspanFin : I.spanFinrank = 1 := by
      change (Submodule.span R {x}).spanFinrank = 1
      exact Submodule.spanFinrank_singleton hx
    have hIJac : I ≤ Ring.jacobson R := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal R]
      exact hIle
    have hle :=
      ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I hIJac
    rw [hdim, hzero', hspanFin] at hle
    norm_num at hle
  have hyRegularS : IsSMulRegular S ybar :=
    isSMulRegular_of_span_singleton_eq_maximalIdeal_of_not_krullDimLE_zero
      hspanS hdimS
  have hyRegular : IsSMulRegular (QuotSMulTop x R) y := by
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro a ha
    rw [Submodule.mem_smul_pointwise_iff_exists] at ha ⊢
    obtain ⟨c, -, hc⟩ := ha
    have hprod : y * a ∈ I := by
      change y * a ∈ Ideal.span {x}
      rw [show y * a = x * c by
        simpa only [smul_eq_mul] using hc.symm]
      exact (Ideal.span {x}).mul_mem_right c
        (Ideal.mem_span_singleton_self x)
    have hzero : ybar * Ideal.Quotient.mk I a = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hprod
    have haZero : Ideal.Quotient.mk I a = 0 :=
      hyRegularS.right_eq_zero_of_smul (by
        simpa only [smul_eq_mul] using hzero)
    have haMem : a ∈ Ideal.span ({x} : Set R) :=
      Ideal.Quotient.eq_zero_iff_mem.mp haZero
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp haMem
    refine ⟨d, Submodule.mem_top, ?_⟩
    simpa only [smul_eq_mul] using hd.symm
  have hweak : IsWeaklyRegular R [x, y] := by
    apply (isWeaklyRegular_cons_iff R x [y]).mpr
    refine ⟨hxRegular, ?_⟩
    exact (isWeaklyRegular_singleton_iff (QuotSMulTop x R) y).mpr hyRegular
  have hmem : ∀ r ∈ [x, y], r ∈ maximalIdeal R := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hxMem
    · exact hyMem
  exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal (L := R) hmem hweak

/-- A two-dimensional regular local domain admits a regular pair generating
its maximal ideal, with no prescribed first parameter. -/
theorem exists_regular_pair_of_finrank_cotangentSpace_eq_two_unconstrained
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hfin : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    ∃ x y : R, IsRegular R [x, y] ∧
      Ideal.ofList [x, y] = maximalIdeal R := by
  classical
  let m : Ideal R := maximalIdeal R
  let b : Basis (Fin 2) (ResidueField R) (CotangentSpace R) :=
    Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hfin
  obtain ⟨x', hx'⟩ := m.toCotangent_surjective (b 0)
  obtain ⟨y', hy'⟩ := m.toCotangent_surjective (b 1)
  let x : R := x'
  let y : R := y'
  let v : Fin 2 → CotangentSpace R :=
    ![m.toCotangent x', m.toCotangent y']
  have hv : v = b := by
    funext i
    fin_cases i
    · simpa [v] using hx'
    · simpa [v] using hy'
  have hvSpan :
      Submodule.span (ResidueField R) (Set.range v) = ⊤ := by
    rw [hv]
    exact b.span_eq
  have himage :
      m.toCotangent '' ({x', y'} : Set m) = Set.range v := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_range, v]
    constructor
    · rintro ⟨w, rfl | rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨x', Or.inl rfl, rfl⟩
      · exact ⟨y', Or.inr rfl, rfl⟩
  have hsubtypeSpan : Submodule.span R ({x', y'} : Set m) = ⊤ := by
    apply (CotangentSpace.span_image_eq_top_iff (R := R)).mp
    rw [himage]
    exact hvSpan
  have hmapSpan :
      (Submodule.span R ({x', y'} : Set m)).map m.subtype = m := by
    rw [hsubtypeSpan, Submodule.map_top, Submodule.range_subtype]
  have hspanSet : Ideal.span ({x, y} : Set R) = maximalIdeal R := by
    change Ideal.span ({x, y} : Set R) = m
    rw [← hmapSpan, Submodule.map_span]
    congr 1
    ext z
    simp [x, y]
  have hspan : Ideal.ofList [x, y] = maximalIdeal R := by
    change Ideal.span {r | r ∈ [x, y]} = maximalIdeal R
    rw [show {r | r ∈ [x, y]} = ({x, y} : Set R) by ext; simp]
    exact hspanSet
  exact ⟨x, y,
    isRegular_pair_of_finrank_cotangentSpace_eq_two_of_span_eq
      hfin hdim hspan,
    hspan⟩

/-- A height-two localization of a regular domain has an unconstrained
regular pair of parameters. -/
theorem exists_regular_pair_localizationAtPrime_of_height_eq_two_unconstrained
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2) :
    ∃ x y : Localization.AtPrime P,
      IsRegular (Localization.AtPrime P) [x, y] ∧
      Ideal.ofList [x, y] =
        maximalIdeal (Localization.AtPrime P) := by
  let R := Localization.AtPrime P
  have hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim R = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P R
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  have hfin :
      Module.finrank (ResidueField R) (CotangentSpace R) = 2 := by
    have hreg :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdim] at hreg
    exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hreg)
  exact exists_regular_pair_of_finrank_cotangentSpace_eq_two_unconstrained
    hfin hdim

end EtaleFundamentalGroups
