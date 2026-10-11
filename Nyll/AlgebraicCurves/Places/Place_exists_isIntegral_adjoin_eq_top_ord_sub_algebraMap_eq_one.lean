/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Places.Place_le_ord_iff_mem_pow_fiberCenter
import Nyll.AlgebraicCurves.Places.Place_min_ord_le_ord_add
import Nyll.AlgebraicCurves.Divisors.Maps

/-!
# Place exists is Integral adjoin eq top ord sub algebra Map eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one

noncomputable section

open _root_.AlgebraicCurve
open _root_.IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace AdaptedPrimitiveProof
open _root_.AlgebraicCurve

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    rw [zpow_natCast]; push_cast at h; exact h
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_eq_zero_of_mem_of_inv_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hfi : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have h1 := ord_nonneg_of_mem v hf
  have h2 := ord_nonneg_of_mem v hfi
  rw [v.ord_inv] at h2
  omega

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · simp [hc]
  exact ord_eq_zero_of_mem_of_inv_mem v (v.algebraMap_mem' c)
    (by rw [← map_inv₀]; exact v.algebraMap_mem' c⁻¹)

theorem ord_neg (v : Place K F) (a : F) : v.ord (-a) = v.ord a := by
  by_cases ha : a = 0
  · rw [ha, neg_zero]
  rw [neg_eq_neg_one_mul, v.ord_mul (by norm_num) ha,
    show (-1 : F) = algebraMap K F (-1) by simp, ord_algebraMap, zero_add]

theorem ord_add_eq_of_lt (v : Place K F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  have hab : a + b ≠ 0 := by
    intro h0
    have : a = -b := eq_neg_of_add_eq_zero_left h0
    rw [this, ord_neg] at h
    exact lt_irrefl _ h
  refine ⟨hab, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt
    have h2 := Place.min_ord_le_ord_add v hab (neg_ne_zero.mpr hb) (by rwa [add_neg_cancel_right])
    rw [add_neg_cancel_right, ord_neg] at h2
    have : min (v.ord (a + b)) (v.ord b) > v.ord a := lt_min hlt h
    omega
  · have h1 := Place.min_ord_le_ord_add v ha hb hab
    rwa [min_eq_left h.le] at h1

theorem ord_add_eq_of_lt' (v : Place K F) {a b : F} (ha : a ≠ 0)
    (h : b = 0 ∨ v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  rcases h with rfl | h
  · rw [add_zero]; exact ⟨ha, rfl⟩
  by_cases hb : b = 0
  · rw [hb, add_zero]; exact ⟨ha, rfl⟩
  exact ord_add_eq_of_lt v ha hb h

end PlaceFacts

section Fibre

variable {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

variable (v : Place K E)

/-- A base-field constant viewed in the integral closure at the chosen place. -/
def kC (a : K) : Place.integralClosureAt F v :=
  algebraMap v.toValuationSubring (Place.integralClosureAt F v) ⟨algebraMap K E a,
    v.algebraMap_mem' a⟩
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in
theorem algebraMap_kC (a : K) :
    algebraMap (Place.integralClosureAt F v) F (kC (F := F) v a) = algebraMap K F a := by
  rw [kC, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E F]
  rfl

variable {v}

theorem exists_uniformizer_mem {w : Place K F} (hw : w.restrict E = v) :
    ∃ π : Place.integralClosureAt F v,
      π ∈ (Place.fiberCenter F v hw).asIdeal ∧
      w.ord (algebraMap (Place.integralClosureAt F v) F π) = 1 := by
  set P := (Place.fiberCenter F v hw).asIdeal with hP
  have hP0 : P ≠ ⊥ := (Place.fiberCenter F v hw).ne_bot
  have hP1 : P ≠ ⊤ := (Place.fiberCenter F v hw).isPrime.ne_top
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP0 hP1 1
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (zero_mem _)
  rw [pow_one] at hπ1
  refine ⟨π, hπ1, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt
    have h2 : ((2 : ℕ) : ℤ) ≤ w.ord (algebraMap _ F π) := by push_cast; omega
    exact hπ2 ((Place.le_ord_iff_mem_pow_fiberCenter hw hπ0 2).mp h2)
  · have := (Place.le_ord_iff_mem_pow_fiberCenter hw hπ0 1).mpr (by rwa [pow_one])
    exact_mod_cast this

theorem two_le_ord_of_mem_sq {w : Place K F} (hw : w.restrict E = v)
    {r : Place.integralClosureAt F v} (hr : r ∈ (Place.fiberCenter F v hw).asIdeal ^ 2) :
    algebraMap (Place.integralClosureAt F v) F r = 0 ∨
      2 ≤ w.ord (algebraMap (Place.integralClosureAt F v) F r) := by
  by_cases hr0 : r = 0
  · left; rw [hr0, map_zero]
  right
  exact_mod_cast (Place.le_ord_iff_mem_pow_fiberCenter hw hr0 2).mpr hr

theorem one_le_ord_of_mem {w : Place K F} (hw : w.restrict E = v)
    {r : Place.integralClosureAt F v} (hr : r ∈ (Place.fiberCenter F v hw).asIdeal) :
    algebraMap (Place.integralClosureAt F v) F r = 0 ∨
      1 ≤ w.ord (algebraMap (Place.integralClosureAt F v) F r) := by
  by_cases hr0 : r = 0
  · left; rw [hr0, map_zero]
  right
  exact_mod_cast (Place.le_ord_iff_mem_pow_fiberCenter hw hr0 1).mpr (by rwa [pow_one])

end Fibre

section Construction

variable {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Infinite K] [FiniteDimensional E F] [Algebra.IsSeparable E F]

theorem main (w : Place K F) :
    ∃ θ : F, IsIntegral (w.restrict E).toValuationSubring θ ∧
      IntermediateField.adjoin E ({θ} : Set F) = ⊤ ∧
      ∃ c : K, w.ord (θ - algebraMap K F c) = 1 ∧
        ∀ w' : Place K F, w'.restrict E = w.restrict E → w' ≠ w →
          w'.ord (θ - algebraMap K F c) = 0 := by
  classical
  set v : Place K E := w.restrict E with hv
  set S : Finset (Place K F) := v.fiberOver F with hS
  have hmemS : ∀ {w' : Place K F}, w' ∈ S ↔ w'.restrict E = v := fun {w'} => Place.mem_fiberOver v
  have hwS : w ∈ S := hmemS.mpr rfl
  let idx : Place K F → ℕ := fun w' => if h : w' ∈ S then (S.equivFin ⟨w', h⟩ : ℕ) else 0
  let c : Place K F → K := fun w' => Infinite.natEmbedding K (idx w')
  have hc_inj : ∀ w₁ ∈ S, ∀ w₂ ∈ S, c w₁ = c w₂ → w₁ = w₂ := by
    intro w₁ h₁ w₂ h₂ h
    have h' : idx w₁ = idx w₂ := (Infinite.natEmbedding K).injective h
    simp only [idx, dite_eq_left h₁, dite_eq_left h₂, Fin.val_inj] at h'
    exact Subtype.ext_iff.mp ((S.equivFin).injective h')
  let P : Place K F → Ideal (Place.integralClosureAt F v) := fun w' =>
    if h : w' ∈ S then (Place.fiberCenter F v (hmemS.mp h)).asIdeal else ⊥
  have hP : ∀ {w'} (h : w' ∈ S), P w' = (Place.fiberCenter F v (hmemS.mp h)).asIdeal :=
    fun h => dite_eq_left h
  let π : Place K F → (Place.integralClosureAt F v) := fun w' =>
    if h : w' ∈ S then (exists_uniformizer_mem (F := F) (hmemS.mp h)).choose else 0
  have hπ : ∀ {w'} (h : w' ∈ S), π w' ∈ (Place.fiberCenter F v (hmemS.mp h)).asIdeal ∧
      w'.ord (algebraMap (Place.integralClosureAt F v) F (π w')) = 1 := by
    intro w' h
    simp only [π, dite_eq_left h]
    exact (exists_uniformizer_mem (F := F) (hmemS.mp h)).choose_spec
  obtain ⟨θ₁, hθ₁⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) P (fun _ => 2)
    (fun w' h => by
      rw [hP h]
      exact Ideal.prime_of_isPrime (Place.fiberCenter F v (hmemS.mp h)).ne_bot
        (Place.fiberCenter F v (hmemS.mp h)).isPrime)
    (fun w₁ h₁ w₂ h₂ hne heq => by
      rw [hP h₁, hP h₂] at heq
      exact hne (Place.eq_of_fiberCenter_eq (hmemS.mp h₁) (hmemS.mp h₂)
        (IsDedekindDomain.HeightOneSpectrum.ext heq)))
    (fun i => kC v (c i) + π i)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E F
  have hαalg : IsAlgebraic v.toValuationSubring α :=
    (IsFractionRing.isAlgebraic_iff v.toValuationSubring E F).mpr (Algebra.IsAlgebraic.isAlgebraic
      α)
  obtain ⟨d, hd0, hdα⟩ := hαalg.exists_integral_multiple
  set θ₀ : (Place.integralClosureAt F v) := ⟨d • α, hdα⟩ with hθ₀
  have hθ₀F : algebraMap (Place.integralClosureAt F v) F θ₀ = (d : E) • α := rfl
  have hdE : (d : E) ≠ 0 := by
    intro h; apply hd0; exact Subtype.ext h
  have hα_mem : ∀ M : IntermediateField E F, algebraMap (Place.integralClosureAt F v) F θ₀ ∈ M → M
    = ⊤ := by
    intro M hM
    rw [hθ₀F] at hM
    have hαM : α ∈ M := by
      have : α = (d : E)⁻¹ • ((d : E) • α) := by rw [smul_smul, inv_mul_cancel₀ hdE, one_smul]
      rw [this]; exact M.smul_mem hM
    have : IntermediateField.adjoin E {α} ≤ M := IntermediateField.adjoin_simple_le_iff.mpr hαM
    rw [hα] at this
    exact top_le_iff.mp this
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Place.maximalIdeal_ne_bot v)
  set mC : (Place.integralClosureAt F v) := algebraMap v.toValuationSubring
    (Place.integralClosureAt F v) m with hmC
  have hmC_mem : ∀ {w'} (h : w' ∈ S), mC ∈ (Place.fiberCenter F v (hmemS.mp h)).asIdeal := by
    intro w' h
    have := Place.fiberCenter_liesOver (F' := F) (hmemS.mp h)
    exact (Ideal.mem_of_liesOver (Place.fiberCenter F v (hmemS.mp h)).asIdeal
      (maximalIdeal v.toValuationSubring) m).mp hm
  let θμ : K → (Place.integralClosureAt F v) := fun μ => θ₁ + mC ^ 2 * kC v μ * θ₀
  have hkC : ∀ a : K, algebraMap (Place.integralClosureAt F v) F (kC v a) = algebraMap E F
    (algebraMap K E a) := by
    intro a; rw [algebraMap_kC, IsScalarTower.algebraMap_apply K E F]
  have : Finite (IntermediateField E F) :=
    Field.finite_intermediateField_of_exists_primitive_element E F ⟨α, hα⟩
  obtain ⟨μ, μ', hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun μ : K => IntermediateField.adjoin E ({algebraMap (Place.integralClosureAt F v) F (θμ μ)} :
      Set F))
  have hprim : IntermediateField.adjoin E ({algebraMap (Place.integralClosureAt F v) F (θμ μ)} :
    Set F) = ⊤ := by
    apply hα_mem
    set M := IntermediateField.adjoin E ({algebraMap (Place.integralClosureAt F v) F (θμ μ)} : Set
      F) with hM
    have h1 : algebraMap (Place.integralClosureAt F v) F (θμ μ) ∈ M :=
      IntermediateField.mem_adjoin_simple_self E _
    have h2 : algebraMap (Place.integralClosureAt F v) F (θμ μ') ∈ M := by
      have : algebraMap (Place.integralClosureAt F v) F (θμ μ') ∈
          IntermediateField.adjoin E ({algebraMap (Place.integralClosureAt F v) F (θμ μ')} : Set F)
            :=
        IntermediateField.mem_adjoin_simple_self E _
      rwa [← heq] at this
    have hdiff : algebraMap (Place.integralClosureAt F v) F (θμ μ) - algebraMap
      (Place.integralClosureAt F v) F (θμ μ') =
        ((m : E) ^ 2 * algebraMap K E (μ - μ')) • algebraMap (Place.integralClosureAt F v) F θ₀ :=
          by
      have hmF : algebraMap (Place.integralClosureAt F v) F mC = algebraMap E F (m : E) := rfl
      simp only [θμ, map_add, map_mul, map_pow, hkC, hmF, Algebra.smul_def, map_sub]
      ring
    have hlam : (m : E) ^ 2 * algebraMap K E (μ - μ') ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ ?_) ?_
      · intro h; apply hm0; exact Subtype.ext h
      · rw [map_ne_zero_iff _ (algebraMap K E).injective]; exact sub_ne_zero.mpr hne
    have : algebraMap (Place.integralClosureAt F v) F θ₀ = ((m : E) ^ 2 * algebraMap K E (μ -
      μ'))⁻¹ •
        (algebraMap (Place.integralClosureAt F v) F (θμ μ) - algebraMap (Place.integralClosureAt F
          v) F (θμ μ')) := by
      rw [hdiff, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [this]
    exact M.smul_mem (M.sub_mem h1 h2)
  have hshape : ∀ {w'} (h : w' ∈ S),
      algebraMap (Place.integralClosureAt F v) F (θμ μ) - algebraMap K F (c w) =
        (algebraMap (Place.integralClosureAt F v) F (θ₁ - (kC v (c w') + π w') + mC ^ 2 * kC v μ *
          θ₀) +
          algebraMap (Place.integralClosureAt F v) F (π w')) + algebraMap K F (c w' - c w) := by
    intro w' h
    simp only [θμ, map_add, map_sub, map_mul, map_pow, hkC, ← IsScalarTower.algebraMap_apply K E F]
    ring
  have hcore : ∀ {w'} (h : w' ∈ S),
      algebraMap (Place.integralClosureAt F v) F (θ₁ - (kC v (c w') + π w') + mC ^ 2 * kC v μ * θ₀)
        +
          algebraMap (Place.integralClosureAt F v) F (π w') ≠ 0 ∧
      w'.ord (algebraMap (Place.integralClosureAt F v) F (θ₁ - (kC v (c w') + π w') + mC ^ 2 * kC v
        μ * θ₀) +
          algebraMap (Place.integralClosureAt F v) F (π w')) = 1 := by
    intro w' h
    have hw' : w'.restrict E = v := hmemS.mp h
    set r : (Place.integralClosureAt F v) := θ₁ - (kC v (c w') + π w') + mC ^ 2 * kC v μ * θ₀ with
      hr
    have hrmem : r ∈ (Place.fiberCenter F v hw').asIdeal ^ 2 := by
      refine Ideal.add_mem _ ?_ ?_
      · have := hθ₁ w' h
        rwa [hP h] at this
      · rw [mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hmC_mem h) 2)
    have hr2 := two_le_ord_of_mem_sq hw' hrmem
    obtain ⟨-, hπ1⟩ := hπ h
    have hπ0 : algebraMap (Place.integralClosureAt F v) F (π w') ≠ 0 := by
      intro h0; rw [h0] at hπ1; simp at hπ1
    have := ord_add_eq_of_lt' w' hπ0 (b := algebraMap (Place.integralClosureAt F v) F r)
      (hr2.imp id fun h2 => by omega)
    rw [add_comm] at this
    exact ⟨this.1, this.2.trans hπ1⟩
  refine ⟨algebraMap (Place.integralClosureAt F v) F (θμ μ), (θμ μ).2, hprim, c w, ?_, ?_⟩
  · rw [hshape hwS, sub_self, map_zero, add_zero]
    exact (hcore hwS).2
  · intro w' hw'v hne'
    have h : w' ∈ S := hmemS.mpr hw'v
    rw [hshape h]
    have hcne : c w' - c w ≠ 0 := by
      intro h0
      exact hne' (hc_inj w' h w hwS (sub_eq_zero.mp h0))
    have hc0 : algebraMap K F (c w' - c w) ≠ 0 := by
      rwa [map_ne_zero_iff _ (algebraMap K F).injective]
    have := ord_add_eq_of_lt w' hc0 (hcore h).1
      (by rw [ord_algebraMap, (hcore h).2]; norm_num)
    rw [add_comm] at this
    rw [this.2, ord_algebraMap]

end Construction

end AlgebraicCurve.AdaptedPrimitiveProof

theorem _root_.AlgebraicCurve.Place.exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one
    {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
    [IsScalarTower K E F] [Infinite K] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (w : AlgebraicCurve.Place K F) :
    ∃ θ : F, IsIntegral (w.restrict E).toValuationSubring θ ∧
      IntermediateField.adjoin E ({θ} : Set F) = ⊤ ∧
      ∃ c : K, w.ord (θ - algebraMap K F c) = 1 ∧
        ∀ w' : AlgebraicCurve.Place K F, w'.restrict E = w.restrict E → w' ≠ w →
          w'.ord (θ - algebraMap K F c) = 0 :=
  AlgebraicCurve.AdaptedPrimitiveProof.main w
end
end AlgebraicCurves.Places.Proofs.Place_exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
