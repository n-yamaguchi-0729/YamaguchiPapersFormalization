/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_natCard_place_ord_sub_pos_le_natCard_doubleCoset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Index

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Places.Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois

/-!
# Nat Card place ord sub pos le nat Card double Coset
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.NatCard_place_ord_sub_pos_le_natCard_doubleCoset
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open _root_.AlgebraicCurve
open scoped IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace PlacesLeDoubleCoset
open _root_.AlgebraicCurve

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

theorem apply_eq_self_of_mem_adjoin (ψ : L →ₐ[K] L) (t : L) (hψ : ψ t = t) {x : L}
    (hx : x ∈ K⟮t⟯) : ψ x = x := by
  let S : IntermediateField K L := (AlgHom.equalizer ψ (AlgHom.id K L)).toIntermediateField
    (fun y hy => by
      rw [AlgHom.mem_equalizer] at hy ⊢
      simp only [AlgHom.coe_id, id_eq] at hy ⊢
      rw [map_inv₀, hy])
  have hle : K⟮t⟯ ≤ S := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change t ∈ AlgHom.equalizer ψ (AlgHom.id K L)
    rw [AlgHom.mem_equalizer]
    simpa using hψ
  have := hle hx
  change x ∈ AlgHom.equalizer ψ (AlgHom.id K L) at this
  rw [AlgHom.mem_equalizer] at this
  simpa using this

theorem algHom_apply_algebraMap (t : L) (E : IntermediateField K⟮t⟯ L) (x : E) (hx : (x : L) = t)
    (ψ : E →ₐ[K] L) (hψ : ψ x = t) (l : K⟮t⟯) : ψ (algebraMap K⟮t⟯ E l) = l := by
  let θ : K⟮t⟯ →ₐ[K] L := ψ.comp (IsScalarTower.toAlgHom K K⟮t⟯ E)
  have hgen : ∀ (z : L) (hz : z ∈ ({t} : Set L)),
      θ ⟨z, IntermediateField.subset_adjoin _ _ hz⟩ =
        (IntermediateField.val K⟮t⟯) ⟨z, IntermediateField.subset_adjoin _ _ hz⟩ := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    have hz' : (⟨z, IntermediateField.subset_adjoin _ _ (by rw [hz]; rfl)⟩ : K⟮t⟯) =
        ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ := Subtype.ext hz
    rw [hz']
    change ψ (algebraMap K⟮t⟯ E ⟨t, _⟩) = t
    have : algebraMap K⟮t⟯ E ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ = x := by
      apply Subtype.ext
      rw [hx]
      rfl
    rw [this, hψ]
  have hθ : θ = IntermediateField.val K⟮t⟯ := IntermediateField.adjoin_algHom_ext K hgen
  exact congrArg (fun φ : K⟮t⟯ →ₐ[K] L => φ l) hθ

theorem isIntegral_of_apply_eq_sub (t : L) [FiniteDimensional K⟮t⟯ L]
    (E : IntermediateField K⟮t⟯ L) (x : E) (hx : (x : L) = t)
    (ψ : E →ₐ[K] L) (hψ : ψ x = t) : ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral K⟮t⟯ y := IsIntegral.of_finite K⟮t⟯ y
  refine ⟨(minpoly K⟮t⟯ y).map (algebraMap K⟮t⟯ E), (minpoly.monic hy).map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : ψ.toRingHom.comp (algebraMap K⟮t⟯ E) = algebraMap K⟮t⟯ L := by
    ext e
    exact algHom_apply_algebraMap t E x hx ψ hψ e
  rw [hcomp]
  exact minpoly.aeval K⟮t⟯ y

theorem finite_doubleCosetQuotient {Γ₀ : Type*} [Group Γ₀] (Γ Kst : Subgroup Γ₀) [Γ.FiniteIndex] :
    Finite (DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀)) := by
  have : Finite (Γ₀ ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  have : Finite (Quotient (QuotientGroup.rightRel Γ)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ).symm
  let π : Quotient (QuotientGroup.rightRel Γ) → DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀) :=
    Quotient.lift (fun a => DoubleCoset.mk Γ Kst a) (by
      intro a b hab
      have hab' : b * a⁻¹ ∈ Γ := QuotientGroup.rightRel_apply.mp hab
      change DoubleCoset.mk Γ Kst a = DoubleCoset.mk Γ Kst b
      rw [DoubleCoset.eq]
      exact ⟨b * a⁻¹, hab', 1, Kst.one_mem, by group⟩)
  refine Finite.of_surjective π ?_
  intro q
  obtain ⟨γ, rfl⟩ : ∃ γ, DoubleCoset.mk Γ Kst γ = q := ⟨q.out, DoubleCoset.out_eq' (H := Γ) (K :=
    Kst) q⟩
  exact ⟨Quotient.mk _ γ, rfl⟩

end AlgebraicCurve.PlacesLeDoubleCoset

open _root_.AlgebraicCurve
open scoped IntermediateField

open NatCard_place_ord_sub_pos_le_natCard_doubleCoset.AlgebraicCurve.PlacesLeDoubleCoset in
theorem _root_.AlgebraicCurve.natCard_place_ord_sub_pos_le_natCard_doubleCoset
    (K : Type*) [Field K] [IsAlgClosed K] {L : Type*} [Field L] [Algebra K L]
    (t : L) (hfin : FiniteDimensional K⟮t⟯ L) (hgal : IsGalois K⟮t⟯ L)
    {Γ₀ : Type*} [Group Γ₀] (σ : Γ₀ →* (L ≃ₐ[K⟮t⟯] L)) (hσ : Function.Surjective σ)
    (Γ Kst : Subgroup Γ₀) [Γ.FiniteIndex]
    (E : IntermediateField K⟮t⟯ L) (hE : ∀ γ ∈ Γ, ∀ e : E, σ γ (e : L) = e)
    (c : K) (W : AlgebraicCurve.Place K L) (hW : 0 < W.ord (t - algebraMap K L c))
    (hD : ∀ k ∈ Kst, AlgebraicCurve.SemilinearAut.ofAlgAut ((σ k).restrictScalars K) • W = W)
    (x : E) (hx : (x : L) = t) :
    Nat.card {P : AlgebraicCurve.Place K E // 0 < P.ord (x - algebraMap K E c)} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀)) := by
  classical
  have : FiniteDimensional K⟮t⟯ L := hfin
  have : IsGalois K⟮t⟯ L := hgal
  have hint : ∀ ψ : E →ₐ[K] L, ψ x = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq_sub t E x hx ψ hψ
  have hDH := AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K x t c
    (E.val.restrictScalars K) hx hfin hgal hint W hW
  let ψ : Γ₀ → (E →ₐ[K] L) := fun γ =>
    ((σ γ⁻¹).restrictScalars K : L →ₐ[K] L).comp (E.val.restrictScalars K)
  have hψapply : ∀ (γ : Γ₀) (e : E), ψ γ e = σ γ⁻¹ e := fun _ _ => rfl
  have hψ : ∀ γ, ψ γ x = t := by
    intro γ
    rw [hψapply]
    have : (x : L) = ((⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯) : L) := hx
    rw [this]
    exact (σ γ⁻¹).commutes (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)
  have hcongr : ∀ (ψ₁ ψ₂ : E →ₐ[K] L) (h₁ : ψ₁.toRingHom.IsIntegral) (h₂ : ψ₂.toRingHom.IsIntegral),
      ψ₁ = ψ₂ → W.restrictAlong ψ₁ h₁ = W.restrictAlong ψ₂ h₂ := by
    rintro ψ₁ ψ₂ h₁ h₂ rfl; rfl
  let T := {P : AlgebraicCurve.Place K E // 0 < P.ord (x - algebraMap K E c)}
  let f : Γ₀ → T := fun γ => ⟨W.restrictAlong (ψ γ) (hint _ (hψ γ)), hDH.2.1 (ψ γ) (hψ γ)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨P, hP⟩
    obtain ⟨ψ', hψ', hres⟩ := hDH.2.2.1 P hP
    let ψ'' : E →ₐ[K⟮t⟯] L :=
      { ψ'.toRingHom with
        commutes' := fun l => algHom_apply_algebraMap t E x hx ψ' hψ' l }
    have hψ''apply : ∀ e : E, ψ'' e = ψ' e := fun _ => rfl
    let φ : L →ₐ[K⟮t⟯] L := ψ''.liftNormal L
    have hφE : ∀ e : E, φ (e : L) = ψ' e := by
      intro e
      simpa only [IntermediateField.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, hψ''apply] using AlgHom.liftNormal_commutes ψ'' L e
    have hφinj : Function.Injective φ := φ.toRingHom.injective
    have hφsurj : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective (f := φ.toLinearMap)).mp hφinj
    let g : L ≃ₐ[K⟮t⟯] L := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
    have hgapply : ∀ z : L, g z = φ z := fun _ => rfl
    obtain ⟨γ₀, hγ₀⟩ := hσ g
    refine ⟨γ₀⁻¹, ?_⟩
    apply Subtype.ext
    change W.restrictAlong (ψ γ₀⁻¹) (hint _ (hψ γ₀⁻¹)) = P
    rw [← hres]
    apply hcongr
    apply AlgHom.ext
    intro e
    rw [hψapply, inv_inv, hγ₀, hgapply, hφE]
  have hconst : ∀ (γ : Γ₀) (a : Γ₀) (_ : a ∈ Γ) (b : Γ₀) (_ : b ∈ Kst), f (a * γ * b) = f γ := by
    intro γ a ha b hb
    apply Subtype.ext
    change W.restrictAlong (ψ (a * γ * b)) (hint _ (hψ (a * γ * b))) = W.restrictAlong (ψ γ) (hint
      _ (hψ γ))
    symm
    apply (hDH.2.2.2.1 (ψ γ) (ψ (a * γ * b)) (hψ γ) (hψ (a * γ * b))).mpr
    refine ⟨σ b⁻¹, hD b⁻¹ (Kst.inv_mem hb), ?_⟩
    apply AlgHom.ext
    intro e
    change ψ (a * γ * b) e = σ b⁻¹ (ψ γ e)
    rw [hψapply, hψapply, mul_inv_rev, mul_inv_rev, map_mul, map_mul, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply,
      hE a⁻¹ (Γ.inv_mem ha) e]
  let fbar : DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀) → T :=
    Quotient.lift f (by
      intro γ γ' hrel
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hrel
      exact (hconst γ a ha b hb).symm)
  have hfbar : Function.Surjective fbar := by
    intro p
    obtain ⟨γ, rfl⟩ := hsurj p
    exact ⟨DoubleCoset.mk Γ Kst γ, rfl⟩
  have : Finite (DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀)) := finite_doubleCosetQuotient Γ
    Kst
  exact Nat.card_le_card_of_surjective fbar hfbar
end AlgebraicCurves.Places.Proofs.NatCard_place_ord_sub_pos_le_natCard_doubleCoset
end ProofImplementation
