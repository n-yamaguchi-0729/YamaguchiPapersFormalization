/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Places.Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
import Nyll.AlgebraicCurves.Places.Place_exists_toValuationSubring_eq_comap_ringHom
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_isSeparable

/-!
# Place ncard alg Hom comp eq preimage eq ramification Index Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace SpecialisationCount

theorem ncard_preimage_eq_mul {G T : Type*} [Finite G] (Θ : G → T) (p : Set T) (hp : p.Finite)
    (h : ℕ) (hfib : ∀ t ∈ p, Set.ncard {g | Θ g = t} = h) :
    Set.ncard {g | Θ g ∈ p} = h * p.ncard := by
  classical
  induction p, hp using Set.Finite.induction_on with
  | empty => simp
  | @insert t s hts hs ih =>
    have hfib' : ∀ t' ∈ s, Set.ncard {g | Θ g = t'} = h := fun t' ht' =>
      hfib t' (Set.mem_insert_of_mem _ ht')
    have hunion : {g | Θ g ∈ insert t s} = {g | Θ g = t} ∪ {g | Θ g ∈ s} := by
      ext g
      simp
    have hdisj : Disjoint {g | Θ g = t} {g | Θ g ∈ s} := by
      rw [Set.disjoint_left]
      rintro g (rfl : Θ g = t) hg
      exact hts hg
    rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ih hfib',
      hfib t (Set.mem_insert _ _), Set.ncard_insert_of_notMem hts hs]
    ring

section Galois

variable {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
  [Algebra F M] [IsScalarTower K F M]

/-- The group homomorphism viewing automorphisms over the extension field as base-field
automorphisms. -/
noncomputable def toAutK : (M ≃ₐ[F] M) →* (M ≃ₐ[K] M) where
  toFun g := g.restrictScalars K
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[scoped simp] theorem toAutK_apply (g : M ≃ₐ[F] M) (x : M) : toAutK (K := K) g x = g x := rfl

theorem mem_smul_iff (g : M ≃ₐ[F] M) (W : Place K M) (x : M) :
    x ∈ (toAutK (K := K) g • W).toValuationSubring ↔ g⁻¹ x ∈ W.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv, AlgEquiv.smul_def, toAutK_apply]

theorem restrict_smul [Algebra.IsIntegral F M] (g : M ≃ₐ[F] M) (W : Place K M) :
    (toAutK (K := K) g • W).restrict F = W.restrict F := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff, mem_smul_iff, AlgEquiv.commutes]

theorem restrict_restrict {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [Algebra F' M]
    [IsScalarTower K F F'] [IsScalarTower K F' M] [IsScalarTower F F' M]
    [Algebra.IsIntegral F F'] [Algebra.IsIntegral F' M] [Algebra.IsIntegral F M] (W : Place K M) :
    (W.restrict F').restrict F = W.restrict F := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff, Place.mem_restrict_iff,
    ← IsScalarTower.algebraMap_apply]

variable [FiniteDimensional F M] [IsGalois F M]

theorem exists_smul_eq_of_restrict_eq (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    ∃ g : M ≃ₐ[F] M, toAutK (K := K) g • W = W' := by
  set v := W.restrict F with hv
  let S := Place.integralClosureAt M v
  have hW : W.restrict F = v := rfl
  have h1 : (Place.fiberCenter M v hW).asIdeal ∈
      (IsLocalRing.maximalIdeal v.toValuationSubring).primesOver S :=
    ⟨(Place.fiberCenter M v hW).isPrime, Place.fiberCenter_liesOver hW⟩
  have h2 : (Place.fiberCenter M v h).asIdeal ∈
      (IsLocalRing.maximalIdeal v.toValuationSubring).primesOver S :=
    ⟨(Place.fiberCenter M v h).isPrime, Place.fiberCenter_liesOver h⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq v.toValuationSubring F M S h1 h2
  refine ⟨σ⁻¹, ?_⟩
  have hW'' : (toAutK (K := K) σ⁻¹ • W).restrict F = v := restrict_smul _ _
  refine Place.eq_of_fiberCenter_eq hW'' h (IsDedekindDomain.HeightOneSpectrum.ext ?_)
  rw [← hσ]
  ext c
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hσc : galRestrict v.toValuationSubring F M S σ c ≠ 0 :=
    (map_ne_zero_iff _ (galRestrict v.toValuationSubring F M S σ).injective).mpr hc
  rw [Ideal.mem_comap, Place.mem_fiberCenter_iff_ord_pos hW'' hc,
    Place.mem_fiberCenter_iff_ord_pos hW hσc, algebraMap_galRestrict_apply]
  have : (toAutK (K := K) σ⁻¹ • W).ord (algebraMap S M c)
      = (toAutK (K := K) σ⁻¹ • W).ord (toAutK (K := K) σ⁻¹ (σ (algebraMap S M c))) := by
    rw [toAutK_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  rw [this, Place.ord_smul]

theorem ncard_setOf_smul_eq (W₁ W : Place K M) (h : W.restrict F = W₁.restrict F) :
    Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W} =
      Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} := by
  obtain ⟨g₀, rfl⟩ := exists_smul_eq_of_restrict_eq W₁ W h
  have : {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = toAutK (K := K) g₀ • W₁} =
      (fun g => g₀ * g) '' {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hg
      refine ⟨g₀⁻¹ * g, ?_, by group⟩
      rw [map_mul, mul_smul, hg, ← mul_smul, map_inv, inv_mul_cancel, one_smul]
    · rintro ⟨g', hg', rfl⟩
      rw [map_mul, mul_smul, hg']
  rw [this, Set.ncard_image_of_injective _ (mul_right_injective g₀)]

theorem ncard_stabilizer [IsAlgClosed K] (W₁ : Place K M) :
    Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} =
      W₁.ramificationIndex F * W₁.inertiaDeg F := by
  classical
  set s : ℕ := Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} with hs
  have hcount := ncard_preimage_eq_mul (fun g : M ≃ₐ[F] M => toAutK (K := K) g • W₁)
    (↑((W₁.restrict F).fiberOver M) : Set (Place K M)) (Finset.finite_toSet _) s
    (fun W hW => by
      rw [Finset.mem_coe, Place.mem_fiberOver] at hW
      exact ncard_setOf_smul_eq W₁ W hW)
  have huniv : {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ ∈
      (↑((W₁.restrict F).fiberOver M) : Set (Place K M))} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Place.mem_fiberOver, restrict_smul]
  rw [huniv, Set.ncard_univ, Set.ncard_coe_finset, IsGalois.card_aut_eq_finrank] at hcount
  have hfi := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W₁.restrict F) W₁ rfl
  have hr : ((W₁.restrict F).fiberOver M).card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨W₁, Place.restrict_mem_fiberOver W₁⟩
  rw [hcount] at hfi
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) (hfi.trans (mul_comm _ _))).symm

end Galois

section Tower

variable {K F F' M : Type*} [Field K] [Field F] [Field F'] [Field M] [Algebra K F] [Algebra K F']
  [Algebra K M] [Algebra F F'] [Algebra F' M] [Algebra F M] [IsScalarTower K F F']
  [IsScalarTower K F' M] [IsScalarTower K F M] [IsScalarTower F F' M]
  [Algebra.IsIntegral F F'] [Algebra.IsIntegral F' M] [Algebra.IsIntegral F M]

theorem inertiaDeg_eq_one [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K M]
    (W : Place K M) : W.inertiaDeg F = 1 := by
  have h := W.deg_restrict_mul_inertiaDeg (F := F)
  rwa [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
    one_mul] at h

theorem ramificationIndex_tower (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex F' * (W.restrict F').ramificationIndex F := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (W.restrict F).toValuationSubring
  have h1 : (W.restrict F).ord (π : F) = 1 := Place.ord_coe_irreducible _ hπ
  have h2 := W.ord_restrict (F := F) (π : F)
  have h3 := W.ord_restrict (F := F') (algebraMap F F' (π : F))
  have h4 := (W.restrict F').ord_restrict (F := F) (π : F)
  rw [← IsScalarTower.algebraMap_apply, h2, h4, restrict_restrict, h1, mul_one, mul_one]
    at h3
  exact_mod_cast h3

end Tower

section Existence

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [Algebra.IsSeparable F' M]

theorem exists_restrict_eq (q : Place K F') : ∃ W : Place K M, W.restrict F' = q := by
  have hker : RingHom.ker (algebraMap q.toValuationSubring (Place.integralClosureAt M q)) ≤
      IsLocalRing.maximalIdeal q.toValuationSubring := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (Place.algebraMap_integralClosureAt_injective (F'
      := M) q)]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := Place.integralClosureAt M q) (IsLocalRing.maximalIdeal q.toValuationSubring) hker
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply Place.maximalIdeal_ne_bot q
    rw [← hQ]
    change Ideal.comap (algebraMap q.toValuationSubring (Place.integralClosureAt M q)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (Place.algebraMap_integralClosureAt_injective (F' := M) q)
  exact ⟨Place.placeOfPrime ⟨Q, hQmax.isPrime, hQne⟩, Place.restrict_placeOfPrime _⟩

end Existence

section Core

variable {K F F' M E : Type*} [Field K] [Field F] [Field F'] [Field M] [Field E]
  [Algebra K F] [Algebra K F'] [Algebra K M]
  [Algebra F F'] [Algebra F' M] [Algebra F M] [Algebra F E]
  [IsScalarTower K F F'] [IsScalarTower K F' M] [IsScalarTower K F M] [IsScalarTower F F' M]

/-- The embedding obtained by composing subfield inclusion, an automorphism, and the target
embedding. -/
noncomputable def theta (ι : M →ₐ[F] E) (g : M ≃ₐ[F] M) : F' →ₐ[F] E :=
  ι.comp ((g : M →ₐ[F] M).comp (IsScalarTower.toAlgHom F F' M))

@[scoped simp] theorem theta_apply (ι : M →ₐ[F] E) (g : M ≃ₐ[F] M) (y : F') :
    theta ι g y = ι (g (algebraMap F' M y)) := rfl

theorem theta_mul_restrictScalars (ι : M →ₐ[F] E) (g : M ≃ₐ[F] M) (h : M ≃ₐ[F'] M) :
    theta ι (g * h.restrictScalars F) = theta (F' := F') ι g := by
  ext y
  simp only [theta_apply, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

theorem setOf_theta_eq (ι : M →ₐ[F] E) (g₀ : M ≃ₐ[F] M) :
    {g : M ≃ₐ[F] M | theta (F' := F') ι g = theta ι g₀} =
      (fun h : M ≃ₐ[F'] M => g₀ * h.restrictScalars F) '' Set.univ := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
  constructor
  · intro hg
    have hfix : ∀ y : F', (g₀⁻¹ * g) (algebraMap F' M y) = algebraMap F' M y := by
      intro y
      have := congrArg (fun τ : F' →ₐ[F] E => τ y) hg
      simp only [theta_apply] at this
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
      exact ι.toRingHom.injective this
    refine ⟨{ (g₀⁻¹ * g).toRingEquiv with commutes' := hfix }, ?_⟩
    refine AlgEquiv.ext fun x => ?_
    change g₀ ((g₀⁻¹ * g) x) = g x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  · rintro ⟨h, rfl⟩
    exact theta_mul_restrictScalars ι g₀ h

variable [FiniteDimensional F M] [IsGalois F M] [IsAlgClosed E]

theorem theta_surjective (ι : M →ₐ[F] E) : Function.Surjective (theta (F' := F') ι) := by
  intro τ
  have : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.of_finite F M
  let : Algebra F' E := τ.toRingHom.toAlgebra
  have : IsScalarTower F F' E := IsScalarTower.of_algebraMap_eq fun x => (τ.commutes x).symm
  have : Algebra.IsAlgebraic F' M :=
    Algebra.IsAlgebraic.tower_top (K := F) F'
  let σ' : M →ₐ[F'] E := IsAlgClosed.lift
  let σ : M →ₐ[F] E := σ'.restrictScalars F
  let : Algebra M E := ι.toRingHom.toAlgebra
  have : IsScalarTower F M E := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨σ.restrictNormal' M, ?_⟩
  ext y
  rw [theta_apply]
  have h1 : ι (σ.restrictNormal' M (algebraMap F' M y)) = σ (algebraMap F' M y) := by
    have := AlgHom.restrictNormal_commutes σ M (algebraMap F' M y)
    rw [Algebra.algebraMap_self, RingHom.id_apply] at this
    exact this
  rw [h1]
  change σ' (algebraMap F' M y) = τ y
  rw [σ'.commutes]
  rfl

theorem ncard_setOf_theta_eq (ι : M →ₐ[F] E) (τ : F' →ₐ[F] E) :
    Set.ncard {g : M ≃ₐ[F] M | theta ι g = τ} = Nat.card (M ≃ₐ[F'] M) := by
  obtain ⟨g₀, rfl⟩ := theta_surjective ι τ
  have hinj : Function.Injective (fun h : M ≃ₐ[F'] M => g₀ * h.restrictScalars F) :=
    (mul_right_injective g₀).comp (AlgEquiv.restrictScalars_injective F)
  rw [setOf_theta_eq, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
omit [IsScalarTower K F F'] [FiniteDimensional F M] [IsGalois F M] [IsAlgClosed E] in
theorem restrict_smul_eq_iff (ι : M →ₐ[F] E) (A : ValuationSubring E) (W₁ : Place K M)
    (hW₁ : W₁.toValuationSubring = A.comap ι.toRingHom) [Algebra.IsIntegral F' M]
    (g : M ≃ₐ[F] M) (q : Place K F') :
    (toAutK (K := K) g⁻¹ • W₁).restrict F' = q ↔
      ∀ y : F', y ∈ q.toValuationSubring ↔ theta ι g y ∈ A := by
  constructor
  · rintro rfl y
    rw [Place.mem_restrict_iff, mem_smul_iff, inv_inv, hW₁, ValuationSubring.mem_comap]
    rfl
  · intro h
    refine Place.ext (SetLike.ext fun y => ?_)
    rw [Place.mem_restrict_iff, mem_smul_iff, inv_inv, hW₁, ValuationSubring.mem_comap, h y]
    rfl

theorem ncard_setOf_forall_mem_iff [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    [IsCurveOver K M] [FiniteDimensional F F']
    (ι : M →ₐ[F] E) (A : ValuationSubring E) (W₁ : Place K M)
    (hW₁ : W₁.toValuationSubring = A.comap ι.toRingHom) (q : Place K F')
    (hq : q.restrict F = W₁.restrict F) :
    Set.ncard {τ : F' →ₐ[F] E | ∀ y : F', y ∈ q.toValuationSubring ↔ τ y ∈ A} =
      q.ramificationIndex F := by
  classical
  have : FiniteDimensional F' M := Module.Finite.of_restrictScalars_finite F F' M
  have : IsGalois F' M := IsGalois.tower_top_of_isGalois F F' M
  set p : Set (F' →ₐ[F] E) := {τ | ∀ y : F', y ∈ q.toValuationSubring ↔ τ y ∈ A} with hp
  have h1 : Set.ncard {g : M ≃ₐ[F] M | theta ι g ∈ p} = Nat.card (M ≃ₐ[F'] M) * p.ncard :=
    ncard_preimage_eq_mul _ p (Set.toFinite p) _ fun τ _ => ncard_setOf_theta_eq ι τ
  have h2 : {g : M ≃ₐ[F] M | theta ι g ∈ p} =
      (fun g => g⁻¹) '' {g : M ≃ₐ[F] M | (toAutK (K := K) g • W₁).restrict F' = q} := by
    rw [Set.image_inv_eq_inv]
    ext g
    simp only [Set.mem_inv, Set.mem_ofPred_eq, hp]
    exact (restrict_smul_eq_iff ι A W₁ hW₁ g q).symm
  have h2' : Set.ncard {g : M ≃ₐ[F] M | theta ι g ∈ p} =
      Set.ncard {g : M ≃ₐ[F] M | (toAutK (K := K) g • W₁).restrict F' = q} := by
    rw [h2, Set.ncard_image_of_injective _ inv_injective]
  have h3 : Set.ncard {g : M ≃ₐ[F] M | (toAutK (K := K) g • W₁).restrict F' = q} =
      Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} * (q.fiberOver M).card := by
    have := ncard_preimage_eq_mul (fun g : M ≃ₐ[F] M => toAutK (K := K) g • W₁)
      (↑(q.fiberOver M) : Set (Place K M)) (Finset.finite_toSet _)
      (Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁}) (fun W hW => by
        rw [Finset.mem_coe, Place.mem_fiberOver] at hW
        refine ncard_setOf_smul_eq W₁ W ?_
        rw [← hq, ← hW, restrict_restrict])
    rw [Set.ncard_coe_finset] at this
    rw [← this]
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Finset.mem_coe, Place.mem_fiberOver]
  have h4 : Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} =
      W₁.ramificationIndex F := by
    rw [ncard_stabilizer, inertiaDeg_eq_one, mul_one]
  obtain ⟨W, hW⟩ := exists_restrict_eq (M := M) q
  have h5 : (q.fiberOver M).card * W.ramificationIndex F' = Nat.card (M ≃ₐ[F'] M) := by
    have := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg q W hW
    rwa [inertiaDeg_eq_one, mul_one, ← IsGalois.card_aut_eq_finrank] at this
  have h6 : W.ramificationIndex F = W₁.ramificationIndex F := by
    have hWv : W.restrict F = W₁.restrict F := by rw [← restrict_restrict (F' := F'), hW, hq]
    have a := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W₁.restrict F) W hWv
    have b := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W₁.restrict F) W₁ rfl
    rw [inertiaDeg_eq_one, mul_one] at a b
    have hr : ((W₁.restrict F).fiberOver M).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨W₁, Place.restrict_mem_fiberOver W₁⟩
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) (a.trans b.symm)
  have h7 : W.ramificationIndex F = W.ramificationIndex F' * q.ramificationIndex F := by
    rw [ramificationIndex_tower (F' := F'), hW]
  have hpos : 0 < (q.fiberOver M).card * W.ramificationIndex F' :=
    Nat.pos_of_ne_zero (mul_ne_zero (Finset.card_ne_zero.mpr ⟨W, (Place.mem_fiberOver _).mpr hW⟩)
      (W.ramificationIndex_pos (F := F')).ne')
  have key : (q.fiberOver M).card * W.ramificationIndex F' * p.ncard =
      (q.fiberOver M).card * W.ramificationIndex F' * q.ramificationIndex F := by
    calc (q.fiberOver M).card * W.ramificationIndex F' * p.ncard
        = Nat.card (M ≃ₐ[F'] M) * p.ncard := by rw [h5]
      _ = W₁.ramificationIndex F * (q.fiberOver M).card := by rw [← h1, h2', h3, h4]
      _ = (q.fiberOver M).card * W.ramificationIndex F' * q.ramificationIndex F := by
          rw [← h6, h7]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos key

end Core

theorem fg_of_finite {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
    [Algebra F M] [IsScalarTower K F M] [Module.Finite F M] {x : F} (hx : Transcendental K x)
    (hfinx : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Transcendental K (algebraMap F M x) ∧
      FiniteDimensional (IntermediateField.adjoin K ({algebraMap F M x} : Set M)) M := by
  let χ : F →ₐ[K] M := IsScalarTower.toAlgHom K F M
  have hχ : ∀ y, χ y = algebraMap F M y := fun _ => rfl
  have hinj : Function.Injective χ := χ.toRingHom.injective
  refine ⟨fun h => hx ((isAlgebraic_algHom_iff χ hinj).mp h), ?_⟩
  let Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  have : FiniteDimensional Kx F := hfinx
  have : IsScalarTower Kx F M := inferInstance
  have : Module.Finite Kx M := Module.Finite.trans F M
  let L : IntermediateField K M := IntermediateField.adjoin K ({algebraMap F M x} : Set M)
  have hmap : ∀ y ∈ IntermediateField.adjoin K ({x} : Set F), χ y ∈ L := by
    intro y hy
    have h1 : χ y ∈ (IntermediateField.adjoin K ({x} : Set F)).map χ := ⟨y, hy, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have hmem : ∀ c : Kx, χ (c : F) ∈ L := fun c => hmap c c.2
  let : Algebra Kx L :=
    (((χ : F →+* M).comp (algebraMap Kx F)).codRestrict L fun c => hmem c).toAlgebra
  have : IsScalarTower Kx L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite Kx L M
end SpecialisationCount

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    (A : ValuationSubring E) (e : F →ₐ[K] E) (v₀ : Place K F)
    (hev₀ : ∀ f : F, f ∈ v₀.toValuationSubring ↔ e f ∈ A)
    (q : Place K F') (hq : q.restrictAlong φ hφ = v₀) :
    Set.ncard {σ : F' →ₐ[K] E | σ.comp φ = e ∧
        ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} =
      q.ramificationIndexAlong φ := by
  let : Algebra F F' := algebraAlong φ
  have : IsScalarTower K F F' := isScalarTower_along φ
  have : Module.Finite F F' := hfin
  have : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  let : Algebra F E := e.toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  have hq' : q.restrict F = v₀ := hq
  change _ = q.ramificationIndex F
  have hset : {σ : F' →ₐ[K] E | σ.comp φ = e ∧ ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} =
      (fun τ : F' →ₐ[F] E => τ.restrictScalars K) ''
        {τ | ∀ g : F', g ∈ q.toValuationSubring ↔ τ g ∈ A} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hσ, hP⟩
      refine ⟨{ (σ : F' →+* E) with commutes' := fun x => ?_ }, hP, ?_⟩
      · change σ (φ x) = e x
        rw [← hσ]
        rfl
      · ext y
        rfl
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨?_, hτ⟩
      ext x
      change τ (algebraMap F F' x) = algebraMap F E x
      exact τ.commutes x
  rw [hset, Set.ncard_image_of_injective _ (AlgHom.restrictScalars_injective K)]
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let L := AlgebraicClosure F'
  let : Algebra F L := inferInstance
  have : IsScalarTower F F' L := inferInstance
  have : IsScalarTower K F' L := inferInstance
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K F' L, IsScalarTower.algebraMap_apply F F' L,
      ← IsScalarTower.algebraMap_apply K F F']
  let M := IntermediateField.normalClosure F F' L
  let : Algebra F' M := inferInstance
  have : IsScalarTower F F' M := inferInstance
  have : FiniteDimensional F M := inferInstance
  let : Algebra K M := inferInstance
  have : IsScalarTower K F M := inferInstance
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.trans F F' L
  have : IsAlgClosure F L := ⟨inferInstance, inferInstance⟩
  have : Normal F M := inferInstance
  have : IsGalois F M := IsGalois.mk
  have : IsScalarTower K F' M := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change algebraMap K L x = algebraMap F' L (algebraMap K F' x)
    exact IsScalarTower.algebraMap_apply K F' L x
  obtain ⟨x, hx, hfinx⟩ := hfg
  obtain ⟨hy, hfiny⟩ :=
    AlgebraicCurve.SpecialisationCount.fg_of_finite (M := M) hx hfinx
  let _ := hfiny
  let _ : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  let _ : IsCurveOver K M := by
    have : Algebra.IsIntegral
        (IntermediateField.adjoin K ({algebraMap F M x} : Set M)) M :=
      Algebra.IsIntegral.of_finite _ _
    have : Algebra.IsSeparable
        (IntermediateField.adjoin K ({algebraMap F M x} : Set M)) M :=
      Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable K M _ hy hfiny inferInstance
  let _ : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.of_finite F M
  let ι : M →ₐ[F] E := IsAlgClosed.lift
  have hwK : ∀ a : K, ι.toRingHom (algebraMap K M a) ∈ A := by
    intro a
    rw [IsScalarTower.algebraMap_apply K F M, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ι.commutes]
    exact (hev₀ _).mp (v₀.algebraMap_mem' a)
  have hwx : ∃ y : M, ι.toRingHom y ∉ A := by
    obtain ⟨f, hf⟩ : ∃ f : F, f ∉ v₀.toValuationSubring := by
      by_contra! h
      exact v₀.ne_top' (SetLike.ext fun f => ⟨fun _ => ValuationSubring.mem_top f, fun _ => h f⟩)
    refine ⟨algebraMap F M f, fun hA => hf ((hev₀ f).mpr ?_)⟩
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ι.commutes] at hA
  obtain ⟨W₁, hW₁⟩ :=
    Place.exists_toValuationSubring_eq_comap_ringHom (K := K) (algebraMap F M x) ι.toRingHom A
      hwK hwx
  have hW₁v : W₁.restrict F = v₀ := by
    refine Place.ext (SetLike.ext fun f => ?_)
    rw [Place.mem_restrict_iff, hW₁, ValuationSubring.mem_comap, hev₀, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, ι.commutes]
    rfl
  exact AlgebraicCurve.SpecialisationCount.ncard_setOf_forall_mem_iff ι A W₁ hW₁ q (hq'.trans
    hW₁v.symm)
end AlgebraicCurves.Places.Proofs.Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
