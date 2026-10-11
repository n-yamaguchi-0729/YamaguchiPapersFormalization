/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Nyll.AlgebraicCurves.Differentials.Residues.TateTrace
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg

/-!
# CompletionTraceSum of isSeparable

A separable algebraic function-field extension satisfies the completed trace-sum identity, using
semilocal completions and ramification and inertia degrees.
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable

noncomputable section

section ProductTrace

open scoped TensorProduct

private theorem gapsw7_x3x_trace_pi (R : Type*) [CommRing R] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  have _em := Classical.em
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  have key : Algebra.leftMulMatrix (Pi.basis b) x
      = Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (b i) (x i)) := by
    refine Matrix.ext fun ji ji' => ?_
    obtain ⟨i, j⟩ := ji
    obtain ⟨i', j'⟩ := ji'
    rcases eq_or_ne i i' with rfl | hne
    · rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i (b i j')) i = x i * b i j' := by
        simp
      rw [hx]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i' (b i' j')) i = 0 := by
        simp [Pi.single_eq_of_ne hne]
      rw [hx]
      simp
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), key,
    Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ =>
    (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

private theorem gapsw7_x3x_trace_baseChange (R A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Free R B]
    [Module.Finite R B] (b : B) :
    Algebra.trace A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b)
      = algebraMap R A (Algebra.trace R B b) := by
  have _em := Classical.em
  have h := LinearMap.trace_baseChange (Algebra.lmul R B b) A
  rw [Algebra.baseChange_lmul] at h
  exact h

private theorem gapsw7_x3x_trace_decomposition_of_prod_iso (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    [∀ i, Module.Free A (S i)] [∀ i, Module.Finite A (S i)]
    (e : (A ⊗[R] B) ≃ₐ[A] ∀ i, S i) (b : B) :
    algebraMap R A (Algebra.trace R B b)
      = ∑ i, Algebra.trace A (S i) (e ((1 : A) ⊗ₜ[R] b) i) := by
  have _em := Classical.em
  rw [← gapsw7_x3x_trace_baseChange R A B b,
    ← Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[R] b),
    gapsw7_x3x_trace_pi A S]

end ProductTrace

section SpectralSetup

open Polynomial IsLocalRing IsDedekindDomain
open AlgebraicCurve AlgebraicCurve.Place
open scoped AlgebraicCurve.Place Valued NNReal WithZero
open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

private theorem kw_ffgc_norm_adicCompletion_eq (x : V.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion V
    ‖x‖ = (WithZeroMulInt.toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  let := kw_ffgc_rankOne_adicCompletion V
  have h := valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (V.heightOneSpectrum.valuedAdicCompletion_surjective F) x
  simp only [Valued.toNormedField.norm_def, Valuation.RankOne.hom]
  rw [← h]; rfl

end SpectralSetup

section AbsoluteValueIntegralClosure

open Polynomial IsLocalRing IsDedekindDomain
open AlgebraicCurve AlgebraicCurve.Place
open scoped AlgebraicCurve.Place Valued NNReal WithZero
open WithZeroMulInt Valuation.IsRankOneDiscrete

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

private theorem kw_ffgc_absoluteValue_extends (c : (W.restrict F).adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion (W.restrict F)
    kw_ffgc_absoluteValue F W
      (algebraMap (W.restrict F).adicCompletion W.adicCompletion c) = ‖c‖ := by
  let := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  let := kw_ffgc_rankOne_adicCompletion W
  have hr : (0 : ℝ) < (W.ramificationIndex F : ℝ) :=
    Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F))
  change ‖algebraMap (W.restrict F).adicCompletion W.adicCompletion c‖
      ^ ((W.ramificationIndex F : ℝ))⁻¹ = ‖c‖
  rw [kw_ffgc_norm_adicCompletion_eq W, kw_ffgc_norm_adicCompletion_eq (W.restrict F),
    kw_ffgc_algebraMap_adicCompletionComap_eq, kw_ffgc_valued_adicCompletionComap,
    map_pow, NNReal.coe_pow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _),
    mul_inv_cancel₀ hr.ne', Real.rpow_one]

private theorem kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion]
    (x : W.adicCompletionIntegers) :
    IsIntegral (W.restrict F).adicCompletionIntegers x := by
  let := kw_ffgc_rankOne_adicCompletion (W.restrict F)
  let := kw_ffgc_rankOne_adicCompletion W
  let : NontriviallyNormedField (W.restrict F).adicCompletion :=
    Valued.toNontriviallyNormedField (W.restrict F).adicCompletion ℤᵐ⁰
  have : IsUltrametricDist (W.restrict F).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have hr : (0 : ℝ) < ((W.ramificationIndex F : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (W.ramificationIndex_pos (F := F)))
  have hxn : ‖(x : W.adicCompletion)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hsn : spectralNorm (W.restrict F).adicCompletion W.adicCompletion
        (x : W.adicCompletion)
      = ‖(x : W.adicCompletion)‖ ^ ((W.ramificationIndex F : ℝ))⁻¹ :=
    (spectralNorm_unique_field_norm_ext (f := kw_ffgc_absoluteValue F W)
      (kw_ffgc_absoluteValue_extends F W) (x : W.adicCompletion)).symm
  have hspec : spectralValue (minpoly (W.restrict F).adicCompletion
      (x : W.adicCompletion)) ≤ 1 := by
    change spectralNorm (W.restrict F).adicCompletion W.adicCompletion
      (x : W.adicCompletion) ≤ 1
    rw [hsn]; exact Real.rpow_le_one (norm_nonneg _) hxn hr.le
  have hmon : (minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)).Monic :=
    minpoly.monic (Algebra.IsAlgebraic.isAlgebraic
      (R := (W.restrict F).adicCompletion) (x : W.adicCompletion)).isIntegral
  have hlift : minpoly (W.restrict F).adicCompletion (x : W.adicCompletion)
      ∈ Polynomial.lifts (algebraMap (W.restrict F).adicCompletionIntegers
          (W.restrict F).adicCompletion) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, ?_⟩, rfl⟩
    exact (Valued.toNormedField.norm_le_one_iff).mp
      ((spectralValue_le_one_iff hmon).mp hspec n)
  obtain ⟨P, hP, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hxintW : IsIntegral (W.restrict F).adicCompletionIntegers (x : W.adicCompletion) := by
    refine ⟨P, hPmon, ?_⟩
    rw [← Polynomial.aeval_def,
      ← Polynomial.aeval_map_algebraMap (W.restrict F).adicCompletion, hP, minpoly.aeval]
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
      W.adicCompletionIntegers W.adicCompletion)
    Subtype.val_injective).mp hxintW

private theorem kw_ffgc_isIntegralClosure_adicCompletionIntegers
    [Algebra.IsAlgebraic (W.restrict F).adicCompletion W.adicCompletion] :
    IsIntegralClosure W.adicCompletionIntegers (W.restrict F).adicCompletionIntegers
      W.adicCompletion where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hxW : IsIntegral W.adicCompletionIntegers x := hx.tower_top
      have : IsIntegrallyClosed W.adicCompletionIntegers :=
        Valuation.Integers.isIntegrallyClosed
          (HeightOneSpectrum.adicCompletionIntegers.integers
            (K := F') (v := W.heightOneSpectrum))
      exact IsIntegrallyClosed.isIntegral_iff.mp hxW
    · rintro ⟨y, rfl⟩
      exact (kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic F W y).map
        (IsScalarTower.toAlgHom (W.restrict F).adicCompletionIntegers
          W.adicCompletionIntegers W.adicCompletion)

end AbsoluteValueIntegralClosure

section IntegerComap

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom
open AlgebraicCurve AlgebraicCurve.Place
open scoped AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

private theorem kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal
    {x : (W.restrict F).adicCompletionIntegers}
    (hx : x ∈ maximalIdeal (W.restrict F).adicCompletionIntegers) :
    kw_ffgc_adicCompletionComapIntegers F W x ∈ maximalIdeal W.adicCompletionIntegers := by
  have hrpos := W.ramificationIndex_pos (F := F)
  rw [show maximalIdeal (W.restrict F).adicCompletionIntegers
      = (W.restrict F).heightOneSpectrum.completionIdeal F from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff] at hx
  rw [show maximalIdeal W.adicCompletionIntegers
      = W.heightOneSpectrum.completionIdeal F' from rfl,
    HeightOneSpectrum.mem_completionIdeal_iff, kw_ffgc_adicCompletionComapIntegers_coe,
    kw_ffgc_valued_adicCompletionComap]
  calc Valued.v (x : (W.restrict F).adicCompletion) ^ W.ramificationIndex F
      < 1 ^ W.ramificationIndex F := pow_lt_pow_left₀ hx zero_le hrpos.ne'
    _ = 1 := one_pow _

private scoped instance kw_ffgc_isLocalHom_adicCompletionComapIntegers :
    IsLocalHom (kw_ffgc_adicCompletionComapIntegers F W) where
  map_nonunit x hx := by
    by_contra hnu
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
      (kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal F W
        ((IsLocalRing.mem_maximalIdeal x).mpr hnu))

end IntegerComap

section ResidueCompletion

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero
open scoped Valued WithZero
open AlgebraicCurve AlgebraicCurve.Place
open scoped AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

private def kw_ffgc_residueFieldEquivCompletionResidueField :
    V.ResidueField ≃+* IsLocalRing.ResidueField V.adicCompletionIntegers :=
  ResidueFieldEquivCompletionResidueField F V.heightOneSpectrum

private theorem kw_ffgc_residueFieldEquivCompletionResidueField_residue (a : V.toValuationSubring) :
    kw_ffgc_residueFieldEquivCompletionResidueField V
        (IsLocalRing.residue V.toValuationSubring a)
      = IsLocalRing.residue V.adicCompletionIntegers
          (algebraMap V.toValuationSubring V.adicCompletionIntegers a) :=
  rfl

end ResidueCompletion

section Semilocal

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain TensorProduct

section FiberAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

private scoped instance kwF4R1V384a_instAlgebraFiberCompletion (v : Place K E) (w' : v.fiber F) :
    Algebra v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_algebraAdicCompletionComap E w'

private scoped instance kwF4R1V384a_instIsScalarTowerFiberCompletion (v : Place K E) (w' :
  v.fiber F) :
    IsScalarTower E v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  refine IsScalarTower.of_algebraMap_eq fun e => ?_
  rw [show algebraMap E w'.adicCompletion e = algebraMap F w'.adicCompletion (algebraMap E F e)
    from IsScalarTower.algebraMap_apply E F w'.adicCompletion e]
  exact kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' e

private scoped instance kwF4R1V384a_instFiniteDimensionalFiberCompletion [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    FiniteDimensional v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_finiteDimensional_adicCompletion E w'

end FiberAlgebra

section SemilocalDiag

variable {K : Type*} (F : Type*) [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

private def kwF4R1V384a_semilocalComponent (v : Place K E) (w' : v.fiber F) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion] w'.1.adicCompletion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.adicCompletion w'.1.adicCompletion)
    (IsScalarTower.toAlgHom E F w'.1.adicCompletion) (fun _ _ => Commute.all _ _)

omit [HasPrincipalDivisors K E] in
@[scoped simp]
private theorem kwF4R1V384a_semilocalComponent_tmul (v : Place K E) (w' : v.fiber F)
    (c : v.adicCompletion) (g : F) :
    kwF4R1V384a_semilocalComponent F v w' (c ⊗ₜ[E] g)
      = algebraMap v.adicCompletion w'.1.adicCompletion c
          * algebraMap F w'.1.adicCompletion g := by
  unfold kwF4R1V384a_semilocalComponent
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

private def kwF4R1V384a_semilocalDiag (v : Place K E) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
  AlgHom.pi (kwF4R1V384a_semilocalComponent F v)

variable {F}

omit [HasPrincipalDivisors K E] in
@[scoped simp]
private theorem kwF4R1V384a_semilocalDiag_apply (v : Place K E) (x : v.adicCompletion ⊗[E] F)
    (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v x w' = kwF4R1V384a_semilocalComponent F v w' x := rfl

omit [HasPrincipalDivisors K E] in
private theorem kwF4R1V384a_semilocalDiag_one_tmul (v : Place K E) (g : F) (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = algebraMap F w'.1.adicCompletion g := by
  rw [kwF4R1V384a_semilocalDiag_apply, kwF4R1V384a_semilocalComponent_tmul,
    map_one, one_mul]

end SemilocalDiag

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private def KwF4R1V384aCompletionSemilocalBij : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E),
    Function.Bijective (kwF4R1V384a_semilocalDiag (K := K) (E := E) F v)

end Mint

section PerComponentSurjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
variable [FiniteDimensional E F]

omit [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F] in
private theorem kwF4R1V384a_completionLinearCombination_surjective
    (w' : Place K F) {ι : Type*} [Fintype ι] (b : Module.Basis ι E F) :
    Function.Surjective (kw_ffgc_completionLinearCombination E w' b) := by
  let := kw_ffgc_rankOne_adicCompletion (K := K) (w'.restrict E)
  let : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion
      (WithZero (Multiplicative ℤ))
  rw [← Set.range_eq_univ, ← LinearMap.coe_range,
    ← (LinearMap.range (kw_ffgc_completionLinearCombination E w' b))
        |>.closed_of_finiteDimensional.closure_eq]
  exact (kw_ffgc_denseRange_completionLinearCombination E w' b).closure_range

omit [HasPrincipalDivisors K E] in
private theorem kwF4R1V384a_semilocalComponent_surjective (v : Place K E) (w' : v.fiber F) :
    Function.Surjective (kwF4R1V384a_semilocalComponent F v w') := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  intro y
  let b := Module.finBasis E F
  obtain ⟨c, hc⟩ := kwF4R1V384a_completionLinearCombination_surjective w' b y
  refine ⟨∑ i, c i ⊗ₜ[E] b i, ?_⟩
  rw [map_sum, ← hc]
  unfold kw_ffgc_completionLinearCombination
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kwF4R1V384a_semilocalComponent_tmul, Algebra.smul_def]

end PerComponentSurjective

section SpecificMints

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private def KwF4R1V384aDistinctKernels : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' w'' : v.fiber F), w' ≠ w'' →
    RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w').toRingHom
      ≠ RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w'').toRingHom

private def KwF4R1V384aFinrankCompletionEF : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F),
    (Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ)
      = (w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)

end SpecificMints

section BijEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private scoped instance kwF4R1V384a_ker_semilocalComponent_isMaximal
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    (RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (kwF4R1V384a_semilocalComponent F v w').toRingHom
    (kwF4R1V384a_semilocalComponent_surjective v w')

private theorem kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (hdist : KwF4R1V384aDistinctKernels K F E) (v : Place K E) :
    Function.Surjective (kwF4R1V384a_semilocalDiag F v) := by
  classical
  intro y
  let m : v.fiber F → Ideal (v.adicCompletion ⊗[E] F) :=
    fun w' => RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom
  have : ∀ w', (m w').IsMaximal :=
    kwF4R1V384a_ker_semilocalComponent_isMaximal v
  have hcop : Pairwise (Function.onFun IsCoprime m) := fun i j hij =>
    Ideal.isCoprime_of_isMaximal (I := m i) (J := m j) (hdist v i j hij)
  choose xw hxw using fun w' => kwF4R1V384a_semilocalComponent_surjective v w' (y w')
  obtain ⟨xbar, hxbar⟩ :=
    Ideal.quotientInfToPiQuotient_surj hcop (fun w' => Ideal.Quotient.mk (m w') (xw w'))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, funext fun w' => ?_⟩
  change kwF4R1V384a_semilocalComponent F v w' x = y w'
  have hcomp : Ideal.Quotient.mk (m w') x = Ideal.Quotient.mk (m w') (xw w') := by
    have := congrFun hxbar w'
    rwa [Ideal.quotientInfToPiQuotient_mk' m x w'] at this
  have hmod : x - xw w' ∈ m w' := Ideal.Quotient.eq.mp hcomp
  have hzero : kwF4R1V384a_semilocalComponent F v w' (x - xw w') = 0 := hmod
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, hxw w']

private scoped instance kwF4R1V384a_instModuleFiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (v : Place K E) (w' : v.fiber F) :
    Module v.adicCompletion w'.1.adicCompletion :=
  Algebra.toModule

private theorem kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    KwF4R1V384aCompletionSemilocalBij K F E := by
  intro _ _ _ v
  have hsurj := kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels hdist v
  refine ⟨?_, hsurj⟩
  let srPi : Semiring ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  let algPi : Algebra v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    inferInstance
  let modPi : Module v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    @Algebra.toModule _ _ _ srPi algPi
  have hdimcod : Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion)
      = Module.finrank E F := by
    have hpi : (Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) : ℕ)
        = ∑ w' : v.fiber F, Module.finrank v.adicCompletion w'.1.adicCompletion := by
      convert Module.finrank_pi_fintype v.adicCompletion using 2 <;>
        exact fun i => inferInstance
    rw [hpi]
    have hsum := Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := E) (F' := F) v
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ w' : v.fiber F,
          ((Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ))
        = ∑ w' : v.fiber F,
            ((w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)) :=
          Finset.sum_congr rfl fun w' _ => hef v w'
      _ = ∑ w' ∈ v.fiber F,
            ((w'.ramificationIndex E : ℤ) * (w'.inertiaDeg E : ℤ)) :=
          Finset.sum_attach (v.fiber F)
            (fun w => (w.ramificationIndex E : ℤ) * (w.inertiaDeg E : ℤ))
      _ = (Module.finrank E F : ℤ) := hsum
  have hdimdom : Module.finrank v.adicCompletion (v.adicCompletion ⊗[E] F)
      = Module.finrank E F := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  have hsurj' : Function.Surjective
      (kwF4R1V384a_semilocalDiag F v).toLinearMap := hsurj
  have fdPi : FiniteDimensional v.adicCompletion
      ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  exact (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    v.adicCompletion (v.adicCompletion ⊗[E] F) _ _ _
    ((w' : v.fiber F) → w'.1.adicCompletion) _ modPi _ fdPi
    (hdimdom.trans hdimcod.symm)
    (kwF4R1V384a_semilocalDiag F v).toLinearMap).mpr hsurj'

end BijEngine

section SemilocalHeadline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V384a_trace_algebraMap_eq_completionTraceAt
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    Algebra.trace v.adicCompletion w'.1.adicCompletion (algebraMap F w'.1.adicCompletion g)
      = AlgebraicCurve.kwHgfV352_completionTraceAt v w'.1 w'.2 g := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  rfl

private theorem kwF4R1V384a_completionTraceSum_of_semilocalBij
    (hbij : KwF4R1V384aCompletionSemilocalBij K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E := by
  classical
  intro _ _ _ v g
  let e : v.adicCompletion ⊗[E] F ≃ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
    AlgEquiv.ofBijective (kwF4R1V384a_semilocalDiag F v) (hbij v)
  have freeFib : ∀ w' : v.fiber F, Module.Free v.adicCompletion w'.1.adicCompletion :=
    fun w' => Module.Free.of_divisionRing v.adicCompletion w'.1.adicCompletion
  rw [gapsw7_x3x_trace_decomposition_of_prod_iso E v.adicCompletion F
        (fun w' : v.fiber F => w'.1.adicCompletion) e g]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [show e ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w' from rfl,
    kwF4R1V384a_semilocalDiag_one_tmul,
    kwF4R1V384a_trace_algebraMap_eq_completionTraceAt]

private theorem kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_semilocalBij
    (kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF hdist hef)

end SemilocalHeadline

end Semilocal

section Discharge

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain TensorProduct IsLocalRing
open scoped AlgebraicCurve.Place Valued NNReal WithZero

section IsSeparableLift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_isSeparable_algebraMap_fiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    IsSeparable v.adicCompletion (algebraMap F w'.1.adicCompletion g) := by
  have hroot : Polynomial.aeval (R := v.adicCompletion)
      (algebraMap F w'.1.adicCompletion g)
      ((minpoly E g).map (algebraMap E v.adicCompletion)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap,
      show algebraMap F w'.1.adicCompletion g
          = IsScalarTower.toAlgHom E F w'.1.adicCompletion g from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmapsep : ((minpoly E g).map (algebraMap E v.adicCompletion)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E g)
  exact hmapsep.of_dvd (minpoly.dvd v.adicCompletion _ hroot)

private theorem kwF4R1V386a_isSeparable_fiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) :
    Algebra.IsSeparable v.adicCompletion w'.1.adicCompletion := by
  have hgen : Algebra.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro y
    obtain ⟨x, rfl⟩ := kwF4R1V384a_semilocalComponent_surjective v w' y
    induction x using TensorProduct.inductionOn with
    | tmul c g =>
      rw [kwF4R1V384a_semilocalComponent_tmul, ← Algebra.smul_def]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self g)) c
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have hsep : ∀ x ∈ Set.range (algebraMap F w'.1.adicCompletion),
      IsSeparable v.adicCompletion x := by
    rintro _ ⟨g, rfl⟩
    exact kwF4R1V386a_isSeparable_algebraMap_fiberCompletion v w' g
  have hgenI : IntermediateField.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (hgen ▸ Algebra.mem_top)
  have hsepAdj : Algebra.IsSeparable v.adicCompletion
      (IntermediateField.adjoin v.adicCompletion
        (Set.range (algebraMap F w'.1.adicCompletion))) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable v.adicCompletion
      w'.1.adicCompletion).mpr hsep
  rw [hgenI] at hsepAdj
  exact Algebra.IsSeparable.of_algHom v.adicCompletion
    (⊤ : IntermediateField v.adicCompletion w'.1.adicCompletion)
    (IntermediateField.topEquiv (F := v.adicCompletion)
      (E := w'.1.adicCompletion)).symm.toAlgHom

end IsSeparableLift

section DistinctKernels

open scoped Valued NNReal WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_spectralNorm_eq_absoluteValue [FiniteDimensional E F]
    (w' : Place K F) (y : w'.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion (w'.restrict E)
    letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
      Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
    spectralNorm (w'.restrict E).adicCompletion w'.adicCompletion y
      = kw_ffgc_absoluteValue E w' y := by
  let := kw_ffgc_rankOne_adicCompletion (w'.restrict E)
  let : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
  have : IsUltrametricDist (w'.restrict E).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  exact (spectralNorm_unique_field_norm_ext (f := kw_ffgc_absoluteValue E w')
    (kw_ffgc_absoluteValue_extends E w') y).symm

private theorem kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (y : w'.1.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion v
    letI : NontriviallyNormedField v.adicCompletion :=
      Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
    spectralNorm v.adicCompletion w'.1.adicCompletion y
      = kw_ffgc_absoluteValue E w'.1 y := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kwF4R1V386a_spectralNorm_eq_absoluteValue (K := K) (E := E) w' y

private theorem kwF4R1V386a_valuedAlgebraMap_le_one_iff (w' : Place K F) (g : F) :
    Valued.v (algebraMap F w'.adicCompletion g) ≤ 1 ↔ g ∈ w'.toValuationSubring :=
  AlgebraicCurve.kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff w' g

omit [Algebra K E] [IsScalarTower K E F] in
private theorem kwF4R1V386a_absoluteValue_algebraMap_le_one_iff
    (w' : Place K F) (g : F) :
    kw_ffgc_absoluteValue E w' (algebraMap F w'.adicCompletion g) ≤ 1
      ↔ g ∈ w'.toValuationSubring := by
  let := kw_ffgc_rankOne_adicCompletion w'
  have hr : (0 : ℝ) < ((w'.ramificationIndex E : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w'.ramificationIndex_pos (F := E)))
  change ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹ ≤ 1
    ↔ g ∈ w'.toValuationSubring
  constructor
  · intro hle
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      by_contra hgt
      have hgt' : 1 < ‖algebraMap F w'.adicCompletion g‖ := not_le.mp hgt
      exact absurd ((Real.one_lt_rpow_iff_of_pos (lt_trans one_pos hgt')).mpr
        (Or.inl ⟨hgt', hr⟩)) (not_lt.mpr hle)
    rw [Valued.toNormedField.norm_le_one_iff] at hn
    exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mp hn
  · intro hmem
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff]
      exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mpr hmem
    calc ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹
        ≤ 1 ^ ((w'.ramificationIndex E : ℝ))⁻¹ :=
          Real.rpow_le_rpow (norm_nonneg _) hn hr.le
      _ = 1 := Real.one_rpow _

private theorem kwF4R1V386a_distinctKernels :
    KwF4R1V384aDistinctKernels K F E := by
  intro _ _ _ v w' w'' hne hker
  apply hne
  have hsurj' := kwF4R1V384a_semilocalComponent_surjective v w'
  have hann : ∀ a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom,
      kwF4R1V384a_semilocalComponent F v w'' a = 0 := fun a ha => by
    have : a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w'').toRingHom :=
      hker ▸ ha
    exact this
  let σ : w'.1.adicCompletion →ₐ[v.adicCompletion] w''.1.adicCompletion :=
    (Ideal.Quotient.liftₐ _ (kwF4R1V384a_semilocalComponent F v w'') hann).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm.toAlgHom
  have hσcomp : ∀ x, σ (kwF4R1V384a_semilocalComponent F v w' x)
      = kwF4R1V384a_semilocalComponent F v w'' x := by
    intro x
    have hstep1 : (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm
        (kwF4R1V384a_semilocalComponent F v w' x) = Ideal.Quotient.mk _ x := by
      rw [show kwF4R1V384a_semilocalComponent F v w' x
          = Ideal.quotientKerAlgEquivOfSurjective hsurj' (Ideal.Quotient.mk _ x) from rfl,
        AlgEquiv.symm_apply_apply]
    change (Ideal.Quotient.liftₐ _ (kwF4R1V384a_semilocalComponent F v w'') hann)
      ((Ideal.quotientKerAlgEquivOfSurjective hsurj').symm
        ((kwF4R1V384a_semilocalComponent F v w') x)) = _
    erw [hstep1, Ideal.Quotient.lift_mk]
  have hσF : ∀ g : F, σ (algebraMap F w'.1.adicCompletion g)
      = algebraMap F w''.1.adicCompletion g := by
    intro g
    have h' := hσcomp ((1 : v.adicCompletion) ⊗ₜ[E] g)
    rwa [kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul,
      kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul] at h'
  let := kw_ffgc_rankOne_adicCompletion v
  let : NontriviallyNormedField v.adicCompletion :=
    Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hσspec : ∀ y, spectralNorm v.adicCompletion w''.1.adicCompletion (σ y)
      = spectralNorm v.adicCompletion w'.1.adicCompletion y := by
    intro y
    unfold spectralNorm
    congr 1
    exact minpoly.algHom_eq σ hσinj y
  refine Subtype.ext ?_
  refine AlgebraicCurve.Place.ext (K := K) (F := F) (SetLike.ext fun g => ?_)
  rw [← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w'.1 g,
    ← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w''.1 g,
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w'
      (algebraMap F w'.1.adicCompletion g),
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w''
      (algebraMap F w''.1.adicCompletion g),
    ← hσF g, hσspec]

end DistinctKernels

section FinrankCompletionEF

open IsLocalRing Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_ramificationIdx_completion_eq
    (w' : Place K F) :
    (maximalIdeal (w'.restrict E).adicCompletionIntegers).ramificationIdx'
      (maximalIdeal w'.adicCompletionIntegers) = w'.ramificationIndex E := by
  set e := w'.ramificationIndex E with he
  have hepos : 0 < e := w'.ramificationIndex_pos (F := E)
  obtain ⟨π, hπval⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer E
    (w'.restrict E).heightOneSpectrum
  have hmap : (maximalIdeal (w'.restrict E).adicCompletionIntegers).map
      (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = Ideal.span {algebraMap _ w'.adicCompletionIntegers π} := by
    rw [show maximalIdeal ((w'.restrict E).adicCompletionIntegers : Type _)
        = (w'.restrict E).heightOneSpectrum.completionIdeal E from rfl,
      IsDedekindDomain.HeightOneSpectrum.completionIdeal,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer E
        _ hπval,
      Ideal.map_span, Set.image_singleton]
  have hπval' : Valued.v (π : (w'.restrict E).adicCompletion)
      = (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) := hπval
  have hval : Valued.v ((algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers π : w'.adicCompletionIntegers) : w'.adicCompletion)
      = (↑(Multiplicative.ofAdd (-(e : ℤ))) : ℤᵐ⁰) := by
    rw [show ((algebraMap _ w'.adicCompletionIntegers π
          : w'.adicCompletionIntegers) : w'.adicCompletion)
        = kw_ffgc_adicCompletionComap E w' (π : (w'.restrict E).adicCompletion) from
      (kw_ffgc_adicCompletionComapIntegers_coe E w' π).symm,
      kw_ffgc_valued_adicCompletionComap, hπval', ← WithZero.coe_pow, WithZero.coe_inj,
      ← ofAdd_nsmul, nsmul_eq_mul, mul_neg_one, he]
  refine Ideal.ramificationIdx'_spec ?_ ?_
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval]
    simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le, not_le]
    omega

private theorem kwF4R1V386a_integersToCompletion_commute
    (w' : Place K F) (a : (w'.restrict E).toValuationSubring) :
    algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers
        (algebraMap (w'.restrict E).toValuationSubring
          (w'.restrict E).adicCompletionIntegers a)
      = algebraMap w'.toValuationSubring w'.adicCompletionIntegers
          (restrictInclusion E w' a) := by
  apply Subtype.ext
  exact (kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' (a : E)).symm

private theorem kwF4R1V386a_inertiaDeg_completion_eq
    (w' : Place K F) :
    (maximalIdeal w'.adicCompletionIntegers).inertiaDeg
      (w'.restrict E).adicCompletionIntegers = w'.inertiaDeg E := by
  have : IsLocalHom (algebraMap (w'.restrict E).adicCompletionIntegers
      w'.adicCompletionIntegers) :=
    kw_ffgc_isLocalHom_adicCompletionComapIntegers E w'
  have : (maximalIdeal w'.adicCompletionIntegers).LiesOver
      (maximalIdeal (w'.restrict E).adicCompletionIntegers) := by
    have hcomap : (maximalIdeal w'.adicCompletionIntegers).comap
        (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = maximalIdeal (w'.restrict E).adicCompletionIntegers :=
      ((IsLocalRing.local_hom_TFAE (algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers)).out 1 5).mp ‹IsLocalHom _›
    exact ⟨hcomap.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal
    (maximalIdeal (w'.restrict E).adicCompletionIntegers)
    (maximalIdeal w'.adicCompletionIntegers)]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (kw_ffgc_residueFieldEquivCompletionResidueField (w'.restrict E))
    (kw_ffgc_residueFieldEquivCompletionResidueField w') ?_
  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact congrArg (IsLocalRing.residue w'.adicCompletionIntegers)
    (kwF4R1V386a_integersToCompletion_commute (K := K) (E := E) w' a)

private theorem kwF4R1V386a_finrankCompletionEF [Algebra.IsSeparable E F] :
    KwF4R1V384aFinrankCompletionEF K F E := by
  intro _ _ _ v wfib
  have hv : wfib.1.restrict E = v := Place.mem_fiber.mp wfib.2
  have hsep : Algebra.IsSeparable v.adicCompletion wfib.1.adicCompletion :=
    kwF4R1V386a_isSeparable_fiberCompletion v wfib
  rcases wfib with ⟨w', hw'⟩
  dsimp only at hv hsep ⊢
  subst hv
  have : Algebra.IsSeparable (w'.restrict E).adicCompletion w'.adicCompletion := hsep
  have : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  have : IsIntegralClosure w'.adicCompletionIntegers
      (w'.restrict E).adicCompletionIntegers w'.adicCompletion :=
    kw_ffgc_isIntegralClosure_adicCompletionIntegers E w'
  have : IsNoetherian (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    IsIntegralClosure.isNoetherian (w'.restrict E).adicCompletionIntegers
      (w'.restrict E).adicCompletion w'.adicCompletion w'.adicCompletionIntegers
  have : Module.Finite (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    Module.IsNoetherian.finite _ _
  have hpne : maximalIdeal (w'.restrict E).adicCompletionIntegers ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField _
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  have : FaithfulSMul (w'.restrict E).adicCompletionIntegers
      w'.adicCompletionIntegers :=
    FaithfulSMul.of_field_isFractionRing (w'.restrict E).adicCompletionIntegers
      w'.adicCompletionIntegers (w'.restrict E).adicCompletion w'.adicCompletion
  have : Module.Flat (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  let _ := Fintype.ofFinite
    ((maximalIdeal (w'.restrict E).adicCompletionIntegers).primesOver
      w'.adicCompletionIntegers)
  let q : (maximalIdeal (w'.restrict E).adicCompletionIntegers).primesOver
      w'.adicCompletionIntegers :=
    ⟨maximalIdeal w'.adicCompletionIntegers, by
      rw [IsLocalRing.primesOver_eq w'.adicCompletionIntegers hpne]
      exact Set.mem_singleton _⟩
  let _ : Unique ((maximalIdeal (w'.restrict E).adicCompletionIntegers).primesOver
      w'.adicCompletionIntegers) :=
    { default := q
      uniq := fun r => by
        apply Subtype.ext
        have hr : (r.1 : Ideal w'.adicCompletionIntegers) ∈
            ({maximalIdeal w'.adicCompletionIntegers} : Set (Ideal w'.adicCompletionIntegers)) :=
          (Set.ext_iff.mp
            (IsLocalRing.primesOver_eq w'.adicCompletionIntegers hpne) r.1).mp r.2
        exact Set.mem_singleton_iff.mp hr }
  have hef := Ideal.sum_ramification_inertia_eq_finrank
    (maximalIdeal (w'.restrict E).adicCompletionIntegers) w'.adicCompletionIntegers
  rw [← IsFractionRing.finrank_eq (w'.restrict E).adicCompletionIntegers
      (w'.restrict E).adicCompletion w'.adicCompletionIntegers w'.adicCompletion] at hef
  have hef' :
      ((default : (maximalIdeal (w'.restrict E).adicCompletionIntegers).primesOver
          w'.adicCompletionIntegers).1).ramificationIdx
            (w'.restrict E).adicCompletionIntegers *
        ((default : (maximalIdeal (w'.restrict E).adicCompletionIntegers).primesOver
          w'.adicCompletionIntegers).1).inertiaDeg
            (w'.restrict E).adicCompletionIntegers =
        Module.finrank (w'.restrict E).adicCompletion w'.adicCompletion := by
    simpa only [Fintype.sum_unique] using hef
  have hdefault :
      (default : (maximalIdeal (w'.restrict E).adicCompletionIntegers).primesOver
        w'.adicCompletionIntegers) = q := Subsingleton.elim _ _
  rw [hdefault] at hef'
  change
    (maximalIdeal w'.adicCompletionIntegers).ramificationIdx
        (w'.restrict E).adicCompletionIntegers *
      (maximalIdeal w'.adicCompletionIntegers).inertiaDeg
        (w'.restrict E).adicCompletionIntegers =
      Module.finrank (w'.restrict E).adicCompletion w'.adicCompletion at hef'
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
      (maximalIdeal (w'.restrict E).adicCompletionIntegers)
      (maximalIdeal w'.adicCompletionIntegers) hpne] at hef'
  rw [kwF4R1V386a_ramificationIdx_completion_eq (K := K) w',
    kwF4R1V386a_inertiaDeg_completion_eq (K := K) w'] at hef'
  exact_mod_cast hef'.symm

end FinrankCompletionEF

section DischargeHeadline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_completionTraceSum_of_isSeparable [Algebra.IsSeparable E F] :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    kwF4R1V386a_distinctKernels kwF4R1V386a_finrankCompletionEF

end DischargeHeadline

end Discharge

end

theorem _root_.AlgebraicCurve.completionTraceSum_of_isSeparable
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsSeparable E F] :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V386a_completionTraceSum_of_isSeparable (K := K) (F := F) (E := E)
#print axioms kwF4R1V386a_distinctKernels
#print axioms kwF4R1V386a_finrankCompletionEF
#print axioms kwF4R1V384a_completionTraceSum_of_semilocalBij
#print axioms kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF
#print axioms AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
end AlgebraicCurves.FunctionFields.Proofs.CompletionTraceSum_of_isSeparable
end ProofImplementation
