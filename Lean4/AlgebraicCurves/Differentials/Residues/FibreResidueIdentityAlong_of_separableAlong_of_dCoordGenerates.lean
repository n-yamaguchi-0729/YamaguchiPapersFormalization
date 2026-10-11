/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Differentials.Residues.FibreIdentity
import AlgebraicCurves.Differentials.Residues.ResidueTraceCompletionCommute_v2
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.FunctionFields.CompletionTraceSum_of_isSeparable
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Residues.Construction

/-!
# Differentials, residues, and divisor correspondences

Separable extensions with generating coordinate differentials satisfy the fibre residue identity.
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs
namespace FibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates

noncomputable section

open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.KaehlerDifferential
open _root_.ModularCurve.KwF4R1V391a

namespace AlgebraicCurve

/-- The residue sum of a pulled-back differential over a place fibre agrees with the base
differential residue of the field trace. -/
def FiberKaehlerCotraceResidueIdentity
    (K F E : Type*) [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
    [Algebra.IsIntegral E F] : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (f : F),
    ∑ w ∈ v.fiber F,
        kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w =
      kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v

variable {K F E : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

theorem localResidueCompletion_spec (v : Place K E) (xh : v.adicCompletion)
    {x : E} (hx : algebraMap E v.adicCompletion x - xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = v.localResidue x := by
  unfold kwHgfV352_localResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x) =
      (algebraMap E v.adicCompletion x₀ - xh) -
        (algebraMap E v.adicCompletion x - xh) := by
    rw [map_sub]
    ring
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hx
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 :=
    v.localResidue_eq_zero_of_ord_nonneg (Or.inr (v.ord_nonneg_of_mem hov))
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem localResidueCompletion_algebraMap (v : Place K E) (x : E) :
    kwHgfV352_localResidueCompletion v (algebraMap E v.adicCompletion x) =
      v.localResidue x :=
  localResidueCompletion_spec v _ (by rw [sub_self]; exact zero_mem _)

theorem localResidueCompletion_add (v : Place K E) (xh yh : v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (xh + yh) =
      kwHgfV352_localResidueCompletion v xh + kwHgfV352_localResidueCompletion v yh := by
  obtain ⟨x, hx⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh
  obtain ⟨y, hy⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v yh
  have heq : algebraMap E v.adicCompletion (x + y) - (xh + yh) =
      (algebraMap E v.adicCompletion x - xh) +
        (algebraMap E v.adicCompletion y - yh) := by
    rw [map_add]
    ring
  rw [localResidueCompletion_spec v xh hx,
    localResidueCompletion_spec v yh hy,
    localResidueCompletion_spec v (xh + yh) (x := x + y) (heq ▸ add_mem hx hy),
    map_add]

theorem localResidueCompletion_sum (v : Place K E) {ι : Type*}
    (s : Finset ι) (f : ι → v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (∑ i ∈ s, f i) =
      ∑ i ∈ s, kwHgfV352_localResidueCompletion v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (0 : v.adicCompletion) = algebraMap E v.adicCompletion 0 from
        (_root_.map_zero _).symm, localResidueCompletion_algebraMap, _root_.map_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, localResidueCompletion_add, ih, Finset.sum_insert ha]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]
    [Algebra.IsIntegral E F] in
theorem kaehlerPullback_smul (g : E) (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E (g • ωE) =
      algebraMap E F g • kaehlerPullback K F E ωE := by
  change (KaehlerDifferential.map K K E F) (g • ωE) =
    algebraMap E F g • (KaehlerDifferential.map K K E F) ωE
  rw [LinearMap.map_smul, algebra_compatible_smul F g]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E] in
theorem completionTraceF_apply [FiniteDimensional E F] (w : Place K F) (g : F) :
    kw_ffgc_completionTraceF' E w g =
      Algebra.trace (w.restrict E).adicCompletion w.adicCompletion
        (algebraMap F w.adicCompletion g) := rfl

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E] in
theorem completionTraceF_mul_algebraMap [FiniteDimensional E F]
    (w : Place K F) (g : F) (c : E) :
    kw_ffgc_completionTraceF' E w (g * algebraMap E F c) =
      kw_ffgc_completionTraceF' E w g *
        algebraMap E (w.restrict E).adicCompletion c := by
  rw [completionTraceF_apply, completionTraceF_apply, map_mul,
    kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w c,
    mul_comm (algebraMap F w.adicCompletion g) _, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul, mul_comm]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E] in
theorem completionTraceAt_mul_algebraMap [FiniteDimensional E F]
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F) (c : E) :
    kwHgfV352_completionTraceAt v w hw (g * algebraMap E F c) =
      kwHgfV352_completionTraceAt v w hw g *
        algebraMap E v.adicCompletion c := by
  have hv : w.restrict E = v := Place.mem_fiber.mp hw
  subst hv
  change (Place.mem_fiber.mp hw ▸ kw_ffgc_completionTraceF' E w
      (g * algebraMap E F c)) =
    (Place.mem_fiber.mp hw ▸ kw_ffgc_completionTraceF' E w g) *
      algebraMap E (w.restrict E).adicCompletion c
  rw [completionTraceF_mul_algebraMap w g c]

omit [HasCanonicalLocalResidueKStar K E] [Algebra.IsIntegral E F] in
theorem kaehlerResidueTerm_pullback_diagonal_eq_dCoord_shift
    [Nontrivial Ω[F⁄K]] [Nontrivial Ω[E⁄K]]
    (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (ωE : Ω[E⁄K]) (g : F) :
    kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F g) w =
      kaehlerResidueTerm (kaehlerPullback K F E v.dCoord)
        (diagonalHom K F (g * algebraMap E F (v.differentialCoeff ωE))) w := by
  unfold kaehlerResidueTerm
  congr 2
  change g * w.differentialCoeff (kaehlerPullback K F E ωE) =
    g * algebraMap E F (v.differentialCoeff ωE) *
      w.differentialCoeff (kaehlerPullback K F E v.dCoord)
  conv_lhs =>
    rw [← v.differentialCoeff_smul_dCoord ωE, kaehlerPullback_smul,
      w.differentialCoeff_smul]
  rw [mul_assoc]

theorem fiberKaehlerCotraceResidueIdentity_of_rtcc_cts
    [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] [∀ v : Place K E, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]
    (hRTCC : ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F],
      KwF4R1V391aResidueTraceCompletionCommute K F E)
    (hCTS : KwHgfV352CompletionTraceSum K F E) :
    FiberKaehlerCotraceResidueIdentity K F E := by
  intro _ _ ωE _hωE _hωF v f
  calc
    ∑ w ∈ v.fiber F,
          kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w =
        ∑ w' ∈ (v.fiber F).attach,
          Algebra.trace K v.ResidueField
            (kwHgfV352_localResidueCompletion v
              (kwHgfV352_completionTraceAt v w'.1 w'.2 f *
                algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
      rw [← Finset.sum_attach (v.fiber F)
        (fun w => kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w)]
      refine Finset.sum_congr rfl fun w' _ => ?_
      rw [kaehlerResidueTerm_pullback_diagonal_eq_dCoord_shift v w'.1 ωE f,
        hRTCC v w'.1 w'.2 (f * algebraMap E F (v.differentialCoeff ωE)),
        completionTraceAt_mul_algebraMap v w'.1 w'.2 f
          (v.differentialCoeff ωE)]
    _ = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            ((∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 f) *
              algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
      rw [Finset.sum_mul,
        localResidueCompletion_sum v (v.fiber F).attach _, map_sum]
    _ = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (algebraMap E v.adicCompletion (Algebra.trace E F f) *
              algebraMap E v.adicCompletion (v.differentialCoeff ωE))) := by
      rw [← hCTS v f]
    _ = Algebra.trace K v.ResidueField
          (v.localResidue (Algebra.trace E F f * v.differentialCoeff ωE)) := by
      rw [← map_mul, localResidueCompletion_algebraMap v]
    _ = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v := by
      unfold kaehlerResidueTerm
      rw [diagonalHom_apply]

theorem kaehlerResidueTerm_smul_diagonal
    [Nontrivial Ω[F⁄K]] (g : F) (ω : Ω[F⁄K]) (f : F)
    (v : Place K F) [v.DCoordGenerates] :
    kaehlerResidueTerm (g • ω) (diagonalHom K F f) v =
      kaehlerResidueTerm ω (diagonalHom K F (g * f)) v := by
  unfold kaehlerResidueTerm
  simp only [diagonalHom_apply]
  rw [v.differentialCoeff_smul,
    show f * (g * v.differentialCoeff ω) = g * f * v.differentialCoeff ω by ring]

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E] in
theorem finsum_place_eq_finsum_fiber_sum
    {M : Type*} [AddCommMonoid M] [HasPrincipalDivisors K F]
    (g : Place K F → M) (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F, g w := by
  classical
  set S := hg.toFinset with hS
  set T := S.image (fun w => w.restrict E) with hT
  rw [finsum_eq_finsetSum_of_support_subset g
    (s := S) (fun w hw => (hS ▸ hg.mem_toFinset.mpr hw))]
  have hsup :
      Function.support (fun v : Place K E => ∑ w ∈ v.fiber F, g w) ⊆ ↑T := by
    intro v hv
    simp only [Function.mem_support] at hv
    obtain ⟨w, hwfib, hwne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    exact Finset.mem_coe.mpr (hT ▸ Finset.mem_image.mpr
      ⟨w, hS ▸ hg.mem_toFinset.mpr hwne, Place.mem_fiber.mp hwfib⟩)
  rw [finsum_eq_finsetSum_of_support_subset _ hsup]
  have hfib : ∀ v ∈ T,
      ∑ w ∈ v.fiber F, g w = ∑ w ∈ S with w.restrict E = v, g w := by
    intro v _
    refine (Finset.sum_subset ?_ ?_).symm
    · intro w hw
      exact Place.mem_fiber.mpr (Finset.mem_filter.mp hw).2
    · intro w hwfib hwfilt
      by_contra hgw
      exact hwfilt (Finset.mem_filter.mpr
        ⟨hS ▸ hg.mem_toFinset.mpr hgw, Place.mem_fiber.mp hwfib⟩)
  rw [Finset.sum_congr rfl hfib]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => hT ▸ Finset.mem_image.mpr ⟨w, hw, rfl⟩) g).symm

theorem residueTheorem_of_fiberKaehlerCotraceResidueIdentity
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalDivisor (K := K) (F := E)]
    [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (hE : ResidueTheorem K E) {ωE₀ : Ω[E⁄K]} (hωE₀ : ωE₀ ≠ 0)
    (hgen : kaehlerPullback K F E ωE₀ ≠ 0)
    (hIdent : FiberKaehlerCotraceResidueIdentity K F E) :
    ResidueTheorem K F := by
  intro ωF hωF f
  rcases isEmpty_or_nonempty (Place K F) with hempty | hne
  · rw [weilOfKaehler_apply]
    exact finsum_eq_zero_of_forall_eq_zero fun w => (hempty.false w).elim
  obtain ⟨w₀⟩ := hne
  have hcoeff : w₀.differentialCoeff (kaehlerPullback K F E ωE₀) ≠ 0 :=
    w₀.differentialCoeff_ne_zero hgen
  set c : F := w₀.differentialCoeff ωF *
    (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹ with hc
  have hωF_eq : ωF = c • kaehlerPullback K F E ωE₀ := by
    symm
    calc
      c • kaehlerPullback K F E ωE₀ =
          c • (w₀.differentialCoeff (kaehlerPullback K F E ωE₀) • w₀.dCoord) := by
        rw [w₀.differentialCoeff_smul_dCoord]
      _ = (c * w₀.differentialCoeff (kaehlerPullback K F E ωE₀)) • w₀.dCoord := by
        rw [smul_smul]
      _ = w₀.differentialCoeff ωF • w₀.dCoord := by
        rw [hc, mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
      _ = ωF := w₀.differentialCoeff_smul_dCoord ωF
  have hterm : ∀ w : Place K F,
      kaehlerResidueTerm ωF (diagonalHom K F f) w =
        kaehlerResidueTerm (kaehlerPullback K F E ωE₀)
          (diagonalHom K F (c * f)) w := fun w => by
    conv_lhs => rw [hωF_eq]
    exact kaehlerResidueTerm_smul_diagonal c (kaehlerPullback K F E ωE₀) f w
  have hsup :
      (Function.support (kaehlerResidueTerm (kaehlerPullback K F E ωE₀)
        (diagonalHom K F (c * f)))).Finite :=
    kaehlerResidueTerm_support_finite_of_adeleSpace hgen (diagonal_mem_adeleSpace _)
  calc
    weilOfKaehler K F hωF ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ =
        ∑ᶠ w : Place K F, kaehlerResidueTerm ωF (diagonalHom K F f) w :=
      weilOfKaehler_apply hωF _
    _ = ∑ᶠ w : Place K F,
        kaehlerResidueTerm (kaehlerPullback K F E ωE₀)
          (diagonalHom K F (c * f)) w := finsum_congr hterm
    _ = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F,
        kaehlerResidueTerm (kaehlerPullback K F E ωE₀)
          (diagonalHom K F (c * f)) w :=
      finsum_place_eq_finsum_fiber_sum (E := E) _ hsup
    _ = ∑ᶠ v : Place K E,
        kaehlerResidueTerm ωE₀
          (diagonalHom K E (Algebra.trace E F (c * f))) v :=
      finsum_congr fun v => hIdent hωE₀ hgen v _
    _ = 0 := by
      have hzero := hE hωE₀ (Algebra.trace E F (c * f))
      rw [weilOfKaehler_apply] at hzero
      exact hzero

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]
    [Algebra.IsIntegral E F] in
theorem mapBaseChange_surjective_of_subsingleton [Subsingleton Ω[F⁄E]] :
    Function.Surjective (KaehlerDifferential.mapBaseChange K E F) := by
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange,
    LinearMap.ker_eq_top]
  exact Subsingleton.elim _ _

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]
    [Algebra.IsIntegral E F] in
theorem exists_kaehlerPullback_ne_zero
    [Algebra.IsSeparable E F] [Nontrivial Ω[F⁄K]] :
    ∃ ωE : Ω[E⁄K], kaehlerPullback K F E ωE ≠ 0 := by
  let _ : Algebra.FormallyUnramified E F := .of_isSeparable E F
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange K E F) :=
    mapBaseChange_surjective_of_subsingleton
  by_contra hzero
  simp only [not_exists, ne_eq, not_not] at hzero
  have hmbc0 : KaehlerDifferential.mapBaseChange K E F = 0 := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
        rw [KaehlerDifferential.mapBaseChange_tmul, LinearMap.zero_apply]
        change x • kaehlerPullback K F E y = 0
        rw [hzero y, smul_zero]
    | add _ _ h1 h2 =>
        simp only [map_add, h1, h2, LinearMap.zero_apply, add_zero]
  obtain ⟨ωF, hωF⟩ := exists_ne (0 : Ω[F⁄K])
  obtain ⟨t, ht⟩ := hsurj ωF
  exact hωF (ht ▸ congrFun (congrArg DFunLike.coe hmbc0) t)

omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]
    [Algebra.IsIntegral E F] in
theorem kaehlerPullback_ne_zero
    [Algebra.IsSeparable E F] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[E⁄K]]
    (v : Place K E) [v.DCoordGenerates] {ωE : Ω[E⁄K]} (hωE : ωE ≠ 0) :
    kaehlerPullback K F E ωE ≠ 0 := by
  obtain ⟨ω₁, hω₁⟩ := exists_kaehlerPullback_ne_zero (K := K) (F := F) (E := E)
  have hd : kaehlerPullback K F E v.dCoord ≠ 0 := by
    intro hzero
    refine hω₁ ?_
    rw [← v.differentialCoeff_smul_dCoord ω₁,
      show kaehlerPullback K F E (v.differentialCoeff ω₁ • v.dCoord) =
        v.differentialCoeff ω₁ • kaehlerPullback K F E v.dCoord from
        (KaehlerDifferential.map K K E F).map_smul _ _, hzero, smul_zero]
  intro hzero
  have hc : v.differentialCoeff ωE ≠ 0 := v.differentialCoeff_ne_zero hωE
  apply hd
  have key : v.differentialCoeff ωE • kaehlerPullback K F E v.dCoord = 0 := by
    rw [← show kaehlerPullback K F E (v.differentialCoeff ωE • v.dCoord) =
        v.differentialCoeff ωE • kaehlerPullback K F E v.dCoord from
        (KaehlerDifferential.map K K E F).map_smul _ _,
      v.differentialCoeff_smul_dCoord ωE, hzero]
  rcases smul_eq_zero.mp key with h | h
  · exact absurd h hc
  · exact h

end AlgebraicCurve

theorem _root_.AlgebraicCurve.fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
    {K F F' : Type*} [Field K] [PerfectField K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [IsCurveOver K F] [IsCurveOver K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hsep : SeparableAlong K φ) : FibreResidueIdentityAlong φ hφ := by
  let _ := algebraAlong φ
  let _ := isScalarTower_along φ
  let _ := isIntegral_along φ hφ
  let _ : Module.Finite F F' := hfin
  let _ : Algebra.IsSeparable F F' := hsep
  intro v ω f'
  change ∑ w ∈ v.fiber F',
      kaehlerResidueTerm (kaehlerPullback K F' F ω) (diagonalHom K F' f') w =
    kaehlerResidueTerm ω (diagonalHom K F (Algebra.trace F F' f')) v
  have hId : AlgebraicCurve.FiberKaehlerCotraceResidueIdentity K F' F :=
    AlgebraicCurve.fiberKaehlerCotraceResidueIdentity_of_rtcc_cts
      (by
        intro _ _
        exact AlgebraicCurve.residueTraceCompletionCommute_v2
          (K := K) (F := F') (E := F))
      (AlgebraicCurve.completionTraceSum_of_isSeparable (K := K) (F := F') (E := F))
  by_cases hω : ω = 0
  · subst hω
    have hpb0 : kaehlerPullback K F' F (0 : Ω[F⁄K]) = 0 :=
      (KaehlerDifferential.map K K F F').map_zero
    have hzF :
        kaehlerResidueTerm (0 : Ω[F⁄K])
          (diagonalHom K F (Algebra.trace F F' f')) v = 0 := by
      simp only [kaehlerResidueTerm, Place.differentialCoeff_zero, mul_zero, map_zero]
    have hzF' : ∀ w ∈ v.fiber F',
        kaehlerResidueTerm (kaehlerPullback K F' F (0 : Ω[F⁄K]))
          (diagonalHom K F' f') w = 0 := by
      intro w _
      rw [hpb0]
      simp only [kaehlerResidueTerm, Place.differentialCoeff_zero, mul_zero, map_zero]
    rw [Finset.sum_eq_zero hzF', hzF]
  · exact hId hω
      (AlgebraicCurve.kaehlerPullback_ne_zero (K := K) (F := F') (E := F) v hω) v f'

end

end FibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
end AlgebraicCurves.Differentials.Residues.Proofs
end ProofImplementation

open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
