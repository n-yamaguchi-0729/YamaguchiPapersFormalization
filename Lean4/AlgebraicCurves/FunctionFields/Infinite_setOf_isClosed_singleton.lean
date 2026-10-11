/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_infinite_setOf_isClosed_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Valuations.Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint

/-!
# Infinite setOf isClosed singleton

An integral curve locally of finite type over a field has infinitely many closed points.
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Infinite_setOf_isClosed_singleton

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace LInf
open _root_.AlgebraicCurve

theorem isField_of_isMaximal_bot (A : Type*) [CommRing A] [Nontrivial A]
    (h : (⊥ : Ideal A).IsMaximal) : IsField A := by
  exact Ring.isField_iff_maximal_bot.mpr h

theorem isField_of_finite_maximalSpectrum (A : Type*) [CommRing A] [IsDomain A] [IsJacobsonRing A]
    [Finite (MaximalSpectrum A)] : IsField A := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out ‹_› Ideal.isRadical_bot
  have hprod : (Finset.univ : Finset (MaximalSpectrum A)).prod (fun m => m.asIdeal) ≤ ⊥ := by
    rw [← hjac]
    refine le_trans Ideal.prod_le_inf ?_
    refine le_sInf fun J hJ => ?_
    exact Finset.inf_le (Finset.mem_univ (⟨J, hJ.2⟩ : MaximalSpectrum A))
  obtain ⟨m, -, hm⟩ := (Ideal.IsPrime.prod_le (Ideal.isPrime_bot (α := A))).mp hprod
  have hm0 : m.asIdeal = ⊥ := le_bot_iff.mp hm
  exact isField_of_isMaximal_bot A (hm0 ▸ m.isMaximal)

end AlgebraicCurve.LInf

open AlgebraicCurve.LInf in
theorem _root_.AlgebraicCurve.infinite_setOf_isClosed_singleton
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] :
    {x : C | IsClosed ({x} : Set C)}.Infinite := by
  classical
  obtain ⟨U, hU, V, hV, hηV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c)
      (genericPoint C)
  have hfU : c.base (genericPoint C) ∈ U := hle hηV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (c.base (genericPoint C))]; exact hfU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(C, V) := (c.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  let : Algebra k Γ(C, V) := ψ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(C, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have : Algebra.FiniteType k Γ(C, V) := by
    obtain ⟨g, hg⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k Γ(C, V)
    let : Algebra (MvPolynomial (Fin 1) k) Γ(C, V) := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin 1) k) Γ(C, V) := hg
    have : IsScalarTower k (MvPolynomial (Fin 1) k) Γ(C, V) :=
      IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
    exact (inferInstance : Algebra.FiniteType k (MvPolynomial (Fin 1) k)).trans
      (inferInstance : Algebra.FiniteType (MvPolynomial (Fin 1) k) Γ(C, V))
  have : IsJacobsonRing Γ(C, V) := isJacobsonRing_of_finiteType (A := k)
  have hnf : ¬ IsField Γ(C, V) := by
    intro hF
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(C, V)
    have := hm
    obtain ⟨_, hdvr⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
        (k := k) m
    have h0 : (0 : Γ(C, V)) ∉ m.primeCompl := fun h => h m.zero_mem
    have hbij := hF.localization_map_bijective (Rₘ := Localization.AtPrime m) h0
    exact IsDiscreteValuationRing.not_isField (Localization.AtPrime m)
      ((RingEquiv.ofBijective _ hbij).symm.toMulEquiv.isField hF)
  by_contra hinf
  have hfin : {x : C | IsClosed ({x} : Set C)}.Finite := Set.not_infinite.mp hinf
  let g : MaximalSpectrum Γ(C, V) → C := fun m => hV.fromSpec ⟨m.asIdeal, m.isMaximal.isPrime⟩
  have hg_closed : ∀ m, IsClosed ({g m} : Set C) := by
    intro m
    apply AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c
    intro hη
    apply hnf
    have hbot : (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum Γ(C, V)) = ⊥ := by
      apply hV.fromSpec.isOpenEmbedding.injective
      change g m = _
      rw [hη, ← genericPoint_eq_bot_of_affine, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
    have hm0 : m.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal hbot
    exact isField_of_isMaximal_bot _ (hm0 ▸ m.isMaximal)
  have hg_inj : Function.Injective g := by
    intro m m' h
    have h' := hV.fromSpec.isOpenEmbedding.injective h
    exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal h')
  have : Finite (MaximalSpectrum Γ(C, V)) := by
    have := hfin.to_subtype
    refine Finite.of_injective
      (fun m => (⟨g m, hg_closed m⟩ : {x : C | IsClosed ({x} : Set C)})) ?_
    intro m m' h
    apply hg_inj
    simp only [Subtype.mk.injEq] at h
    exact h
  exact hnf (isField_of_finite_maximalSpectrum Γ(C, V))
end AlgebraicCurves.FunctionFields.Proofs.Infinite_setOf_isClosed_singleton
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
