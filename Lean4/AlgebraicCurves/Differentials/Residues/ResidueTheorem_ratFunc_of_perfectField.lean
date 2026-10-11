/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Differentials.Uniformizer
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Differentials.Residues.TateTrace
import AlgebraicCurves.Differentials.Residues.Construction
import AlgebraicCurves.Places.Rational.Infinity
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.OverDVR
import AlgebraicCurves.Places.Rational.RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
import AlgebraicCurves.Places.Rational.RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero
import AlgebraicCurves.Places.Rational.RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero

/-!
# Residue Theorem rat Func of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.RatFuncResidue
open _root_.AlgebraicCurves.Differentials.Residues.Proofs
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

namespace J1ThirteenPlaneModel
end J1ThirteenPlaneModel
namespace J1ThirteenPicZeroFibreDiamond
end J1ThirteenPicZeroFibreDiamond
namespace J1ThirteenPicZeroLiteralChordChain
end J1ThirteenPicZeroLiteralChordChain
namespace J1ThirteenPicZeroPlaceDictionary
end J1ThirteenPicZeroPlaceDictionary
namespace J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
end J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
namespace J1ThirteenPicZeroLitPic0Comparison
end J1ThirteenPicZeroLitPic0Comparison
namespace J1ThirteenX113RiemannRochRows
end J1ThirteenX113RiemannRochRows
namespace MazurTate1973Mt31b
end MazurTate1973Mt31b
namespace J1ThirteenX113PackageHeldRowOne
end J1ThirteenX113PackageHeldRowOne
namespace MilneAvAg9bRd9DictionaryHeld3Closure
end MilneAvAg9bRd9DictionaryHeld3Closure
namespace J1ThirteenX113OrdRowWellDefinedReduction
end J1ThirteenX113OrdRowWellDefinedReduction
namespace MilneAvAg9bRd10EllKFinUpperRow
end MilneAvAg9bRd10EllKFinUpperRow
namespace MilneAvAg9bRd11X113TowerPowerBasis
end MilneAvAg9bRd11X113TowerPowerBasis
namespace Ag9b11bX113HwdUnitDischarge
end Ag9b11bX113HwdUnitDischarge
namespace MilneAvAg9bRd11DictionaryBinderShrink
end MilneAvAg9bRd11DictionaryBinderShrink
namespace MilneAvAg9bRd12X113AssemblyRetirement
end MilneAvAg9bRd12X113AssemblyRetirement
namespace MilneAvAg9bRd12T1P1InftyResidue
end MilneAvAg9bRd12T1P1InftyResidue
namespace MilneAvAg9bRd12X113LocalDatumMint
end MilneAvAg9bRd12X113LocalDatumMint
namespace MilneAvAg9bRd12X113FiveRowUpgrade
end MilneAvAg9bRd12X113FiveRowUpgrade
namespace AdjoinRoot
open _root_.AdjoinRoot
open _root_.AdjoinRoot
end AdjoinRoot
namespace Ag9b11bX113HwdUnitDischarge
end Ag9b11bX113HwdUnitDischarge
namespace Algebra
open _root_.Algebra
open _root_.Algebra
end Algebra
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace CongruenceSubgroup
open _root_.CongruenceSubgroup
end CongruenceSubgroup
namespace CoordinateRing
end CoordinateRing
namespace IntermediateField
open _root_.IntermediateField
open _root_.IntermediateField
end IntermediateField
namespace IntermediateField
open _root_.IntermediateField
namespace algebraAdjoinAdjoin
open _root_.IntermediateField.algebraAdjoinAdjoin
open _root_.IntermediateField
end IntermediateField.algebraAdjoinAdjoin
namespace IsDedekindDomain
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsLocalRing
open _root_.IsLocalRing
open _root_.IsLocalRing
end IsLocalRing
namespace J1ThirteenPicZeroFibreDiamond
end J1ThirteenPicZeroFibreDiamond
namespace J1ThirteenPicZeroLitPic0Comparison
end J1ThirteenPicZeroLitPic0Comparison
namespace J1ThirteenPicZeroLiteralChordChain
end J1ThirteenPicZeroLiteralChordChain
namespace J1ThirteenPicZeroPlaceDictionary
end J1ThirteenPicZeroPlaceDictionary
namespace J1ThirteenPicZeroPlaceDictionary
namespace PlaceConstruction
end J1ThirteenPicZeroPlaceDictionary.PlaceConstruction
namespace J1ThirteenPlaneModel
end J1ThirteenPlaneModel
namespace J1ThirteenX113OrdRowWellDefinedReduction
end J1ThirteenX113OrdRowWellDefinedReduction
namespace J1ThirteenX113PackageHeldRowOne
end J1ThirteenX113PackageHeldRowOne
namespace J1ThirteenX113RiemannRochRows
end J1ThirteenX113RiemannRochRows
namespace KaehlerDifferential
open _root_.KaehlerDifferential
open _root_.KaehlerDifferential
end KaehlerDifferential
namespace MazurTate1973Mt31b
end MazurTate1973Mt31b
namespace MilneAvAg9bRd10EllKFinUpperRow
end MilneAvAg9bRd10EllKFinUpperRow
namespace MilneAvAg9bRd11DictionaryBinderShrink
end MilneAvAg9bRd11DictionaryBinderShrink
namespace MilneAvAg9bRd11X113TowerPowerBasis
end MilneAvAg9bRd11X113TowerPowerBasis
namespace MilneAvAg9bRd12T1P1InftyResidue
end MilneAvAg9bRd12T1P1InftyResidue
namespace MilneAvAg9bRd12X113AssemblyRetirement
end MilneAvAg9bRd12X113AssemblyRetirement
namespace MilneAvAg9bRd12X113FiveRowUpgrade
end MilneAvAg9bRd12X113FiveRowUpgrade
namespace MilneAvAg9bRd12X113LocalDatumMint
end MilneAvAg9bRd12X113LocalDatumMint
namespace MilneAvAg9bRd9DictionaryHeld3Closure
end MilneAvAg9bRd9DictionaryHeld3Closure
namespace ModularCurve
namespace KwNo6Pin
open _root_.ModularCurve.KwNo6Pin
open _root_.ModularCurve
end ModularCurve.KwNo6Pin
namespace ModularCurve
namespace KwNo6Section
open _root_.ModularCurve.KwNo6Section
open _root_.ModularCurve
end ModularCurve.KwNo6Section
namespace ModularCurve
namespace Ldgr35Cs
open _root_.ModularCurve.Ldgr35Cs
open _root_.ModularCurve
end ModularCurve.Ldgr35Cs
namespace ModularCurve
namespace Ldgr36Rc
open _root_.ModularCurve.Ldgr36Rc
open _root_.ModularCurve
end ModularCurve.Ldgr36Rc
namespace ModularCurve
namespace Ldgr36Si
open _root_.ModularCurve.Ldgr36Si
open _root_.ModularCurve
end ModularCurve.Ldgr36Si
namespace ModularCurve
namespace Lg37
open _root_.ModularCurve.Lg37
open _root_.ModularCurve
end ModularCurve.Lg37
namespace ModularCurve
namespace Ldgr37Ch
open _root_.ModularCurve.Ldgr37Ch
open _root_.ModularCurve
end ModularCurve.Ldgr37Ch
namespace ModularCurve
namespace Ldgr39Hf
open _root_.ModularCurve
end ModularCurve.Ldgr39Hf
namespace ModularCurve
namespace Mp72a102T3
open _root_.ModularCurve.Mp72a102T3
open _root_.ModularCurve
end ModularCurve.Mp72a102T3
namespace Module
open _root_.Module
open _root_.Module
end Module
namespace Mp72a101T2
end Mp72a101T2
namespace Mp72a102T1
open _root_.Mp72a102T1
end Mp72a102T1
namespace Mp72a102T2
open _root_.Mp72a102T2
end Mp72a102T2
namespace Mp72a103T2
open _root_.Mp72a103T2
end Mp72a103T2
namespace P1PortPointwise
open _root_.Pointwise
end P1PortPointwise
namespace P1PortPolynomial
open _root_.Polynomial
open _root_.Polynomial
end P1PortPolynomial
namespace P1PortPolynomialBivariate
open _root_.Polynomial
namespace Bivariate
open _root_.Polynomial.Bivariate
open _root_.Polynomial
end P1PortPolynomialBivariate.Bivariate
namespace RationalFunctionField
end RationalFunctionField
namespace TameRamificationConverseThree
end TameRamificationConverseThree
namespace P1PortTensorProduct
open _root_.TensorProduct
open _root_.TensorProduct
end P1PortTensorProduct
namespace The
end The
namespace UniqueFactorizationMonoid
open _root_.UniqueFactorizationMonoid
open _root_.UniqueFactorizationMonoid
end UniqueFactorizationMonoid
namespace WithZero
open _root_.WithZero
open _root_.WithZero
end WithZero
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable {K F}
variable (v : Place K F)
end Place
namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor
variable {K F}
end Divisor
namespace Pic0
open _root_.AlgebraicCurve.Pic0
variable {K F}
end Pic0
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
open scoped _root_.Pointwise
variable {K F}
variable (σ : F ≃ₐ[K] F)
variable (v : Place K F)
end Place
namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor
open scoped _root_.Pointwise
variable {K F}
end Divisor
namespace Pic0
open _root_.AlgebraicCurve.Pic0
open scoped _root_.Pointwise
variable {K F}
end Pic0
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
end Place
end AlgebraicCurve
end
end
end
section
section
open _root_.Polynomial
open _root_.Module
open _root_.Algebra
namespace FLT
namespace EulerDualBasis
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable {F : Type*} [Field F] [CharZero F] {g : F[X]} [Fact (Irreducible g)]
end FLT.EulerDualBasis
namespace FLT
namespace EulerDualBasis
namespace Gates
open _root_.AdjoinRoot
end FLT.EulerDualBasis.Gates
end
end
section
section
noncomputable section
open _root_.KaehlerDifferential
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
namespace IsCurveOver
open _root_.AlgebraicCurve.IsCurveOver
variable {K F}
end IsCurveOver
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable {K F}
variable (v : Place K F)
end Place
variable {K F}
variable (K F)
/-- Uniformizer differentials at each place differ by a coefficient of order zero. -/
def OrdDifferentialWellDefined : Prop :=
  ∀ (v : Place K F) (π π' : F), v.ord π = 1 → v.ord π' = 1 →
    ∃ u : F, v.ord u = 0 ∧
      KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π

end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
end ModularCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}
variable (K F)
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.Polynomial
open _root_.IsDedekindDomain
open scoped _root_.Polynomial.Bivariate
namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end AlgebraicCurve.Place
namespace WeierstrassCurve
open _root_.WeierstrassCurve
namespace Affine
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine.CoordinateRing
open _root_.AlgebraicCurve
variable {F : Type*} [Field F] {W : Affine F}
variable (v : AlgebraicCurve.Place F W.FunctionField)
end WeierstrassCurve.Affine
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace ModularCurve
namespace Lg37
open _root_.ModularCurve.Lg37
open _root_.ModularCurve
open _root_.AlgebraicCurve
open _root_.ModularCurve.Ldgr36Si
open _root_.ModularCurve.Ldgr36Rc
open _root_.ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end CompletionCarrier
section Inhabitant
end Inhabitant
section Stratum
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
end Stratum
section MovedCarrier
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
variable [HasCanonicalLocalResidueKStar K F']
end MovedCarrier
section CommittedPlace
end CommittedPlace
end ModularCurve.Lg37
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section SinglePlace
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end SinglePlace
section Restrict
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']
private theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')
variable [Algebra.IsIntegral F F']
section RestrictDef
variable [Algebra K F] [IsScalarTower K F F']
end RestrictDef
end Restrict
end Place
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.Polynomial
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
open _root_.IntermediateField
namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
open _root_.AlgebraicCurve
section Ultrametric
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.AlgebraicCurve.Place.ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h
  : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]

open _root_.AlgebraicCurve.Place
end Ultrametric
section SumLeFinrank
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
end SumLeFinrank
end AlgebraicCurve.Place
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
section RationalFunctionFieldInfty
end RationalFunctionFieldInfty
section Tower
variable (p : ℕ) [NeZero p]
end Tower
section Degree
variable (p : ℕ) [NeZero p]
end Degree
section Restriction
end Restriction
section Assembly
variable {p : ℕ} [NeZero p]
end Assembly
end ModularCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
open scoped _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
section OfHeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]
end OfHeightOneSpectrum
end Place
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]
theorem inftyValuation_isEquiv_adicValuation :
    (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  (placeInfty K).isEquiv_adicValuation_of_valuationSubring_eq rfl

theorem placeInfty_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end PlaceInfty
variable {K}
theorem eq_ofHeightOneSpectrum_or_eq_placeInfty [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

section ResidueDegree
variable (K)
end ResidueDegree
section DegInfty
variable (K) [DecidableEq (RatFunc K)]
theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩
  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, _root_.map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt_left hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

end DegInfty
end RationalFunctionField
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
omit [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial
  Ω[F⁄K]] in
theorem exists_smul_eq_of_ne_zero (v : Place K F) {ω ω₀ : Ω[F⁄K]}
    (hω : ω ≠ 0) (hω₀ : ω₀ ≠ 0) : ∃ g : F, g ≠ 0 ∧ ω = g • ω₀ := by
  set a := v.differentialCoeff ω with ha
  set b := v.differentialCoeff ω₀ with hb
  have h0 : b ≠ 0 := v.differentialCoeff_ne_zero hω₀
  refine ⟨a * b⁻¹, mul_ne_zero (v.differentialCoeff_ne_zero hω) (inv_ne_zero h0), ?_⟩
  have hω₀eq : ω₀ = b • v.dCoord := hb ▸ (v.differentialCoeff_smul_dCoord ω₀).symm
  rw [hω₀eq, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  exact ha ▸ (v.differentialCoeff_smul_dCoord ω).symm

section TraceDescent
variable (K F)
variable (E : Type*) [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F]
end TraceDescent
section Engine
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [HasPrincipalDivisors K E]
end Engine
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
open _root_.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.WithZero
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section Transport
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end Transport
end Place
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]
variable (K F) in
/-- The principal adele associated to a function. -/
def principalAdele : F →ₗ[K] adeleSpace K F where
  toFun f := ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
  map_add' f g := Subtype.ext ((diagonalHom K F).map_add f g)
  map_smul' c f := Subtype.ext ((diagonalHom K F).map_smul c f)

section P1NamedRows
open scoped _root_.Polynomial
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The monomial generators of the polynomial part of a rational function. -/
def P1PolynomialGenerators : Set (RatFunc K) := Set.range fun n : ℕ => RatFunc.X ^ n

/-- The partial fraction atoms at finite places. -/
def P1PrincipalPartGenerators : Set (RatFunc K) :=
  {f | ∃ (p c : K[X]) (m : ℕ), p.Monic ∧ Irreducible p ∧ c.degree < p.degree ∧ 1 ≤ m ∧
    f = algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m}

/-- The polynomial and finite principal part generators of rational functions. -/
def P1PartialFractionGenerators : Set (RatFunc K) :=
  P1PolynomialGenerators K ∪ P1PrincipalPartGenerators K

variable {K}
end P1NamedRows
section P1Gates
open scoped _root_.Polynomial
theorem gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PolynomialGenerators K) := by
  rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    ← RatFunc.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end P1Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace Mp72a102T1
open _root_.Mp72a102T1
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.ModularCurve.Lg37
open _root_.ModularCurve.Ldgr37Ch
open Mp72a101T2
open scoped _root_.Polynomial
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
section Engine
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Engine
section FinitePlace
variable (K : Type*) [Field K]
end FinitePlace
section RatWs
end RatWs
end Mp72a102T1
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace Mp72a102T2
open _root_.Mp72a102T2
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.ModularCurve.Lg37
open _root_.ModularCurve.Ldgr35Cs
open Mp72a101T2
open scoped _root_.Polynomial
section ResidueCalculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end ResidueCalculus
section Engine
variable {K : Type*} [Field K] {p : K[X]}
end Engine
section Corners
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
end Corners
section RatProduction
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
end RatProduction
section AxiomAudit
end AxiomAudit
end Mp72a102T2
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (w : Place K F')
end Place
namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor
end Divisor
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.IsDedekindDomain
open _root_.WithZero
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
variable [HasCanonicalLocalResidueKStar K F]
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace ModularCurve
open _root_.ModularCurve
namespace MilneAvAg9bRd14CubeRowCartierSliceStart
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
open scoped _root_.Polynomial
end MilneAvAg9bRd14CubeRowCartierSliceStart
end ModularCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
open scoped _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section DegPos
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end DegPos
end Place
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K]
end RationalFunctionField
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section Restrict
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')
end Restrict
end Place
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]
section RatFuncIntegrality
open _root_.AlgebraicCurve.RationalFunctionField
variable (K)
variable [DecidableEq (RatFunc K)]
theorem algebraMap_polynomial_mem_of_ne_placeInfty'
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ v.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd rfl hv

theorem pow_X_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n ∈ v.toValuationSubring := by
  have h : algebraMap K[X] (RatFunc K) (Polynomial.X ^ n) ∈ v.toValuationSubring :=
    algebraMap_polynomial_mem_of_ne_placeInfty' K hv (Polynomial.X ^ n)
  rwa [map_pow, RatFunc.algebraMap_X] at h

theorem pow_X_mul_mem_of_ne_placeInfty
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (n : ℕ)
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    (RatFunc.X : RatFunc K) ^ n * g ∈ v.toValuationSubring :=
  mul_mem (pow_X_mem_of_ne_placeInfty K hv n) hg

end RatFuncIntegrality
section P1PolynomialSubrows
open _root_.AlgebraicCurve.RationalFunctionField
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The differential coefficient is regular at every finite place. -/
def P1DifferentialCoeffRegularFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K →
    v.differentialCoeff ω₀ ∈ v.toValuationSubring

variable {K}
end P1PolynomialSubrows
section P1PrincipalPartSubrows
open _root_.AlgebraicCurve.RationalFunctionField
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- A rational function atom with a prescribed polynomial denominator power. -/
abbrev p1PrincipalPartAtom (p c : K[X]) (m : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m

variable {K}
omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in
theorem finitePlace_ne_placeInfty {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp ≠ placeInfty K :=
  fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

end P1PrincipalPartSubrows
section P1Composed
open _root_.AlgebraicCurve.RationalFunctionField
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end P1Composed
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.Polynomial
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section SubsingletonCriterion
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
end SubsingletonCriterion
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end Place
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]
theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (placeInfty K).ord f = 0 := by
  rw [(placeInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl

theorem ord_placeInfty_eq_intDegree_mul {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = f.intDegree * (placeInfty K).ord (RatFunc.X) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hpoly : ∀ q : K[X], q ≠ 0 →
      (placeInfty K).ord (algebraMap K[X] (RatFunc K) q)
        = (q.natDegree : ℤ) * (placeInfty K).ord (RatFunc.X) := by
    intro q hq
    have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
    have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
    have hXpow : (RatFunc.X : RatFunc K) ^ q.natDegree ≠ 0 := pow_ne_zero _ hX
    have hXpoly : (RatFunc.X : RatFunc K) ^ q.natDegree
        = algebraMap K[X] (RatFunc K) (Polynomial.X ^ q.natDegree) := by
      rw [map_pow, RatFunc.algebraMap_X]
    have hdeg : (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree).intDegree = 0 := by
      rw [RatFunc.intDegree_div hq' hXpow, RatFunc.intDegree_polynomial, hXpoly,
        RatFunc.intDegree_polynomial, natDegree_X_pow, sub_self]
    have hne : algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree ≠ 0 :=
      div_ne_zero hq' hXpow
    have h0 := ord_placeInfty_eq_zero_of_intDegree_eq_zero K hne hdeg
    have hsplit : algebraMap K[X] (RatFunc K) q
        = (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree)
          * RatFunc.X ^ q.natDegree :=
      (div_mul_cancel₀ _ hXpow).symm
    rw [hsplit, (placeInfty K).ord_mul hne hXpow, h0, zero_add, ← zpow_natCast,
      (placeInfty K).ord_zpow]
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (placeInfty K).ord_mul hnum' (inv_ne_zero hden'), (placeInfty K).ord_inv,
    hpoly _ (RatFunc.num_ne_zero hf), hpoly _ f.denom_ne_zero, ← div_eq_mul_inv,
    RatFunc.intDegree_div hnum' hden', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring

theorem ord_placeInfty_X : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hneg : (placeInfty K).ord (RatFunc.X : RatFunc K) < 0 := by
    by_contra h
    have hmem : (RatFunc.X : RatFunc K) ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hX (not_lt.mp h)
    rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
      RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hX,
      RatFunc.intDegree_X, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hmem
    omega
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (placeInfty K).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (placeInfty K).ord (RatFunc.X : RatFunc K) ∣ 1 := by
    rw [← (placeInfty K).ord_coe_irreducible hπ, ord_placeInfty_eq_intDegree_mul K hπ0]
    exact Dvd.intro_left _ rfl
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega

theorem ord_placeInfty_algebraMap' {q : K[X]} (hq : q ≠ 0) :
    (placeInfty K).ord (algebraMap K[X] (RatFunc K) q) = -(q.natDegree : ℤ) := by
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hq
  rw [ord_placeInfty_eq_intDegree_mul K hq', ord_placeInfty_X, RatFunc.intDegree_polynomial]
  ring

end PlaceInfty
section Principal
variable {K}
end Principal
end RationalFunctionField
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section Congr
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')
variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he
end Congr
end Place
namespace Pic0
open _root_.AlgebraicCurve.Pic0
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include e he
end Pic0
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
open _root_.IntermediateField
end ModularCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section IntegrallyClosed
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
end IntegrallyClosed
section SupportTransfer
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']
variable (w : Place K F')
end SupportTransfer
section Chart
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)
end Chart
section FiberFiniteness
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
end FiberFiniteness
end Place
section Assembly
variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']
end Assembly
end AlgebraicCurve
end
end
end
section
section
open _root_.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section CotangentEngine
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end CotangentEngine
end Place
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
end
end
section
section
noncomputable section
open _root_.Polynomial
open _root_.UniqueFactorizationMonoid
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
variable {K : Type*} [Field K]
theorem exists_monic_irreducible_factorization {d : K[X]} (hd : d.Monic) :
    ∃ (s : Finset K[X]) (n : K[X] → ℕ),
      (∀ p ∈ s, p.Monic) ∧ (∀ p ∈ s, Irreducible p) ∧
      (Set.Pairwise (s : Set K[X]) fun i j => IsCoprime i j) ∧
      d = ∏ p ∈ s, p ^ n p := by
  classical
  refine ⟨(normalizedFactors d).toFinset,
    fun p => (normalizedFactors d).count p, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ((Polynomial.mem_normalizedFactors_iff hd.ne_zero).mp
      (Multiset.mem_toFinset.mp hp)).2.1
  · intro p hp
    exact irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp)
  · intro p hp q hq hne
    have hp' := Multiset.mem_toFinset.mp hp
    have hq' := Multiset.mem_toFinset.mp hq
    rw [(irreducible_of_normalized_factor p hp').coprime_iff_not_dvd]
    exact fun hdvd => hne (normalizedFactors_eq_of_dvd d p hp' q hq' hdvd)
  · calc d = (normalizedFactors d).prod := by
            rw [prod_normalizedFactors_eq hd.ne_zero, hd.normalize_eq_self]
      _ = ∏ p ∈ (normalizedFactors d).toFinset, p ^ (normalizedFactors d).count p :=
            Finset.prod_multiset_count _

theorem algebraMap_mem_span_P1PartialFractionGenerators (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Submodule.span K (P1PartialFractionGenerators K) :=
  Submodule.span_mono Set.subset_union_left
    (gate_algebraMap_polynomial_mem_span_P1PolynomialGenerators q)

theorem div_pow_mem_span_P1PartialFractionGenerators
    {p c : K[X]} (hpmon : p.Monic) (hpirr : Irreducible p)
    (hdeg : c.degree < p.degree) {m : ℕ} (hm : 1 ≤ m) :
    algebraMap K[X] (RatFunc K) c / (algebraMap K[X] (RatFunc K) p) ^ m
      ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  exact Submodule.subset_span (Or.inr ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩)

theorem ratFunc_mem_span_P1PartialFractionGenerators (f : RatFunc K) :
    f ∈ Submodule.span K (P1PartialFractionGenerators K) := by
  classical
  have hdenmon : f.denom.Monic := RatFunc.monic_denom f
  obtain ⟨s, n, hmon, hirr, hcop, hdfac⟩ :=
    exists_monic_irreducible_factorization hdenmon
  have hginv : ∀ p ∈ s,
      (algebraMap K[X] (RatFunc K) p)⁻¹ * algebraMap K[X] (RatFunc K) p = 1 :=
    fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hmon p hp).ne_zero)
  obtain ⟨q, r, hr, hpfrac⟩ :=
    Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) f.num hmon hcop n hginv
  have hLHS : algebraMap K[X] (RatFunc K) f.num *
      ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p = f := by
    have hprod : ∏ p ∈ s, ((algebraMap K[X] (RatFunc K) p)⁻¹) ^ n p
        = (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
      rw [hdfac, map_prod]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => by rw [map_pow, inv_pow]
    rw [hprod, ← div_eq_mul_inv, RatFunc.num_div_denom]
  rw [← hLHS, hpfrac]
  refine Submodule.add_mem _ (algebraMap_mem_span_P1PartialFractionGenerators q) ?_
  refine Submodule.sum_mem _ fun p hp => ?_
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [inv_pow, ← div_eq_mul_inv]
  exact div_pow_mem_span_P1PartialFractionGenerators (hmon p hp) (hirr p hp)
    (hr p hp j) j.succ_pos

theorem p1PartialFractionSpan_eq_top :
    Submodule.span K (P1PartialFractionGenerators K) = ⊤ :=
  Submodule.eq_top_iff'.mpr ratFunc_mem_span_P1PartialFractionGenerators

end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
open _root_.AlgebraicCurve
open _root_.ModularCurve.Lg37
open _root_.Polynomial
open _root_.IntermediateField
open _root_.Mp72a102T1
open _root_.Mp72a102T2
namespace ModularCurve
namespace KwNo6Section
open _root_.ModularCurve.KwNo6Section
open _root_.ModularCurve
section GenericIso
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end GenericIso
section GenericSection
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end GenericSection
section Modular
end Modular
end ModularCurve.KwNo6Section
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsLocalRing
open _root_.Polynomial
open scoped _root_.Polynomial
namespace ModularCurve
namespace Mp72a102T3
open _root_.ModularCurve.Mp72a102T3
open _root_.ModularCurve
open _root_.AlgebraicCurve
open _root_.ModularCurve.Lg37
section General
variable {R : Type*} [CommRing R] (I : Ideal R)
end General
section Carrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Carrier
section RatProduction
open _root_.AlgebraicCurve.RationalFunctionField
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]
end RatProduction
end ModularCurve.Mp72a102T3
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section OrdIntegrand
variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end OrdIntegrand
section MOneMembership
variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end MOneMembership
section MOneTerm
variable [CharZero K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end MOneTerm
section MOneInftyVanish
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
end MOneInftyVanish
section FiniteSideRow
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
end FiniteSideRow
section FiniteSideBridge
variable [CharZero K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end FiniteSideBridge
section TwoPlaceCancelFromFinite
variable [CharZero K]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end TwoPlaceCancelFromFinite
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
open scoped _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
theorem ord_eq_neg_log_of_valuationSubring_eq (w : Valuation F ℤᵐ⁰)
    (hw : w.valuationSubring = v.toValuationSubring) {π : F} (hπ : w π = exp (-1 : ℤ))
    {f : F} (hf : f ≠ 0) : v.ord f = -log (w f) := by
  have hequiv : w.IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hw
  have hexp_lt : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl]
    exact exp_lt_exp.mpr (by omega)
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hadic_π₀ : v.adicValuation (π₀ : F) = exp (-1 : ℤ) := v.adicValuation_coe_irreducible hπ₀
  have hwπ₀ : w (π₀ : F) = exp (-1 : ℤ) := by
    refine le_antisymm (le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mpr ?_)) ?_
    · rw [hadic_π₀]
      exact hexp_lt
    · rw [← hπ]
      refine (hequiv π π₀).mpr ?_
      rw [hadic_π₀]
      refine le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mp ?_)
      rw [hπ]
      exact hexp_lt
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  have hwu : w ((u : v.toValuationSubring) : F) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr ((v.adicValuation_coe_eq_one_iff _).mpr u.isUnit)
  set n := v.ord f with hn
  rw [hu, map_mul, map_zpow₀, hwu, hwπ₀, one_mul, log_zpow, log_exp, smul_eq_mul]
  ring

end Place
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K]
theorem ord_ofHeightOneSpectrum_eq_neg_log (w : HeightOneSpectrum K[X]) {p : K[X]}
    (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f
      = -log (w.valuation (RatFunc K) f) := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  exact (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval hf

theorem ord_ofHeightOneSpectrum_of_span (w : HeightOneSpectrum K[X]) {p : K[X]}
    (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [ord_ofHeightOneSpectrum_eq_neg_log w hp hw (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]

section PlaceInftyOrd
variable [DecidableEq (RatFunc K)]
theorem ord_placeInfty {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = -f.intDegree := by
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [(placeInfty K).ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K) rfl hπ
      hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

end PlaceInftyOrd
section IrreducibleDivisor
variable [DecidableEq (RatFunc K)]
end IrreducibleDivisor
end RationalFunctionField
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
omit [DecidableEq (RatFunc K)] in
theorem D_ratFuncX_eq_neg_X_sq_smul_D_inv :
    KaehlerDifferential.D K (RatFunc K) RatFunc.X
      = (-(RatFunc.X : RatFunc K) ^ 2) •
          KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ :=
  (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
    (mul_inv_cancel₀ RatFunc.X_ne_zero)

theorem ord_placeInfty_X_inv : (placeInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(placeInfty K).ord_inv, ord_placeInfty_X, neg_neg]

theorem ord_placeInfty_X_pow (n : ℕ) :
    (placeInfty K).ord ((RatFunc.X : RatFunc K) ^ n) = -(n : ℤ) := by
  rw [show ((RatFunc.X : RatFunc K) ^ n) = (RatFunc.X : RatFunc K) ^ (n : ℤ) from
    (zpow_natCast _ n).symm, (placeInfty K).ord_zpow, ord_placeInfty_X]
  ring

section NonVanishing
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
omit [DecidableEq (RatFunc K)] in
theorem D_ratFuncX_inv_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := by
  classical
  obtain ⟨u, -, hueq⟩ :=
    hwd (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (placeInfty K).uniformizer
      (ord_placeInfty_X_inv K) (placeInfty K).ord_uniformizer
  intro h0
  refine (placeInfty K).dCoord_ne_zero ?_
  change KaehlerDifferential.D K (RatFunc K) (placeInfty K).uniformizer = 0
  rw [hueq, h0, smul_zero]

end NonVanishing
section DifferentialCoeff
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
theorem differentialCoeff_placeInfty_D_X_eq :
    (placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = (-(RatFunc.X : RatFunc K) ^ 2) *
          (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv, (placeInfty K).differentialCoeff_smul]

theorem ord_differentialCoeff_placeInfty_D_X_inv_eq_zero
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ord
        ((placeInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)) = 0 := by
  obtain ⟨u, hu0, hueq⟩ :=
    hwd (placeInfty K) (placeInfty K).uniformizer (RatFunc.X : RatFunc K)⁻¹
      (placeInfty K).ord_uniformizer (ord_placeInfty_X_inv K)
  rw [(placeInfty K).differentialCoeff_unique
    (show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹
        = u • (placeInfty K).dCoord from hueq), hu0]

end DifferentialCoeff
section OrdDifferential
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
theorem ordDifferential_placeInfty_D_ratFuncX
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ordDifferential
        (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)) = -2 := by
  rw [Place.ordDifferential, differentialCoeff_placeInfty_D_X_eq K, neg_mul,
    (placeInfty K).ord_neg,
    (placeInfty K).ord_mul (pow_ne_zero 2 RatFunc.X_ne_zero)
      ((placeInfty K).differentialCoeff_ne_zero (D_ratFuncX_inv_ne_zero K hwd)),
    ord_placeInfty_X_pow K 2, ord_differentialCoeff_placeInfty_D_X_inv_eq_zero K hwd]
  norm_num

end OrdDifferential
section Factorisation
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Factorisation
section NamedSubrow
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
end NamedSubrow
section Bridge
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Bridge
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section Uniqueness
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
end Uniqueness
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
attribute [local instance 0] valuationSubringAlgebra
section Setup
variable (v : Place K F)
end Setup
section Center
variable {v : Place K F} {w : Place K F'}
end Center
section ValuationDictionary
variable {v : Place K F} {w : Place K F'}
end ValuationDictionary
section ResidueDictionary
variable {v : Place K F} {w : Place K F'}
end ResidueDictionary
section Bijection
variable {v : Place K F}
end Bijection
section Assembly
variable (v : Place K F)
end Assembly
end Place
end AlgebraicCurve
end
end
end
section
section
open _root_.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Polynomial
open _root_.IsLocalRing
open scoped _root_.TensorProduct
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section ResidueEngine
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end ResidueEngine
end Place
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace ModularCurve
open _root_.ModularCurve
namespace MilneAvAg9bRd15UnitNormalFormLaurentSeed
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
open scoped _root_.Polynomial
end MilneAvAg9bRd15UnitNormalFormLaurentSeed
end ModularCurve
end
end
end
section
section
open _root_.Polynomial
open _root_.IsLocalRing
open _root_.AlgebraicCurve
open _root_.ModularCurve.Lg37
open _root_.ModularCurve.Mp72a102T3
open _root_.Mp72a103T2
open _root_.Mp72a102T1
open _root_.ModularCurve.KwNo6Section
namespace ModularCurve
namespace KwNo6Pin
open _root_.ModularCurve.KwNo6Pin
open _root_.ModularCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end ModularCurve.KwNo6Pin
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.IsLocalRing
open _root_.Polynomial
open scoped _root_.Polynomial
namespace Mp72a103T2
open _root_.Mp72a103T2
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.ModularCurve.Lg37
open _root_.ModularCurve.Mp72a102T3
open _root_.Mp72a102T2
section Calculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Calculus
section NumeratorBand
variable {K : Type*} [Field K] [CharZero K]
end NumeratorBand
section RatProduction
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]
end RatProduction
end Mp72a103T2
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K]
/-- The differential of the rational function field coordinate. -/
abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  · exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

variable {K}
theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_
  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by simp [h])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

section NumDenom
variable {w : HeightOneSpectrum K[X]}
local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w
private theorem uniformizer_ne_zero' : (v).uniformizer ≠ 0 :=
  (v).uniformizer_ne_zero

theorem ord_algebraMap_denom_uniformizer_eq_zero {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.denom) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  by_contra hne
  have hpd : p ∣ π.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ π.num := fun hpn =>
    hp.not_isUnit (π.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) π.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hπne)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) π.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)) (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hordπ
  omega

theorem ord_algebraMap_num_uniformizer_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.num) = 1 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_uniformizer_eq_zero hp hwp] at hordπ
  omega

theorem not_dvd_num'denom_sub_numdenom' {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ¬ p ∣ ((v).uniformizer.num.derivative * (v).uniformizer.denom
            - (v).uniformizer.num * (v).uniformizer.denom.derivative) := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  have hpn' : ¬ p ∣ π.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hπne)
      (ord_algebraMap_num_uniformizer_eq_one hp hwp)
  have hpd : ¬ p ∣ π.denom := fun hpd => by
    have := ord_algebraMap_denom_uniformizer_eq_zero (w := w) hp hwp
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mpr hpd this
  have hpn : p ∣ π.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hπne)).mp ?_
    rw [ord_algebraMap_num_uniformizer_eq_one hp hwp]; exact one_ne_zero
  intro hdvd
  have hpnd' : p ∣ π.num * π.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ π.num.derivative * π.denom := by
    have := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at this
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

end NumDenom
section PerPlace
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {w : HeightOneSpectrum K[X]}
local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w
theorem ord_differentialCoeff_dX_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).ord ((v).differentialCoeff (dX K)) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'
  set ξ : K[X] := π.num.derivative * π.denom - π.num * π.denom.derivative with hξ
  have hd0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hcoord : (v).dCoord
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2) • dX K := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K π, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
    rfl
  have hξ0 : ξ ≠ 0 := by
    intro h; rw [hξ] at h
    exact not_dvd_num'denom_sub_numdenom' hp hwp hsep (h ▸ dvd_zero p)
  have hcoeff0 : algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2 ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (pow_ne_zero 2 hd0)
  have hcoeff : (v).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2)⁻¹ := by
    refine (v).differentialCoeff_unique ?_
    rw [hcoord, smul_smul, inv_mul_cancel₀ hcoeff0, one_smul]
  have hordξ : (v).ord (algebraMap K[X] (RatFunc K) ξ) = 0 := by
    by_contra h
    refine not_dvd_num'denom_sub_numdenom' hp hwp hsep ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  rw [hcoeff, (v).ord_inv, div_eq_mul_inv,
    (v).ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (inv_ne_zero (pow_ne_zero 2 hd0)),
    hordξ, (v).ord_inv, ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_uniformizer_eq_zero hp hwp]
  ring

end PerPlace
section Discharge
variable (K)
variable [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end Discharge
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
omit [DecidableEq (RatFunc K)] in
theorem ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne
    (w : HeightOneSpectrum K[X]) {p : K[X]} (hp : Irreducible p)
    (hne : w ≠ heightOneSpectrumOfIrreducible K hp) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 0 := by
  by_contra hord
  refine hne (HeightOneSpectrum.ext ?_)
  have hmem : p ∈ w.asIdeal :=
    (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp.ne_zero).mp hord
  exact ((PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le
    (w.isPrime.isMaximal w.ne_bot).ne_top
    ((Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hmem)).symm

theorem ord_algebraMap_irreducible_eq_zero_of_ne
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ placeInfty K) :
    v.ord (algebraMap K[X] (RatFunc K) p) = 0 := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · refine ord_ofHeightOneSpectrum_irreducible_eq_zero_of_ne K w hp ?_
    rintro rfl; exact hvp rfl
  · exact absurd rfl hvinf

theorem inv_algebraMap_pow_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ placeInfty K) (m : ℕ) :
    ((algebraMap K[X] (RatFunc K) p) ^ m)⁻¹ ∈ v.toValuationSubring := by
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
  refine v.mem_of_ord_nonneg (inv_ne_zero (pow_ne_zero m hp0)) ?_
  rw [v.ord_inv, ← zpow_natCast, v.ord_zpow,
    ord_algebraMap_irreducible_eq_zero_of_ne K hp hvp hvinf, mul_zero, _root_.neg_zero]

theorem p1PrincipalPartAtom_mem_of_ne_finitePlace
    {p : K[X]} (hp : Irreducible p) (c : K[X]) (m : ℕ) {v : Place K (RatFunc K)}
    (hvp : v ≠ finitePlace K hp) (hvinf : v ≠ placeInfty K) :
    p1PrincipalPartAtom K p c m ∈ v.toValuationSubring := by
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv]
  exact mul_mem (algebraMap_polynomial_mem_of_ne_placeInfty' K hvinf c)
    (inv_algebraMap_pow_mem_of_ne_finitePlace K hp hvp hvinf m)

section Reduction
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end Reduction
theorem ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : p ≠ 0) {c : K[X]} (hc : c ≠ 0) (m : ℕ) :
    (placeInfty K).ord (p1PrincipalPartAtom K p c m)
      = (m : ℤ) * p.natDegree - c.natDegree := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp
  have hc' : algebraMap K[X] (RatFunc K) c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc
  unfold p1PrincipalPartAtom
  rw [div_eq_mul_inv, (placeInfty K).ord_mul hc' (inv_ne_zero (pow_ne_zero m hp')),
    (placeInfty K).ord_inv, ← zpow_natCast, (placeInfty K).ord_zpow,
    RatFuncResidue.AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap' K hc,
    RatFuncResidue.AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap' K hp]
  ring

section CanonicalDivisor
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end CanonicalDivisor
section NamedSubrows
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end NamedSubrows
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.KaehlerDifferential
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K]
end RationalFunctionField
variable (K F)
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section Identity
variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
variable {K F F'}
end Identity
namespace Divisor
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve.Divisor
section Pullback
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
end Pullback
section Galois
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
variable [FiniteDimensional F F']
end Galois
section Descent
variable {K F' F'' : Type*} [Field K] [Field F'] [Field F'']
  [Algebra K F'] [Algebra K F''] [Algebra F' F''] [IsScalarTower K F' F'']
  [Algebra.IsIntegral F' F''] [FiniteDimensional F' F'']
end Descent
end Divisor
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']
section GaloisClosure
variable (F'' : Type*) [Field F''] [Algebra K F''] [Algebra (RatFunc K) F'']
  [Algebra F' F''] [IsScalarTower K (RatFunc K) F''] [IsScalarTower K F' F'']
  [FiniteDimensional (RatFunc K) F''] [Algebra.IsSeparable (RatFunc K) F'']
  [IsGalois (RatFunc K) F''] [FiniteDimensional F' F'']
end GaloisClosure
end RationalFunctionField
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
section SurjectivePlaceInfty
variable (K) [DecidableEq (RatFunc K)]
end SurjectivePlaceInfty
section NamedRow
variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
end NamedRow
section SATGate
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
end SATGate
section XInvCoordinate
variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end XInvCoordinate
section Bridge
variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Bridge
section IntegralRecursion
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
end IntegralRecursion
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
open _root_.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Polynomial
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section EftEngine
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end EftEngine
end Place
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
end
end
section
section
open _root_.Polynomial
open _root_.IsLocalRing
open _root_.AlgebraicCurve
open _root_.ModularCurve.Lg37
open _root_.ModularCurve.Mp72a102T3
open _root_.Mp72a103T2
open _root_.Mp72a102T1
open _root_.ModularCurve.KwNo6Section
namespace ModularCurve
namespace KwNo6Pin
open _root_.ModularCurve.KwNo6Pin
open _root_.ModularCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
section WitnessW
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))
include hℓ
end WitnessW
end ModularCurve.KwNo6Pin
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
section WronskianBound
variable {K : Type*} [Field K]
theorem natDegree_numDenomWronskian_lt {n d : K[X]} (hn : n ≠ 0) (hd : d ≠ 0)
    (hW : n.derivative * d - n * d.derivative ≠ 0) :
    (n.derivative * d - n * d.derivative).natDegree < n.natDegree + d.natDegree := by
  have hdeg : (n.derivative * d - n * d.derivative).degree < (n * d).degree := by
    rw [Polynomial.degree_mul]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_right (Polynomial.degree_ne_bot.mpr hd)]
      exact Polynomial.degree_derivative_lt hn
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_left (Polynomial.degree_ne_bot.mpr hn)]
      exact Polynomial.degree_derivative_lt hd
  have h2 := Polynomial.natDegree_lt_natDegree hW hdeg
  rwa [Polynomial.natDegree_mul hn hd] at h2

end WronskianBound
section DXCoeff
variable (K : Type*) [Field K]
/-- The rational function derivative given by the quotient rule. -/
def ratFuncDXCoeff (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
    / (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem ratFuncDXCoeff_def (f : RatFunc K) :
    ratFuncDXCoeff K f
      = algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / (algebraMap K[X] (RatFunc K) f.denom) ^ 2 := rfl

theorem D_eq_ratFuncDXCoeff_smul_dX (f : RatFunc K) :
    KaehlerDifferential.D K (RatFunc K) f = ratFuncDXCoeff K f • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [ratFuncDXCoeff_def, div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K f,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd), one_smul]

theorem wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero {f : RatFunc K}
    (h : ratFuncDXCoeff K f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h0
  exact h (by rw [ratFuncDXCoeff_def, h0, _root_.map_zero, zero_div])

end DXCoeff
section FinitePlaces
variable {K : Type*} [Field K]
variable {w : HeightOneSpectrum K[X]}
local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w
theorem ord_algebraMap_denom_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne
  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hord
  omega

theorem ord_algebraMap_num_eq_one_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.num) = 1 := by
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := hord
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord] at h
  omega

theorem not_dvd_wronskian_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) := by
  have hpn' : ¬ p ∣ f.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hf)
      (ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord)
  have hpd : ¬ p ∣ f.denom := fun hpd => by
    have h0 := ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mpr hpd h0
  have hpn : p ∣ f.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hf)).mp ?_
    rw [ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord]
    exact one_ne_zero
  intro hdvd
  have hpnd' : p ∣ f.num * f.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ f.num.derivative * f.denom := by
    have h1 := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at h1
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

theorem ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (v).ord (ratFuncDXCoeff K f) = 0 := by
  have hW : ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) :=
    not_dvd_wronskian_of_ord_eq_one hp hwp hsep hf hord
  have hξ0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := fun h =>
    hW (h ▸ dvd_zero p)
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hξ0' : algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hξ0
  have hordξ : (v).ord (algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)) = 0 := by
    by_contra h
    refine hW ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  refine ⟨div_ne_zero hξ0' (pow_ne_zero 2 hd0), ?_⟩
  rw [ratFuncDXCoeff_def, div_eq_mul_inv,
    (v).ord_mul hξ0' (inv_ne_zero (pow_ne_zero 2 hd0)), (v).ord_inv, hordξ,
    ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord]
  ring

end FinitePlaces
section PlaceInftySide
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
theorem ord_placeInfty_ratFuncDXCoeff_ge {g : RatFunc K} (hg : g ≠ 0)
    (hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0) :
    (placeInfty K).ord g + 1 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  have hn0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hd0 : g.denom ≠ 0 := g.denom_ne_zero
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0
  have hdeg : (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree
      < g.num.natDegree + g.denom.natDegree :=
    natDegree_numDenomWronskian_lt hn0 hd0 hW
  have hcoeff : (placeInfty K).ord (ratFuncDXCoeff K g)
      = 2 * (g.denom.natDegree : ℤ)
        - (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree := by
    rw [ratFuncDXCoeff_def, ord_placeInfty (div_ne_zero hW' (pow_ne_zero 2 hd')),
      RatFunc.intDegree_div hW' (pow_ne_zero 2 hd'), RatFunc.intDegree_polynomial,
      ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
    push_cast
    ring
  have hgord : (placeInfty K).ord g = (g.denom.natDegree : ℤ) - g.num.natDegree := by
    rw [ord_placeInfty hg, RatFunc.intDegree]
    ring
  rw [hcoeff, hgord]
  omega

theorem exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero {g : RatFunc K}
    (hg : g ≠ 0) (hord : (placeInfty K).ord g = 0) :
    ∃ e : RatFunc K, (e = 0 ∨ 2 ≤ (placeInfty K).ord e) ∧
      KaehlerDifferential.D K (RatFunc K) g = e • dX K := by
  have hmem : RatFunc.inftyValuation K g ≤ 1 := by
    have h1 : g ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hg hord.symm.le
    rwa [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at h1
  obtain ⟨c, hc⟩ :=
    RatFuncResidue.AlgebraicCurve.RationalFunctionField.exists_sub_algebraMap_intDegree_neg K hmem
  have hDg : KaehlerDifferential.D K (RatFunc K) g
      = KaehlerDifferential.D K (RatFunc K) (g - algebraMap K (RatFunc K) c) := by
    rw [map_sub, Derivation.map_algebraMap (KaehlerDifferential.D K (RatFunc K)) c, sub_zero]
  rcases hc with hc0 | hcneg
  · exact ⟨0, Or.inl rfl, by rw [hDg, hc0, _root_.map_zero, zero_smul]⟩
  · have hg₁0 : g - algebraMap K (RatFunc K) c ≠ 0 := by
      intro h0
      rw [h0] at hcneg
      simp at hcneg
    refine ⟨ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c), ?_,
      by rw [hDg, D_eq_ratFuncDXCoeff_smul_dX]⟩
    rcases eq_or_ne (ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c)) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hW := wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K h0
      have hge := ord_placeInfty_ratFuncDXCoeff_ge hg₁0 hW
      have hord₁ : 1 ≤ (placeInfty K).ord (g - algebraMap K (RatFunc K) c) := by
        rw [ord_placeInfty hg₁0]
        omega
      omega

theorem exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one {h : RatFunc K}
    (hh : h ≠ 0) (hord : (placeInfty K).ord h = -1) :
    ∃ b : RatFunc K, b ≠ 0 ∧ (placeInfty K).ord b = 0 ∧
      KaehlerDifferential.D K (RatFunc K) h = b • dX K := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXinv : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX
  have hg0 : h * (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := mul_ne_zero hh hXinv
  have hordg : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹) = 0 := by
    rw [(placeInfty K).ord_mul hh hXinv, (placeInfty K).ord_inv, ord_placeInfty_X, hord]
    ring
  obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg0 hordg
  have hh_eq : h = h * (RatFunc.X : RatFunc K)⁻¹ * RatFunc.X := by
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  have hDh : KaehlerDifferential.D K (RatFunc K) h
      = (h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e) • dX K := by
    conv_lhs => rw [hh_eq]
    rw [Derivation.leibniz, hDe, smul_smul,
      show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) = dX K from rfl,
      ← add_smul]
  rcases he with rfl | he2
  · refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * 0, ?_, ?_, hDh⟩
    · rw [mul_zero, add_zero]
      exact hg0
    · rw [mul_zero, add_zero]
      exact hordg
  · have he0 : e ≠ 0 := by
      intro h0
      rw [h0, (placeInfty K).ord_zero] at he2
      omega
    have hXe0 : (RatFunc.X : RatFunc K) * e ≠ 0 := mul_ne_zero hX he0
    have hlt : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹)
        < (placeInfty K).ord ((RatFunc.X : RatFunc K) * e) := by
      rw [hordg, (placeInfty K).ord_mul hX he0, ord_placeInfty_X]
      omega
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e, ?_, ?_, hDh⟩
    · intro hsum
      have hXe_eq : (RatFunc.X : RatFunc K) * e = -(h * (RatFunc.X : RatFunc K)⁻¹) := by
        linear_combination hsum
      rw [hXe_eq, (placeInfty K).ord_neg] at hlt
      exact lt_irrefl _ hlt
    · rw [(placeInfty K).ord_add_eq_left hg0 hXe0 hlt]
      exact hordg

theorem exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one {f : RatFunc K}
    (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ∃ e : RatFunc K, e ≠ 0 ∧ (placeInfty K).ord e = 2 ∧
      KaehlerDifferential.D K (RatFunc K) f = e • dX K := by
  have hf' : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hord' : (placeInfty K).ord f⁻¹ = -1 := by
    rw [(placeInfty K).ord_inv, hord]
  obtain ⟨b, hb0, hbord, hDb⟩ := exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one hf' hord'
  refine ⟨-(f ^ 2 * b), neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hf) hb0), ?_, ?_⟩
  · rw [(placeInfty K).ord_neg, (placeInfty K).ord_mul (pow_ne_zero 2 hf) hb0, hbord,
      add_zero, ← zpow_natCast, (placeInfty K).ord_zpow, hord]
    norm_num
  · conv_lhs => rw [← inv_inv f]
    rw [(KaehlerDifferential.D K (RatFunc K)).leibniz_inv f⁻¹, hDb, inv_inv, smul_smul,
      neg_mul]

end PlaceInftySide
section Glue
variable {K : Type*} [Field K]
theorem exists_ord_zero_smul_of_smul_dX_eq {v : Place K (RatFunc K)} {π π' c c' : RatFunc K}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hord : v.ord c' = v.ord c)
    (hD : KaehlerDifferential.D K (RatFunc K) π = c • dX K)
    (hD' : KaehlerDifferential.D K (RatFunc K) π' = c' • dX K) :
    ∃ u : RatFunc K, v.ord u = 0 ∧
      KaehlerDifferential.D K (RatFunc K) π' = u • KaehlerDifferential.D K (RatFunc K) π := by
  refine ⟨c' / c, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hc' (inv_ne_zero hc), v.ord_inv, hord]
    ring
  · rw [hD, hD', smul_smul, div_mul_cancel₀ _ hc]

end Glue
section ConsumerGates
variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ConsumerGates
section NonVacuity
variable (K : Type*) [Field K]
end NonVacuity
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
theorem two_le_ord_placeInfty_p1PrincipalPartAtom
    {p : K[X]} (hp : Irreducible p) {c : K[X]} (hc : c ≠ 0) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) := by
  rw [ord_placeInfty_p1PrincipalPartAtom K hp.ne_zero hc]
  have hndeg : c.natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hc hdeg
  have hpdeg : 1 ≤ (p.natDegree : ℤ) := by exact_mod_cast hp.natDegree_pos
  have hm' : 2 ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

section InftyVanish
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end InftyVanish
section NamedSubrow
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end NamedSubrow
section MOneReduction
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end MOneReduction
section ComposedEngine
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end ComposedEngine
section UnitFinite
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
/-- The differential coefficient has order zero at every finite place of the rational field. -/
def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0

variable {K}
omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [Nontrivial Ω[(RatFunc K)⁄K]] [HasPrincipalDivisors K (RatFunc K)] in
theorem p1DifferentialCoeffRegularFinite_of_unitFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hunit : P1DifferentialCoeffUnitFinite K hω₀) :
    P1DifferentialCoeffRegularFinite K hω₀ :=
  fun v hv => v.mem_of_ord_nonneg (v.differentialCoeff_ne_zero hω₀) (hunit v hv).ge

end UnitFinite
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IntermediateField
open _root_.AlgebraicCurve
open _root_.Polynomial
open _root_.TensorProduct
open _root_.Module
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable (K : Type*) [Field K]
variable {F : Type*} [Field F] [Algebra K F]
variable {K}
variable (K F)
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
end ModularCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
attribute [local instance 0] valuationSubringAlgebra
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
end Place
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']
section GaloisClosure
variable (F'' : Type*) [Field F''] [Algebra K F''] [Algebra (RatFunc K) F'']
  [Algebra F' F''] [IsScalarTower K (RatFunc K) F''] [IsScalarTower K F' F'']
  [FiniteDimensional (RatFunc K) F''] [Algebra.IsSeparable (RatFunc K) F'']
  [IsGalois (RatFunc K) F''] [FiniteDimensional F' F'']
end GaloisClosure
end RationalFunctionField
end AlgebraicCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
section SurjectiveDegOne
end SurjectiveDegOne
section PCoordinateIdentity
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end PCoordinateIdentity
section NamedHigherDeg
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end NamedHigherDeg
section DegOneDischarge
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end DegOneDischarge
section ComposedEngine
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
section AlgClosed
variable [IsAlgClosed K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end AlgClosed
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
open _root_.CongruenceSubgroup
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Polynomial
open _root_.IsLocalRing
namespace ValuationSubring
open _root_.ValuationSubring
open _root_.ValuationSubring
variable {F : Type*} [Field F]
end ValuationSubring
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section CenterIdeal
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))
end CenterIdeal
end Place
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
end
end
section
section
open _root_.Polynomial
open _root_.IsLocalRing
open _root_.AlgebraicCurve
open _root_.ModularCurve.Lg37
open _root_.ModularCurve.KwNo6Section
open _root_.ModularCurve.KwNo6Pin
open _root_.Mp72a102T1
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end AlgebraicCurve
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
theorem ordDifferentialWellDefined_ratFunc_of_perfectField (K : Type*) [Field K]
    [PerfectField K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  · obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section ConsumerGates
variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ConsumerGates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section Defect
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
end Defect
section CorrectedCarrier
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end CorrectedCarrier
section CorrectedBridge
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end CorrectedBridge
section UnitFinite
variable [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end UnitFinite
section CorrectedEngine
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end CorrectedEngine
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
section Defect
variable (K)
variable [DecidableEq (RatFunc K)] [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K
  (RatFunc K)]
end Defect
section CanonicityRow
variable (K F)
variable [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]
variable {K F}
end CanonicityRow
section MOneSimplePoleBounds
variable (K)
variable [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
end MOneSimplePoleBounds
section MOneSimplePoleRow
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
variable {K}
end MOneSimplePoleRow
section CorrectedSubrow2
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {K}
end CorrectedSubrow2
section NearClose
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end NearClose
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
noncomputable section
open _root_.Polynomial
open _root_.IntermediateField
open _root_.AlgebraicCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K : Type*} [Field K]
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
section Engine
variable {K : Type*} [Field K] {N : ℕ} [NeZero N]
end Engine
section Corollaries
variable (K : Type*) [Field K]
end Corollaries
end ModularCurve
end
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section TraceRow
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end TraceRow
section Monotonicity
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Monotonicity
section DegOneDischarge
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end DegOneDischarge
section TraceBridge
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end TraceBridge
section ComposedEngine
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
section AlgClosed
variable [IsAlgClosed K] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end AlgClosed
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section CenterNonzero
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))
end CenterNonzero
section LocalizationSubalgebra
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))
end LocalizationSubalgebra
end Place
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section EulerGeneral
variable [CharZero K] {p : K[X]} [Fact (Irreducible p)]
end EulerGeneral
section AlgEquiv
variable {p : K[X]} (hpirr : Irreducible p)
end AlgEquiv
section TraceTransport
variable {p : K[X]} (hpirr : Irreducible p)
end TraceTransport
section BridgeRows
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
end BridgeRows
section FinitePlaceTrace
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates]
end FinitePlaceTrace
section HigherDegReduction
variable [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end HigherDegReduction
section ComposedEngine
variable [CharZero K] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
end AlgebraicCurve
section AxiomAudits
end AxiomAudits
end
end
end
section
section
open _root_.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
section IntegrallyClosed
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable (B : Subalgebra K F) (hB : (B : Set F) ⊆ (v.toValuationSubring : Set F))
end IntegrallyClosed
end Place
section TwoCharts
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end TwoCharts
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section Gates
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Gates
end AlgebraicCurve
section AxiomAudits
end AxiomAudits
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg
  ord_eq_neg_log_of_valuationSubring_eq
variable (v : Place K F)
end Place
section DerivativeRegular
variable (K)
variable [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end DerivativeRegular
section LeibnizCore
variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end LeibnizCore
section BridgeDischarge
variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [HasLocalResidue K (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end BridgeDischarge
section ComposedEngine
variable (K)
variable [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)]
  [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
end AlgebraicCurve
section AxiomAudits
end AxiomAudits
end
end
end
section
section
open _root_.IsLocalRing
open _root_.IntermediateField
open _root_.IntermediateField.algebraAdjoinAdjoin
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section AdjoinRingProperties
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end AdjoinRingProperties
section TranscendentalChart
variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]
variable {K}
end TranscendentalChart
section IsAffineChartEngine
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
section
variable (B : Subalgebra K F)
end
end IsAffineChartEngine
section SeparatingTranscendental
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end SeparatingTranscendental
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
section AxiomAudits
end AxiomAudits
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section LowDegRegular
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end LowDegRegular
section LowDegValue
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end LowDegValue
section NamedCarriers
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end NamedCarriers
section EraseLeadLinearity
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end EraseLeadLinearity
section ComposedEngine
variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)]
  [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
end AlgebraicCurve
section AxiomAudits
end AxiomAudits
end
end
end
section
section
open _root_.IntermediateField
namespace IntermediateField
open _root_.IntermediateField
open _root_.IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end IntermediateField
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section CharZeroSeparable
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end CharZeroSeparable
section SeparatingTranscendentalCore
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end SeparatingTranscendentalCore
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
section AxiomAudits
end AxiomAudits
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section MonicRatioResidue
end MonicRatioResidue
section NamedCarrier
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end NamedCarrier
section MonicRatioReduction
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end MonicRatioReduction
section ComposedEngine
variable [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)]
  [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
section Monotonicity
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Monotonicity
end AlgebraicCurve
section AxiomAudits
end AxiomAudits
end
end
end
section
section
open _root_.IntermediateField
namespace IntermediateField
open _root_.IntermediateField
open _root_.IntermediateField
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
end IntermediateField
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section PurelyTranscendentalSimple
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable {K F}
end PurelyTranscendentalSimple
section SelfAdjoinInstance
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
end SelfAdjoinInstance
section TowerComposites
variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
end TowerComposites
section AdjoinTowerComposites
variable {K E F' : Type*} [Field K] [Field E] [Field F']
variable [Algebra K E] [Algebra K F']
end AdjoinTowerComposites
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
section AxiomAudits
end AxiomAudits
end
end
section
section
noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
section NamedRow
variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
end NamedRow
section SATGate
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
end SATGate
section XInvCoordinate
variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end XInvCoordinate
section InftyXDischarge
variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end InftyXDischarge
section ComposedEngine
variable (K) [DecidableEq (RatFunc K)] [CharZero K]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)] [HasLocalResidue K (RatFunc K)]
  [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ComposedEngine
section Monotonicity
variable (K) [DecidableEq (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Monotonicity
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end
end
section
section
open _root_.IntermediateField
namespace IntermediateField
open _root_.IntermediateField
open _root_.IntermediateField
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
end IntermediateField
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section Congr
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
end Congr
section RatFuncInstance
variable (K : Type*) [Field K]
end RatFuncInstance
section Iff
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Iff
section CharZeroReflection
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end CharZeroReflection
section TowerComposites
variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
end TowerComposites
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
end ModularCurve
section AxiomAudits
end AxiomAudits
end
end
section
section
open _root_.IntermediateField
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section AbstractEngine
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end AbstractEngine
section ChainComposites
variable {K F F' : Type*} [Field K] [Field F] [Field F']
variable [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
end ChainComposites
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
variable (N : ℕ) [NeZero N]
end ModularCurve
section AxiomAudits
end AxiomAudits
end
end
section
section
noncomputable section
open scoped _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K]
end RationalFunctionField
section TransportTwoRoutes
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
end TransportTwoRoutes
section ConsumerDemonstrations
variable {K : Type*} [Field K] [CharZero K]
end ConsumerDemonstrations
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
open _root_.IntermediateField
section RatBasePinned
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
end RatBasePinned
section RatBaseCrossing
end RatBaseCrossing
end ModularCurve
section AxiomAudits
end AxiomAudits
end
end
end
section
section
noncomputable section
open _root_.KaehlerDifferential
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
section Uniqueness
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Uniqueness
section Profile
variable (K : Type*) [Field K]
section ProfileValues
variable [CharZero K] [DecidableEq (RatFunc K)]
end ProfileValues
section Instance
variable [CharZero K]
end Instance
section ExactDivisor
variable [CharZero K] [DecidableEq (RatFunc K)]
end ExactDivisor
end Profile
section RatDiamond
end RatDiamond
end AlgebraicCurve
namespace ModularCurve
open _root_.ModularCurve
open _root_.AlgebraicCurve
open _root_.IntermediateField
end ModularCurve
section AxiomAudit
end AxiomAudit
end
end
end

section P1PortInst
open scoped _root_.Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace P1PortInst
end AlgebraicCurve.P1PortInst
open scoped _root_.AlgebraicCurve in
instance AlgebraicCurve.P1PortInst.instFormallyEtalePolynomialRatFunc (K : Type*) [Field K] :
    Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

open scoped _root_.AlgebraicCurve in
/-- The singleton basis of rational-function differentials obtained by localization of
polynomial differentials. -/
noncomputable def AlgebraicCurve.P1PortInst.kaehlerRatFuncBasis (K : Type*) [Field K] :
    Module.Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  (((Module.Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm).baseChange
    (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

open scoped _root_.AlgebraicCurve in
instance AlgebraicCurve.P1PortInst.instNontrivialKaehlerRatFunc (K : Type*) [Field K] :
    Nontrivial Ω[(RatFunc K)⁄K] :=
  nontrivial_of_ne _ _ ((AlgebraicCurve.P1PortInst.kaehlerRatFuncBasis K).ne_zero ())

end P1PortInst

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_smul_left (g : F) (ω : Ω[F⁄K]) (α : Place K F → F)
    (v : Place K F) :
    kaehlerResidueTerm (g • ω) α v = kaehlerResidueTerm ω (mulAdele K g α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply, mul_left_comm, mul_assoc]

theorem weilSmul_weilOfKaehler [HasPrincipalDivisors K F] {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) :
    weilSmul K F g (weilOfKaehler K F hω) = weilOfKaehler K F hgω := by
  refine LinearMap.ext fun α => ?_
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  exact finsum_congr fun v => (kaehlerResidueTerm_smul_left g ω α v).symm

theorem weilOfKaehler_smul_diagonal [HasPrincipalDivisors K F] {g : F} {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) (hgω : g • ω ≠ 0) (f : F) :
    weilOfKaehler K F hgω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = weilOfKaehler K F hω ⟨diagonalHom K F (g * f), diagonal_mem_adeleSpace (g * f)⟩ := by
  rw [← weilSmul_weilOfKaehler hω hgω, weilSmul_apply]
  exact congrArg _ (Subtype.ext (funext fun v => by
    simp only [adeleSpaceMul_coe, mulAdele_apply, diagonalHom_apply]))

theorem residueTheorem_iff_of_ne_zero (v : Place K F) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    (∀ [HasPrincipalDivisors K F], ResidueTheorem K F) ↔
      ∀ [HasPrincipalDivisors K F], ∀ f : F,
        weilOfKaehler K F hω₀ ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 := by
  constructor
  · intro hRT _ f; exact hRT hω₀ f
  · intro hsingle _ ω hω f
    obtain ⟨g, hg, rfl⟩ := exists_smul_eq_of_ne_zero v hω hω₀
    rw [weilOfKaehler_smul_diagonal hω₀ hω f]
    exact hsingle (g * f)

section TraceDescent
variable (K F)
variable (E : Type*) [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F]
end TraceDescent
section Engine
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [HasPrincipalDivisors K E]
end Engine
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]
variable (K F) in
/-- The linear residue-sum functional on functions paired with the selected nonzero
differential. -/
def kaehlerResidueFunctional {ω : Ω[F⁄K]} (hω : ω ≠ 0) : F →ₗ[K] K :=
  (weilOfKaehler K F hω).comp (principalAdele K F)

variable (K F) in
/-- The subspace of functions annihilated by the residue-sum functional. -/
def kaehlerResidueKernel {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Submodule K F :=
  LinearMap.ker (kaehlerResidueFunctional K F hω)

theorem mem_kaehlerResidueKernel {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F} :
    f ∈ kaehlerResidueKernel K F hω
      ↔ weilOfKaehler K F hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 :=
  Iff.rfl

theorem residueTheorem_iff_kaehlerResidueKernel_eq_top (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ResidueTheorem K F ↔ kaehlerResidueKernel K F hω₀ = ⊤ := by
  rw [Submodule.eq_top_iff']
  constructor
  · intro h f
    exact (mem_kaehlerResidueKernel hω₀).mpr (h hω₀ f)
  · intro h
    have hsingle : ∀ [HasPrincipalDivisors K F] (f : F),
        weilOfKaehler K F hω₀ ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0 := by
      intro _ f
      exact (mem_kaehlerResidueKernel hω₀).mp (h f)
    intro ω hω f
    exact (residueTheorem_iff_of_ne_zero v hω₀).mpr hsingle hω f

theorem residueTheorem_of_span_le_kernel (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {S : Set F}
    (hspan : Submodule.span K S = ⊤) (hS : S ⊆ kaehlerResidueKernel K F hω₀) :
    ResidueTheorem K F := by
  rw [residueTheorem_iff_kaehlerResidueKernel_eq_top v hω₀]
  exact top_unique (hspan ▸ Submodule.span_le.mpr hS)
omit [HasPrincipalDivisors K F] in
theorem residueTheorem_of_union_span_le_kernel (v : Place K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {S₁ S₂ : Set F} :
    ∀ [HasPrincipalDivisors K F],
      Submodule.span K (S₁ ∪ S₂) = ⊤ →
      S₁ ⊆ kaehlerResidueKernel K F hω₀ →
      S₂ ⊆ kaehlerResidueKernel K F hω₀ →
      ResidueTheorem K F := by
  intro _ hspan hS₁ hS₂
  exact residueTheorem_of_span_le_kernel v hω₀ hspan (Set.union_subset hS₁ hS₂)

section P1NamedRows
open scoped _root_.Polynomial
variable (K)
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- The assertion that the partial-fraction generators span the rational function field. -/
def P1PartialFractionSpan : Prop :=
  Submodule.span K (P1PartialFractionGenerators K) = ⊤

/-- Vanishing of the residue-sum functional on the polynomial generators. -/
def P1ResiduePolynomialPart {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) : Prop :=
  P1PolynomialGenerators K ⊆ kaehlerResidueKernel K (RatFunc K) hω₀

/-- Vanishing of the residue-sum functional on the principal-part generators. -/
def P1ResiduePrincipalPart {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) : Prop :=
  P1PrincipalPartGenerators K ⊆ kaehlerResidueKernel K (RatFunc K) hω₀

variable {K}

omit [HasPrincipalDivisors K (RatFunc K)] in
theorem residueTheorem_ratFunc_of_partialFractions (v : Place K (RatFunc K))
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) :
    ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1PartialFractionSpan K →
      P1ResiduePolynomialPart K hω₀ →
      P1ResiduePrincipalPart K hω₀ →
      ResidueTheorem K (RatFunc K) := by
  intro _ hspan hpoly hprin
  exact residueTheorem_of_union_span_le_kernel v hω₀ hspan hpoly hprin

end P1NamedRows
section P1Gates
open scoped _root_.Polynomial
end P1Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.Polynomial
open _root_.UniqueFactorizationMonoid
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
variable {K : Type*} [Field K]

theorem residueTheorem_ratFunc_of_generators_residue
    [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    (v : Place K (RatFunc K)) {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0) :
    ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1ResiduePolynomialPart K hω₀ → P1ResiduePrincipalPart K hω₀ →
      ResidueTheorem K (RatFunc K) := by
  intro _ hpoly hprin
  exact residueTheorem_ratFunc_of_partialFractions v hω₀ p1PartialFractionSpan_eq_top hpoly hprin

end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]

theorem mem_kaehlerResidueKernel_iff_finsum {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F} :
    f ∈ kaehlerResidueKernel K F hω
      ↔ ∑ᶠ v, kaehlerResidueTerm ω (diagonalHom K F f) v = 0 :=
  Iff.rfl

theorem mem_kaehlerResidueKernel_of_term_zero_compl {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {T : Finset (Place K F)}
    (hcompl : ∀ v ∉ T, kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hsum : ∑ v ∈ T, kaehlerResidueTerm ω (diagonalHom K F f) v = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  rw [mem_kaehlerResidueKernel_iff_finsum hω,
    finsum_eq_finsetSum_of_support_subset _
      (fun v hv => by_contra fun hT => hv (hcompl v hT))]
  exact hsum

theorem mem_kaehlerResidueKernel_of_singleton {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ : Place K F}
    (hcompl : ∀ v, v ≠ v₀ → kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hv₀ : kaehlerResidueTerm ω (diagonalHom K F f) v₀ = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  refine mem_kaehlerResidueKernel_of_term_zero_compl hω (T := {v₀}) ?_ ?_
  · intro v hv
    exact hcompl v (by simpa using hv)
  · simpa using hv₀

theorem mem_kaehlerResidueKernel_of_pair {ω : Ω[F⁄K]} (hω : ω ≠ 0) {f : F}
    {v₀ v₁ : Place K F} (hne : v₀ ≠ v₁)
    (hcompl : ∀ v, v ≠ v₀ → v ≠ v₁ → kaehlerResidueTerm ω (diagonalHom K F f) v = 0)
    (hsum : kaehlerResidueTerm ω (diagonalHom K F f) v₀
      + kaehlerResidueTerm ω (diagonalHom K F f) v₁ = 0) :
    f ∈ kaehlerResidueKernel K F hω := by
  classical
  refine mem_kaehlerResidueKernel_of_term_zero_compl hω (T := {v₀, v₁}) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hcompl v hv.1 hv.2
  · rw [Finset.sum_pair hne]; exact hsum

section RatFuncIntegrality
open _root_.AlgebraicCurve.RationalFunctionField
variable (K)
variable [DecidableEq (RatFunc K)]
end RatFuncIntegrality
section P1PolynomialSubrows
open _root_.AlgebraicCurve.RationalFunctionField
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- Vanishing at infinity of the residue term for every nonnegative power of the variable. -/
def P1PolynomialResidueAtInfinity {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ n : ℕ, kaehlerResidueTerm ω₀
    (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n)) (placeInfty K) = 0

variable {K}

theorem p1ResiduePolynomialPart_of_subrows {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀) :
    P1ResiduePolynomialPart K hω₀ := by
  rintro _ ⟨n, rfl⟩
  refine mem_kaehlerResidueKernel_of_singleton hω₀ (v₀ := placeInfty K) ?_ (hinf n)
  intro v hv
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem (pow_X_mul_mem_of_ne_placeInfty K hv n (hreg v hv)))

end P1PolynomialSubrows
section P1PrincipalPartSubrows
open _root_.AlgebraicCurve.RationalFunctionField
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- Vanishing of a principal-part residue away from its finite pole and infinity. -/
def P1PrincipalPartTermZeroOffSupport {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 1 ≤ m →
    ∀ v : Place K (RatFunc K), v ≠ finitePlace K hpirr → v ≠ placeInfty K →
      kaehlerResidueTerm ω₀
        (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m)) v = 0

/-- Cancellation of the residues at the finite pole and infinity for a principal-part
generator. -/
def P1PrincipalPartTwoPlaceCancel {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 1 ≤ m →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
        (finitePlace K hpirr)
      + kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
          (placeInfty K)
      = 0

variable {K}

theorem p1ResiduePrincipalPart_of_subrows {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hoff : P1PrincipalPartTermZeroOffSupport K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    P1ResiduePrincipalPart K hω₀ := by
  rintro _ ⟨p, c, m, hpmon, hpirr, hdeg, hm, rfl⟩
  exact mem_kaehlerResidueKernel_of_pair hω₀ (finitePlace_ne_placeInfty hpirr)
    (hoff p c m hpmon hpirr hdeg hm) (hcancel p c m hpmon hpirr hdeg hm)

end P1PrincipalPartSubrows
section P1Composed
open _root_.AlgebraicCurve.RationalFunctionField
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
omit [HasPrincipalDivisors K (RatFunc K)] in
theorem residueTheorem_ratFunc_of_four_subrows
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀)
    (hoff : P1PrincipalPartTermZeroOffSupport K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    ∀ [HasPrincipalDivisors K (RatFunc K)], ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_generators_residue (placeInfty K) hω₀
    (p1ResiduePolynomialPart_of_subrows hω₀ hreg hinf)
    (p1ResiduePrincipalPart_of_subrows hω₀ hoff hcancel)

end P1Composed
section Gates
open _root_.AlgebraicCurve.RationalFunctionField
variable [DecidableEq (RatFunc K)]
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
section Reduction
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
omit [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in
theorem p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀) :
    P1PrincipalPartTermZeroOffSupport K hω₀ := by
  intro p c m _hpmon hpirr _hdeg _hm v hvp hvinf
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  exact Or.inr (v.ord_nonneg_of_mem
    (mul_mem (p1PrincipalPartAtom_mem_of_ne_finitePlace K hpirr c m hvp hvinf) (hreg v hvinf)))
omit [HasPrincipalDivisors K (RatFunc K)] in
theorem residueTheorem_ratFunc_of_three_subrows
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hreg : P1DifferentialCoeffRegularFinite K hω₀)
    (hinf : P1PolynomialResidueAtInfinity K hω₀)
    (hcancel : P1PrincipalPartTwoPlaceCancel K hω₀) :
    ∀ [HasPrincipalDivisors K (RatFunc K)], ResidueTheorem K (RatFunc K) :=
  residueTheorem_ratFunc_of_four_subrows hω₀ hreg hinf
    (p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite K hω₀ hreg) hcancel

end Reduction
section CanonicalDivisor
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end CanonicalDivisor
section NamedSubrows
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- The assertion that the selected differential has order minus two at infinity. -/
def P1OrdDifferentialPlaceInftyEqNegTwo {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  (placeInfty K).ordDifferential ω₀ = -2

/-- Cancellation of the finite and infinite residues for a first-order principal-part
generator. -/
def P1PrincipalPartTwoPlaceCancelMOne {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1))
        (finitePlace K hpirr)
      + kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c 1))
          (placeInfty K)
      = 0

variable {K}
end NamedSubrows
section Gates
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable (K)
section InftyVanish
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
omit [HasCanonicalDivisor (K := K) (F := RatFunc K)] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in
theorem kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hInfty : P1OrdDifferentialPlaceInftyEqNegTwo K hω₀)
    {p : K[X]} (hp : Irreducible p) (c : K[X]) {m : ℕ}
    (hdeg : c.degree < p.degree) (hm : 2 ≤ m) :
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
      (placeInfty K) = 0 := by
  refine kaehlerResidueTerm_eq_zero_of_ord_nonneg ?_
  rw [diagonalHom_apply]
  rcases eq_or_ne c 0 with rfl | hc
  · left
    change algebraMap K[X] (RatFunc K) 0 / (algebraMap K[X] (RatFunc K) p) ^ m
        * (placeInfty K).differentialCoeff ω₀ = 0
    rw [map_zero, zero_div, zero_mul]
  · right
    have hatom0 : p1PrincipalPartAtom K p c m ≠ 0 := by
      simp only [p1PrincipalPartAtom, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨(map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc,
        pow_ne_zero _ ((map_ne_zero_iff _
          (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero)⟩
    have hd0 : (placeInfty K).differentialCoeff ω₀ ≠ 0 :=
      (placeInfty K).differentialCoeff_ne_zero hω₀
    rw [(placeInfty K).ord_mul hatom0 hd0]
    have h2 : 2 ≤ (placeInfty K).ord (p1PrincipalPartAtom K p c m) :=
      two_le_ord_placeInfty_p1PrincipalPartAtom K hp hc hdeg hm
    have hordD : (placeInfty K).ord ((placeInfty K).differentialCoeff ω₀) = -2 := hInfty
    omega

end InftyVanish
section NamedSubrow
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

/-- Vanishing of the finite-place residue term for principal parts with denominator exponent at
least two. -/
def P1FinitePlaceTermZeroMGeTwo {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ (p c : K[X]) (m : ℕ) (_ : p.Monic) (hpirr : Irreducible p), c.degree < p.degree → 2 ≤ m →
    kaehlerResidueTerm ω₀ (diagonalHom K (RatFunc K) (p1PrincipalPartAtom K p c m))
      (finitePlace K hpirr) = 0

end NamedSubrow
section MOneReduction
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
omit [HasCanonicalDivisor (K := K) (F := RatFunc K)] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in
theorem p1PrincipalPartTwoPlaceCancel_of_mOne
    {ω₀ : Ω[(RatFunc K)⁄K]} (hω₀ : ω₀ ≠ 0)
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K hω₀)
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K hω₀)
    (hInfty : P1OrdDifferentialPlaceInftyEqNegTwo K hω₀) :
    P1PrincipalPartTwoPlaceCancel K hω₀ := by
  intro p c m hpmon hpirr hdeg hm
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    exact hMOne p c hpmon hpirr hdeg
  · rw [hMGeTwo p c m hpmon hpirr hdeg h2,
      kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m K hω₀ hInfty hpirr c hdeg h2, add_zero]

end MOneReduction
section ComposedEngine
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end ComposedEngine
section UnitFinite
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end UnitFinite
section Gates
variable {K}
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section NonVanishing
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)] in
theorem D_ratFuncX_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) ≠ 0 := by
  classical
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv K, smul_ne_zero_iff]
  exact ⟨neg_ne_zero.mpr (pow_ne_zero 2 RatFunc.X_ne_zero), D_ratFuncX_inv_ne_zero K hwd⟩

end NonVanishing
section DifferentialCoeff
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end DifferentialCoeff
section OrdDifferential
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem p1OrdDifferentialPlaceInftyEqNegTwo_D_X
    [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [HasPrincipalDivisors K (RatFunc K)]
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    P1OrdDifferentialPlaceInftyEqNegTwo K (D_ratFuncX_ne_zero K hwd) :=
  ordDifferential_placeInfty_D_ratFuncX K hwd

end OrdDifferential
section Factorisation
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Factorisation
section NamedSubrow
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
end NamedSubrow
section Bridge
variable [HasCanonicalLocalResidueKStar K (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Bridge
section Gates
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
section MOneSplit
variable [HasPrincipalDivisors K (RatFunc K)]
omit [CharZero K] in
theorem p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo
    (hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K))
    (hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K)) :
    P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) :=
  p1PrincipalPartTwoPlaceCancel_of_mOne (dX_ne_zero K) hMOne hMGeTwo
    (p1OrdDifferentialPlaceInftyEqNegTwo_D_X K hwd)

end MOneSplit
section CanonicalDivisorProfile
end CanonicalDivisorProfile
section Gates
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.KaehlerDifferential
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
section PerfectDCoord
variable (K : Type*) [Field K] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  · obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField

instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField
end PerfectDCoord
section Profile
variable (K : Type*) [Field K]
section PerfectProfileValues
variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem p1DifferentialCoeffRegularFinite_dX_of_perfectField :
    P1DifferentialCoeffRegularFinite K (dX_ne_zero K) :=
  p1DifferentialCoeffRegularFinite_of_unitFinite (dX_ne_zero K)
    (p1DifferentialCoeffUnitFinite_dX_of_perfectField K)

end PerfectProfileValues
section PerfectInstance
variable [PerfectField K]
end PerfectInstance
section PerfectExactDivisor
variable [PerfectField K] [DecidableEq (RatFunc K)]
end PerfectExactDivisor
section CharZeroRoutes
variable [CharZero K]
end CharZeroRoutes
end Profile
section FiniteFieldReadings
end FiniteFieldReadings
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

noncomputable section
open _root_.IsDedekindDomain
open _root_.WithZero
open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.KaehlerDifferential
open _root_.Polynomial
namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open scoped _root_.Polynomial
open _root_.AlgebraicCurve.RationalFunctionField
variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc
  K)]

theorem residueTheorem_ratFunc_of_two_subrows_of_perfectField
    : ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1PolynomialResidueAtInfinity K (dX_ne_zero K) →
      P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) →
      ResidueTheorem K (RatFunc K) := by
  intro _ hinf hcancel
  exact residueTheorem_ratFunc_of_three_subrows K (dX_ne_zero K)
    (p1DifferentialCoeffRegularFinite_dX_of_perfectField K) hinf hcancel

theorem p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField
    : ∀ [HasPrincipalDivisors K (RatFunc K)],
      P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) →
      P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K) →
      P1PrincipalPartTwoPlaceCancel K (dX_ne_zero K) := by
  intro _ hMOne hMGeTwo
  exact p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K) hMOne hMGeTwo

section Gates
end Gates
section CharZeroTwoRoutes
variable (L : Type*) [Field L] [CharZero L] [DecidableEq (RatFunc L)]
end CharZeroTwoRoutes
section Strictness
end Strictness
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

open _root_.AlgebraicCurves.Differentials.Residues.Proofs in
open _root_.AlgebraicCurve in
open _root_.AlgebraicCurve.RationalFunctionField in
open RatFuncResidue.AlgebraicCurve in
open RatFuncResidue.RationalFunctionField in
open RatFuncResidue.AlgebraicCurve.RationalFunctionField in
open _root_.Polynomial in
theorem _root_.AlgebraicCurve.residueTheorem_ratFunc_of_perfectField
    (K : Type*) [Field K] [PerfectField K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]] :
    AlgebraicCurve.ResidueTheorem K (RatFunc K) := by
  classical
  have hinf : P1PolynomialResidueAtInfinity K (dX_ne_zero K) := by
    intro n
    simp only [kaehlerResidueTerm, diagonalHom_apply]
    exact AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero K n
  have hMOne : P1PrincipalPartTwoPlaceCancelMOne K (dX_ne_zero K) := by
    intro p c hmon hpirr hdeg
    simp only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom, pow_one]
    exact trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
      K hmon hpirr hdeg
  have hMGeTwo : P1FinitePlaceTermZeroMGeTwo K (dX_ne_zero K) := by
    intro p c m hmon hpirr hdeg hm
    simp only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom]
    exact AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero K
      hmon hpirr hdeg hm
  intro ω hω f
  exact residueTheorem_ratFunc_of_two_subrows_of_perfectField K hinf
    (p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField K hMOne hMGeTwo) hω f
end AlgebraicCurves.Differentials.Residues.Proofs.RatFuncResidue
end ProofImplementation
