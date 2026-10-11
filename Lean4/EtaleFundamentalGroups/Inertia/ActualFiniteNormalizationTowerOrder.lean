/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationLocalTower
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteLevelNormalizationAlgebra
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.UniformizerRadicalRamification
import SchemeTheory.Normalization.SubalgebraNormalizationTowerRamification
import SchemeTheory.Normalization.NativeNormalizationPrime
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.RingTheory.Localization.DedekindPrime
import ValuedFieldTheory.Ramification.HilbertRamification.DVRUniformizerFactorization
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Uniformizer orders in finite normalization towers

Relates the upper ramification index to the lower index and the additive valuation of a lower
uniformizer under the local inclusion.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v w

/-- The closed valuation calculation from the supplied original coefficient
triangle and the already computed orders of one original uniformizer. -/
private theorem index_mul_of_coefficient_factorization
    (A : Type u) (S : Type v) (T : Type w)
    [CommRing A] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (cE : A →+* S) (cF : A →+* T) (f : S →+* T)
    (a : A) (ha : Irreducible a) (eE eF : ℕ)
    (heE : eE = (IsDiscreteValuationRing.addVal S (cE.toFun a)).toNat)
    (heF : eF = (IsDiscreteValuationRing.addVal T (cF.toFun a)).toNat)
    (hcE : Function.Injective cE.toFun) (hbase : f.comp cE = cF) :
    ∀ π : S, Irreducible π →
      eF = (IsDiscreteValuationRing.addVal T (f.toFun π)).toNat * eE := by
  intro π hπ
  obtain ⟨unit, hunit⟩ := mappedUniformizer_factorization_addVal A S cE hcE a ha π hπ
  have hfactor : cE.toFun a = π ^ eE * unit.val := by
    rw [heE]
    exact hunit
  have hupper : cF.toFun a = (f.toFun π) ^ eE * f.toFun unit.val := by
    exact (RingHom.congr_fun hbase a).symm.trans
      ((congrArg f.toFun hfactor).trans
        ((map_mul f (π ^ eE) unit.val).trans
          (congrArg (fun z : T => z * f.toFun unit.val) (map_pow f π eE))))
  have hunitVal : IsDiscreteValuationRing.addVal T (f.toFun unit.val) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (unit.isUnit.map f)
  have hval : IsDiscreteValuationRing.addVal T (cF.toFun a) =
      eE • IsDiscreteValuationRing.addVal T (f.toFun π) := by
    rw [hupper, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, hunitVal, add_zero]
  calc
    eF = (IsDiscreteValuationRing.addVal T (cF.toFun a)).toNat := heF
    _ = (eE • IsDiscreteValuationRing.addVal T (f.toFun π)).toNat :=
      congrArg ENat.toNat hval
    _ = eE * (IsDiscreteValuationRing.addVal T (f.toFun π)).toNat := by
      rw [nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast]
    _ = (IsDiscreteValuationRing.addVal T (f.toFun π)).toNat * eE := Nat.mul_comm _ _


/-- The prescribed coefficient inclusion is injective, established before
any second finite stage or local ring is opened. -/
private theorem actualFinite_coefficient_injective
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (E : FiniteGaloisIntermediateField K L) :
    Function.Injective (algebraMap A (finiteAbsoluteNormalizationAlgebra A K L E)) := by
  have tfAL : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have faithful : FaithfulSMul A (finiteAbsoluteNormalizationAlgebra A K L E) :=
    subalgebraNormalizationCommAlgCat_faithfulSMul
      (finiteLevelNormalizationSubalgebra A K L E)
  exact FaithfulSMul.algebraMap_injective A (finiteAbsoluteNormalizationAlgebra A K L E)

/-- The actual upper ramification index is the lower index times the raw
local uniformizer exponent. This is expressed directly through the literal
local inclusion consumed by the canonical character, so no alternate scalar
action on either local ring is needed. -/
theorem actualFiniteNormalization_ramificationIdx_tower_addVal
    (A : Type u) (K : Type v) (L : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fL : Field L] [aAK : Algebra A K] [frAK : IsFractionRing A K]
    [aKL : Algebra K L] [aAL : Algebra A L] [tAKL : IsScalarTower A K L]
    [gKL : IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [qMax : Q.IsMaximal]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
    letI := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
    letI := localizationAtPrime_isDiscreteValuationRing
      (finiteAbsoluteNormalizationAlgebra A K L F)
      (finiteAbsoluteNormalizationPrime A K L Q F)
      (finiteAbsoluteNormalizationPrime_ne_bot A K L Q F)
    ∀ π : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E),
      Irreducible π →
      (finiteAbsoluteNormalizationPrime A K L Q F).ramificationIdx A =
        ((IsDiscreteValuationRing.addVal
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F))).toFun
          ((actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).toFun π)).toNat *
        (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A := by
  let B := finiteAbsoluteNormalizationAlgebra A K L E
  let C := finiteAbsoluteNormalizationAlgebra A K L F
  let P : Ideal B := finiteAbsoluteNormalizationPrime A K L Q E
  let R : Ideal C := finiteAbsoluteNormalizationPrime A K L Q F
  have pP : P.IsPrime := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have pR : R.IsPrime := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  have dB : IsDedekindDomain B := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have dC : IsDedekindDomain C := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
  have hP : P ≠ ⊥ := finiteAbsoluteNormalizationPrime_ne_bot A K L Q E
  have hR : R ≠ ⊥ := finiteAbsoluteNormalizationPrime_ne_bot A K L Q F
  have overP : P.LiesOver (IsLocalRing.maximalIdeal A) :=
    subalgebraNormalizationPrime_liesOver_maximalIdeal
      (finiteLevelNormalizationSubalgebra A K L E) Q
  have overR : R.LiesOver (IsLocalRing.maximalIdeal A) :=
    subalgebraNormalizationPrime_liesOver_maximalIdeal
      (finiteLevelNormalizationSubalgebra A K L F) Q
  let g : B →+* C := actualFiniteNormalizationTowerRingMap A K L E F h
  have hg : P = R.comap g := actualFiniteNormalizationPrime_tower A K L Q E F h
  have hcoeff : g.comp (algebraMap A B) = algebraMap A C :=
    subalgebraNormalizationTowerRingMap_comp_base
      (finiteLevelNormalizationSubalgebra A K L E)
      (finiteLevelNormalizationSubalgebra A K L F) h
  have hinjAB : Function.Injective (algebraMap A B) :=
    actualFinite_coefficient_injective A K L E
  change letI : IsDiscreteValuationRing (Localization.AtPrime R) :=
      localizationAtPrime_isDiscreteValuationRing C R hR
    ∀ π : Localization.AtPrime P, Irreducible π →
      R.ramificationIdx A =
        (IsDiscreteValuationRing.addVal (Localization.AtPrime R)
          ((Localization.localRingHom P R g hg).toFun π)).toNat * P.ramificationIdx A
  clear_value g P R B C
  clear h E F qMax Q gKL tAKL aAL aKL frAK aAK fL L fK K
  let S : Type w := Localization.AtPrime P
  let rS : CommRing S := inferInstanceAs (CommRing (Localization.AtPrime P))
  let T : Type w := Localization.AtPrime R
  let rT : CommRing T := inferInstanceAs (CommRing (Localization.AtPrime R))
  have dS : IsDomain S := inferInstanceAs (IsDomain (Localization.AtPrime P))
  have dT : IsDomain T := inferInstanceAs (IsDomain (Localization.AtPrime R))
  have vS : IsDiscreteValuationRing S := localizationAtPrime_isDiscreteValuationRing B P hP
  have vT : IsDiscreteValuationRing T := localizationAtPrime_isDiscreteValuationRing C R hR
  let cE : A →+* S := (algebraMap B S).comp (algebraMap A B)
  let cF : A →+* T := (algebraMap C T).comp (algebraMap A C)
  let f : S →+* T := Localization.localRingHom P R g hg
  let eE : ℕ := P.ramificationIdx A
  let eF : ℕ := R.ramificationIdx A
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible A
  have heE : eE = (IsDiscreteValuationRing.addVal S (cE.toFun a)).toNat :=
    (ramificationIdx_eq_ord_localized_uniformizer P a ha).trans
      (congrArg ENat.toNat (Ring.ord_eq_addVal (cE.toFun a)))
  have heF : eF = (IsDiscreteValuationRing.addVal T (cF.toFun a)).toNat :=
    (ramificationIdx_eq_ord_localized_uniformizer R a ha).trans
      (congrArg ENat.toNat (Ring.ord_eq_addVal (cF.toFun a)))
  have hcE : Function.Injective cE.toFun :=
    (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors).comp hinjAB
  have hbase : f.comp cE = cF := by
    apply RingHom.ext
    intro x
    exact (Localization.localRingHom_to_map P R g hg (algebraMap A B x)).trans
      (congrArg (algebraMap C T) (RingHom.congr_fun hcoeff x))
  change ∀ π : S, Irreducible π →
    eF = (IsDiscreteValuationRing.addVal T (f.toFun π)).toNat * eE
  exact index_mul_of_coefficient_factorization A S T cE cF f a ha eE eF heE heF hcE hbase

end EtaleFundamentalGroups.Inertia

end
