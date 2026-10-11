/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Authors: Salvatore Mercuri, Kevin Buzzard
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Ring.RingNF
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Ext
import Lean.Elab.Tactic.RCases
import Aesop.Frontend.Tactic
import Aesop.BuiltinRules
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Differentials.Uniformizer
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Basic
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Valuations.AdicCompletion
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Differentials.Residues.TateTrace
import Nyll.AlgebraicCurves.Places.OverDVR

/-!
Compatibility of Tate constructions with finite extensions.
-/

section ProofImplementation

attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
namespace AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve
end AlgebraicCurve.Place
namespace Filter
open _root_.Filter
open _root_.Filter
end Filter
namespace IsDedekindDomain
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain
end IsDedekindDomain
namespace IsDedekindDomain
open _root_.IsDedekindDomain
namespace HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing
open _root_.IsLocalRing
open _root_.IsLocalRing
end IsLocalRing
namespace LinearMap
open _root_.LinearMap
open _root_.LinearMap
end LinearMap
namespace ModularCurve
open _root_.ModularCurve
namespace KwF4R1V410a
open _root_.ModularCurve
end ModularCurve.KwF4R1V410a
namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve
end ModularCurve.KwF4gRRTate
namespace ModularCurve
open _root_.ModularCurve
namespace Lg37
open _root_.ModularCurve
end ModularCurve.Lg37
namespace MonoidWithZeroHom
open _root_.MonoidWithZeroHom
open _root_.MonoidWithZeroHom
end MonoidWithZeroHom
namespace Multiplicative
open _root_.Multiplicative
open _root_.Multiplicative
end Multiplicative
namespace NumberField
open _root_.NumberField
open _root_.NumberField
end NumberField
namespace Pointwise
open _root_.Pointwise
end Pointwise
namespace Submodule
open _root_.Submodule
open _root_.Submodule
end Submodule
namespace Topology
open _root_.Topology
end Topology
namespace WithZero
open _root_.WithZero
open _root_.WithZero
end WithZero

section
namespace IsLocalRing
open _root_.IsLocalRing
end IsLocalRing
open scoped _root_.IsLocalRing in
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

end

section
section


open _root_.LinearMap
open _root_.Submodule

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateFactoring

end ModularCurve.KwF4gRRTate

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

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

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
open _root_.AlgebraicCurve.Pic0

variable {K F}

end Pic0

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

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
open _root_.AlgebraicCurve.Pic0

open scoped _root_.Pointwise

variable {K F}

end Pic0

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

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
open _root_.IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

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

section

variable {F : Type*} [Field F]

namespace ValuationSubring
open _root_.ValuationSubring
end ValuationSubring
open scoped _root_.ValuationSubring in
theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _

open scoped _root_.ValuationSubring in
theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩

open scoped _root_.ValuationSubring in
theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩

end

end

end

section
section


noncomputable section

open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.WithZero
open _root_.MonoidWithZeroHom

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end AdicCompletion

section Henselian

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end Henselian

section WithValLevel

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end WithValLevel

section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionComap

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end Bridge

end AlgebraicCurve.Place

end
end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem mem_adicIntegersKSubmod_iff (x : u.adicCompletion) :
    x ∈ adicIntegersKSubmod u ↔ x ∈ u.adicCompletionIntegers := Iff.rfl

theorem tateProj_mem_integers (x : u.adicCompletion) :
    tateProj u x ∈ u.adicCompletionIntegers :=
  (mem_adicIntegersKSubmod_iff u _).mp
    (Submodule.coe_mem
      (Submodule.projectionOnto (adicIntegersKSubmod u) _
        (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u))) x))

theorem tateProj_of_mem {x : u.adicCompletion} (hx : x ∈ u.adicCompletionIntegers) :
    tateProj u x = x := by
  have h := Submodule.projectionOnto_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))
    (⟨x, (mem_adicIntegersKSubmod_iff u x).mpr hx⟩ : adicIntegersKSubmod u)
  have hcoe := congrArg (Subtype.val (p := fun y => y ∈ adicIntegersKSubmod u)) h
  exact hcoe

theorem range_tateProj : LinearMap.range (tateProj u) = adicIntegersKSubmod u := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact tateProj_mem_integers u y
  · intro x hx
    exact ⟨x, tateProj_of_mem u hx⟩

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [HasCanonicalLocalResidueKStar K L]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end TateAtoms

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section PoleWindow

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- The K-submodule of completed elements whose poles are cleared by the chosen power of πh. -/
def poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletion where
  carrier := {x | (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, mul_add] at ha hb ⊢; exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_ofPred_eq, mul_zero]; exact zero_mem _
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K L u.adicCompletion, mul_left_comm]
    exact mul_mem ((kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
      (u.algebraMap_mem' c)) hx

theorem mem_poleWindowKSubmod_iff (πh : u.adicCompletionIntegers) (M : ℕ)
    (x : u.adicCompletion) :
    x ∈ poleWindowKSubmod u πh M ↔ (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers :=
  Iff.rfl

theorem adicIntegersKSubmod_le_poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    adicIntegersKSubmod u ≤ poleWindowKSubmod u πh M :=
  fun _ hx => mul_mem (pow_mem πh.2 M) hx

theorem kwF4gRRTate_clearPole (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (fh : u.adicCompletion) :
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers := by
  obtain ⟨a, b, hb, hfh⟩ := IsFractionRing.div_surjective
    (A := u.adicCompletionIntegers) (K := u.adicCompletion) fh
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨M, ub, hbeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπh
  refine ⟨M, ?_⟩
  have hcoe : ∀ x : u.adicCompletionIntegers,
      (x : u.adicCompletion) = algebraMap _ u.adicCompletion x := fun _ => rfl
  have hbK0 : (b : u.adicCompletion) ≠ 0 := by
    rw [hcoe]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hbfh : (b : u.adicCompletion) * fh = (a : u.adicCompletion) := by
    rw [← hfh, hcoe b, hcoe a, mul_div_cancel₀ _ (hcoe b ▸ hbK0)]
  have hπheq : ((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers) * b = πh ^ M := by
    rw [hbeq, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hπheqK : ((((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers)
        : u.adicCompletion)) * (b : u.adicCompletion)
      = (πh : u.adicCompletion)^M := by
    have := congrArg (algebraMap u.adicCompletionIntegers u.adicCompletion) hπheq
    simp only [map_mul, map_pow] at this
    exact this
  rw [← hπheqK, mul_assoc, hbfh]
  exact mul_mem (Subtype.coe_prop _) a.2

variable (K L) in
/-- Every completed element has a pole cleared by some power of an irreducible completed integer. -/
def KwF4gRRTateClearPole : Prop :=
  ∀ (u : Place K L) (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (fh : u.adicCompletion),
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers

theorem kwF4gRRTate_clearPole_discharged : KwF4gRRTateClearPole K L :=
  fun u πh hπh fh => kwF4gRRTate_clearPole u πh hπh fh

theorem lmul_mem_poleWindow (πh : u.adicCompletionIntegers) (M : ℕ) (fh : u.adicCompletion)
    (hM : (πh : u.adicCompletion) ^ M * fh ∈ u.adicCompletionIntegers)
    {a : u.adicCompletion} (ha : a ∈ u.adicCompletionIntegers) :
    fh * a ∈ poleWindowKSubmod u πh M := by
  rw [mem_poleWindowKSubmod_iff, ← mul_assoc]; exact mul_mem hM ha

variable (K L) in
/-- Each pole window modulo the completed integers is finite dimensional over K at a place with
finite residue. -/
def KwF4gRRTatePoleWindowFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K
      (poleWindowKSubmod u πh M ⧸
        (adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)

theorem ker_tateProj_inf_integers :
    LinearMap.ker (tateProj u) ⊓ adicIntegersKSubmod u = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hker, hint⟩ := Submodule.mem_inf.mp hx
  have h0 : tateProj u x = 0 := LinearMap.mem_ker.mp hker
  rw [Submodule.mem_bot, ← tateProj_of_mem u hint, h0]

theorem finiteDimensional_ker_inf_poleWindow [u.FiniteResidue]
    (hPW : KwF4gRRTatePoleWindowFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      ((LinearMap.ker (tateProj u) ⊓ poleWindowKSubmod u πh M : Submodule K _)) := by
  have := hPW u πh hπh M
  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  let A' : Submodule K P := A.comap P.subtype
  let ι : (LinearMap.ker (tateProj u) ⊓ P : Submodule K _) →ₗ[K] P ⧸ A' :=
    (A'.mkQ).comp (Submodule.inclusion inf_le_right)
  refine FiniteDimensional.of_injective ι ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro xh hxker
  obtain ⟨x, hxkp⟩ := xh
  obtain ⟨hxk, hxp⟩ := Submodule.mem_inf.mp hxkp
  simp only [ι, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.inclusion_apply] at hxker
  have hxA : x ∈ A := hxker
  have hx0 : x = 0 := by
    have hbot : x ∈ (⊥ : Submodule K u.adicCompletion) := by
      rw [← ker_tateProj_inf_integers u]; exact Submodule.mem_inf.mpr ⟨hxk, hxA⟩
    exact (Submodule.mem_bot K).mp hbot
  exact Subtype.ext hx0

theorem finiteDimensional_principalPart_range [u.FiniteResidue]
    (hCP : KwF4gRRTateClearPole K L) (hPW : KwF4gRRTatePoleWindowFinite K L)
    (fh : u.adicCompletion) :
    FiniteDimensional K
      (LinearMap.range
        ((LinearMap.id - tateProj u) ∘ₗ lmulK u fh ∘ₗ (adicIntegersKSubmod u).subtype)) := by
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hM⟩ := hCP u πh hπh fh
  have := finiteDimensional_ker_inf_poleWindow u hPW πh hπh M
  refine Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.ker (tateProj u) ⊓ poleWindowKSubmod u πh M) ?_
  rintro y ⟨⟨a, ha⟩, rfl⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
    LinearMap.id_apply]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, tateProj_of_mem u (tateProj_mem_integers u _), sub_self]
  · exact sub_mem (lmul_mem_poleWindow u πh M fh hM ha)
      (adicIntegersKSubmod_le_poleWindowKSubmod u πh M (tateProj_mem_integers u _))

theorem tateComm_target_le_range (pA φ ψ : u.adicCompletion →ₗ[K] u.adicCompletion)
    (Rf Rg : Submodule K u.adicCompletion) :
    Submodule.map (pA ∘ₗ ψ) Rf ⊔ Submodule.map (pA ∘ₗ φ) Rg ≤ LinearMap.range pA := by
  refine sup_le ?_ ?_ <;>
  · rintro y ⟨x, _, rfl⟩; exact LinearMap.mem_range_self pA _

theorem kwF4gRRTate_commFinite_of_clearPole_of_poleWindowFinite
    [∀ u : Place K L, u.FiniteResidue]
    (hCP : KwF4gRRTateClearPole K L) (hPW : KwF4gRRTatePoleWindowFinite K L) :
    KwF4gRRTateCommFinite K L := by
  intro u fh gh
  have hcomm : lmulK u fh ∘ₗ lmulK u gh = lmulK u gh ∘ₗ lmulK u fh := by
    ext x
    change fh * (gh * x) = gh * (fh * x)
    ring
  have hRf := finiteDimensional_principalPart_range u hCP hPW fh
  have hRg := finiteDimensional_principalPart_range u hCP hPW gh
  set pA := tateProj u
  set A := adicIntegersKSubmod u
  set Rf := LinearMap.range ((LinearMap.id - pA) ∘ₗ lmulK u fh ∘ₗ A.subtype)
  set Rg := LinearMap.range ((LinearMap.id - pA) ∘ₗ lmulK u gh ∘ₗ A.subtype)
  set S : Submodule K u.adicCompletion :=
    Submodule.map (pA ∘ₗ lmulK u gh) Rf ⊔ Submodule.map (pA ∘ₗ lmulK u fh) Rg
  have : FiniteDimensional K (Submodule.map (pA ∘ₗ lmulK u gh) Rf) := Module.Finite.map _ _
  have : FiniteDimensional K (Submodule.map (pA ∘ₗ lmulK u fh) Rg) := Module.Finite.map _ _
  have hSfin : FiniteDimensional K S := Submodule.finiteDimensional_sup _ _
  have hSle : S ≤ LinearMap.range pA :=
    tateComm_target_le_range u pA (lmulK u fh) (lmulK u gh) Rf Rg
  have : FiniteDimensional K (S.comap (LinearMap.range pA).subtype) := by
    have e := Submodule.comapSubtypeEquivOfLe hSle
    exact FiniteDimensional.of_injective e.toLinearMap e.injective
  refine Submodule.finiteDimensional_of_le (S₂ := S.comap (LinearMap.range pA).subtype) ?_
  rintro y ⟨⟨a, haR⟩, rfl⟩
  have haA : a ∈ adicIntegersKSubmod u := range_tateProj u ▸ haR
  rw [Submodule.mem_comap, Submodule.subtype_apply, tateCommRestrict_apply,
    tateComm_eq_of_commute hcomm a]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact ⟨(lmulK u fh) a - pA ((lmulK u fh) a), ⟨⟨a, haA⟩, rfl⟩, rfl⟩
  · exact ⟨(lmulK u gh) a - pA ((lmulK u gh) a), ⟨⟨a, haA⟩, rfl⟩, rfl⟩

theorem kwF4gRRTate_commFinite_of_poleWindowFinite [∀ u : Place K L, u.FiniteResidue]
    (hPW : KwF4gRRTatePoleWindowFinite K L) :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_clearPole_of_poleWindowFinite
    kwF4gRRTate_clearPole_discharged hPW

end PoleWindow

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open scoped _root_.WithZero _root_.Multiplicative _root_.Topology
open _root_.Filter

namespace IsDedekindDomain
open _root_.IsDedekindDomain
namespace HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsDedekindDomain

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

namespace adicCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

theorem
_root_.AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite.isOpen_setOf_valued_le
    {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ γ} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have hz0 : vK z ≠ 0 := by rw [hz]; exact hγ
  have hr0 : (vK).restrict z ≠ 0 := fun h =>
    hz0 ((Valuation.restrict_eq_zero_iff vK).mp h)
  have hset : {y : v.adicCompletion K | Valued.v y ≤ γ}
      = {y : v.adicCompletion K | (vK).restrict y ≤ (vK).restrict z} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hz]
  rw [hset]
  exact Valued.isOpen_closedBall _ hr0

end adicCompletion

section NumberField

open _root_.NumberField

variable (F : Type*) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

end NumberField

end IsDedekindDomain.HeightOneSpectrum

section AxiomAudit

open _root_.IsDedekindDomain.HeightOneSpectrum

end AxiomAudit

end

end

section
section


noncomputable section

open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing
open _root_.WithZero
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4R1V410a
open _root_.ModularCurve

scoped instance kwF4R1V410a_subsingletonHeightOneSpectrumDVR
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Subsingleton (HeightOneSpectrum O) :=
  ⟨fun a b => IsDedekindDomain.HeightOneSpectrum.ext
    (((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      inferInstance).2.unique ⟨a.3, a.2⟩ ⟨b.3, b.2⟩)⟩

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring
local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring
local notation "O_W" => w.adicCompletionIntegers
local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

theorem kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff (n : ℕ) (x : O_w) :
    algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n ↔ x ∈ (𝔪_w) ^ n := by
  have hval : Valued.v (algebraMap (O_w) (O_W) x).val
      = w.heightOneSpectrum.intValuation x := by
    have h1 : (algebraMap (O_w) (O_W) x).val
        = ((algebraMap (O_w) F x : F) : w.adicCompletion) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation' (K := F) w.heightOneSpectrum,
      valuation_of_algebraMap]
  rw [adicCompletion.mem_completionIdeal_pow, hval, ← WithZero.exp_eq_coe_ofAdd,
    intValuation_le_pow_iff_mem, w.heightOneSpectrum_asIdeal]

theorem kwF4R1V410a_exists_sub_mem_completionIdeal_pow (n : ℕ) (y : O_W) :
    ∃ x : O_w, y - algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n := by
  have hball_open : IsOpen {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} :=
    (TateCommFinite.isOpen_setOf_valued_le
      F w.heightOneSpectrum
      WithZero.exp_ne_zero).preimage (continuous_sub_right y.val)
  have hy_mem : y.val ∈ {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.mem_ofPred_eq, sub_self, _root_.map_zero]; exact zero_le
  have hmeet := mem_closure_iff.mp
    ((denseRange_algebraMap F w.heightOneSpectrum) y.val) _ hball_open hy_mem
  have hexists : ∃ z : F, Valued.v (algebraMap F w.adicCompletion z - y.val)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hmeet with ⟨z₀, hz₀_ball, z, hz_eq⟩
    exact ⟨z, hz_eq ▸ hz₀_ball⟩
  obtain ⟨z, hz⟩ := hexists
  rw [show algebraMap F w.adicCompletion z = ((z : F) : w.adicCompletion) from rfl] at hz
  have hz_val_le : w.heightOneSpectrum.valuation F z ≤ 1 := by
    have hzhat : Valued.v ((z : w.adicCompletion)) ≤ (1 : ℤᵐ⁰) := by
      calc Valued.v ((z : w.adicCompletion))
          = Valued.v (((z : w.adicCompletion) - y.val) + y.val) := by ring_nf
        _ ≤ max (Valued.v ((z : w.adicCompletion) - y.val)) (Valued.v y.val) :=
            Valuation.map_add _ _ _
        _ ≤ (1 : ℤᵐ⁰) := max_le
            (hz.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)))
            y.2
    rwa [valuedAdicCompletion_eq_valuation'] at hzhat
  have hz_mem : z ∈ (O_w : ValuationSubring F) := by
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one F z
      (fun v' => by
        obtain rfl : v' = w.heightOneSpectrum := Subsingleton.elim _ _
        exact hz_val_le)
    exact hr ▸ r.2
  refine ⟨⟨z, hz_mem⟩, ?_⟩
  rw [adicCompletion.mem_completionIdeal_pow, ← WithZero.exp_eq_coe_ofAdd]
  have hsub : (y - algebraMap (O_w) (O_W) ⟨z, hz_mem⟩ : O_W).val
      = y.val - ((z : F) : w.adicCompletion) := rfl
  rw [hsub, Valuation.map_sub_swap]
  exact hz

/-- Completion induces a ring equivalence modulo corresponding powers of the local maximal
ideals. -/
def
_root_.AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite.kwF4R1V410a_quotientEquiv
    (n : ℕ) :
    (O_w) ⧸ (𝔪_w) ^ n ≃+* (O_W) ⧸ (𝔪_W) ^ n :=
  RingEquiv.ofBijective
    (Ideal.quotientMap _ (algebraMap (O_w) (O_W))
      (fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mpr hx))
    ⟨Ideal.quotientMap_injective'
      (fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mp
        (Ideal.mem_comap.mp hx)),
    fun y => by
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hx⟩ := kwF4R1V410a_exists_sub_mem_completionIdeal_pow w n y'
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      refine (Ideal.quotientMap_mk (J := (𝔪_w) ^ n) (I := (𝔪_W) ^ n)
        (f := algebraMap (O_w) (O_W))
        (H := fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mpr hx)
        (x := x)).trans ?_
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by
        rw [← neg_sub, neg_mem_iff]; exact hx)⟩

theorem
_root_.AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite.kwF4R1V410a_quotientEquiv_mk
    (n : ℕ) (x : O_w) :
    TateCommFinite.kwF4R1V410a_quotientEquiv w n (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk _ (algebraMap (O_w) (O_W) x) := rfl

end Bridge

end ModularCurve.KwF4R1V410a

end
end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem coe_smul_K (c : K) (x : u.adicCompletionIntegers) :
    ((c • x : u.adicCompletionIntegers) : u.adicCompletion) = c • (x : u.adicCompletion) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

/-- Multiplication by πh to the power M sends the pole window to the completed integers. -/
def poleWindowShift (πh : u.adicCompletionIntegers) (M : ℕ) :
    poleWindowKSubmod u πh M →ₗ[K] u.adicCompletionIntegers where
  toFun x := ⟨(πh : u.adicCompletion)^M * (x : u.adicCompletion), x.2⟩
  map_add' x y := by apply Subtype.ext; push_cast; ring
  map_smul' c x := by
    apply Subtype.ext
    rw [coe_smul_K]
    change (πh : u.adicCompletion)^M * (c • (x : u.adicCompletion))
        = c • ((πh : u.adicCompletion)^M * (x : u.adicCompletion))
    rw [mul_smul_comm]

theorem poleWindowShift_injective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Injective (poleWindowShift u πh M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz
    exact hπh.ne_zero (Subtype.ext hz)
  have hx0 : (x : u.adicCompletion) = 0 := by
    have := congrArg Subtype.val hx
    exact (mul_eq_zero.mp this).resolve_left hπhM0
  exact Subtype.ext hx0

theorem poleWindowShift_surjective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Surjective (poleWindowShift u πh M) := by
  intro y
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz; exact hπh.ne_zero (Subtype.ext hz)
  refine ⟨⟨(y : u.adicCompletion) / (πh : u.adicCompletion)^M, ?_⟩, ?_⟩
  · rw [mem_poleWindowKSubmod_iff, mul_div_cancel₀ _ hπhM0]; exact y.2
  · apply Subtype.ext
    change (πh : u.adicCompletion)^M * ((y : u.adicCompletion) / (πh : u.adicCompletion)^M)
        = (y : u.adicCompletion)
    rw [mul_div_cancel₀ _ hπhM0]

/-- Multiplication by an irreducible πh to the power M identifies the pole window with the
completed integers. -/
def poleWindowShiftEquiv (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    poleWindowKSubmod u πh M ≃ₗ[K] u.adicCompletionIntegers :=
  LinearEquiv.ofBijective (poleWindowShift u πh M)
    ⟨poleWindowShift_injective u πh hπh M, poleWindowShift_surjective u πh hπh M⟩

/-- The K-submodule of completed integers divisible by πh to the power M. -/
def piPowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletionIntegers where
  carrier := {y | ∃ x : u.adicCompletionIntegers, y = πh^M * x}
  add_mem' := by rintro a b ⟨xa, rfl⟩ ⟨xb, rfl⟩; exact ⟨xa + xb, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  smul_mem' c y := by
    rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

theorem poleWindowShift_image_integers (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule.map (poleWindowShift u πh M)
        ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
      = piPowKSubmod u πh M := by
  ext y
  constructor
  · rintro ⟨⟨x, hxP⟩, hxA, rfl⟩
    refine ⟨⟨(x : u.adicCompletion), hxA⟩, ?_⟩
    apply Subtype.ext; push_cast; rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : u.adicCompletion),
      adicIntegersKSubmod_le_poleWindowKSubmod u πh M x.2⟩, x.2, ?_⟩
    apply Subtype.ext; push_cast; rfl

variable (K L) in
/-- Quotients of completed integers by powers of an irreducible element are finite dimensional
over K. -/
def KwF4gRRTateDVRQuotPowKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)

theorem kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (hDVR : KwF4gRRTateDVRQuotPowKFinite K L) :
    KwF4gRRTatePoleWindowFinite K L := by
  intro u _ πh hπh M
  have := hDVR u πh hπh M
  have e := (poleWindowShiftEquiv u πh hπh M).toLinearMap
  let e' := Submodule.Quotient.equiv
    ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
    (piPowKSubmod u πh M)
    (poleWindowShiftEquiv u πh hπh M)
    (poleWindowShift_image_integers u πh M)
  exact FiniteDimensional.of_injective e'.toLinearMap e'.injective

theorem kwF4gRRTate_commFinite_of_DVRQuotPowKFinite [∀ u : Place K L, u.FiniteResidue]
    (hDVR : KwF4gRRTateDVRQuotPowKFinite K L) :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_poleWindowFinite
    (kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite hDVR)

end PoleWindowShift

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DVRQuotDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem piPowKSubmod_eq_restrictScalars (πh : u.adicCompletionIntegers) (M : ℕ) :
    piPowKSubmod u πh M
      = (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, h⟩⟩

/-- Identifies the quotient by the K-submodule of multiples of πh to the power M with the
corresponding ideal quotient. -/
def quotPiPowEquivIdealQuot (πh : u.adicCompletionIntegers) (M : ℕ) :
    (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)
      ≃ₗ[K] (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) :=
  (Submodule.quotEquivOfEq _ _ (piPowKSubmod_eq_restrictScalars u πh M)).trans
    (Submodule.Quotient.restrictScalarsEquiv K _)

variable (K L) in
/-- The quotient of completed integers by an irreducible element is finite dimensional over K at
each place with finite residue. -/
def KwF4gRRTateDVRCotangentKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh),
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))

theorem range_mulLeft_eq_restrictScalars_span (a : u.adicCompletionIntegers) :
    LinearMap.range (LinearMap.mulLeft K a)
      = (Ideal.span {a} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩


theorem finiteDimensional_restrictScalarsQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K (u.adicCompletionIntegers ⧸
      (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
  induction M with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Submodule.restrictScalars_top]
    infer_instance
  | succ M ih =>
    have hle : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)
        ≤ Ideal.span {πh^M} := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact ⟨πh, rfl⟩
    have hle' : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K
        ≤ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K :=
      Submodule.restrictScalars_mono K hle
    set N : Submodule K (u.adicCompletionIntegers ⧸
        (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
      (Submodule.restrictScalars K (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)).map
        (Submodule.restrictScalars K (Ideal.span {πh^(M+1)} : Ideal _)).mkQ with hN_def
    have hquot : FiniteDimensional K
        ((u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal _).restrictScalars K) ⧸ N) := by
      have := ih
      exact Module.Finite.equiv
        (Submodule.quotientQuotientEquivQuotient _ _ hle').symm
    have hN : FiniteDimensional K N := by
      set φ : u.adicCompletionIntegers →ₗ[K] (u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
        (Submodule.restrictScalars K
            (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)).mkQ ∘ₗ
          LinearMap.mulLeft K (πh^M) with hφ_def
      have hrange : LinearMap.range φ = N := by
        rw [hφ_def, LinearMap.range_comp, range_mulLeft_eq_restrictScalars_span, hN_def]
      have hker : LinearMap.ker φ
          = (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K := by
        simp only [hφ_def, LinearMap.ker_comp, Submodule.ker_mkQ]
        ext x
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
          Ideal.mem_span_singleton]
        have hπM : (πh : u.adicCompletionIntegers)^M ≠ 0 := pow_ne_zero M hπh.ne_zero
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, mul_left_cancel₀ hπM (by rw [hc, pow_succ, mul_assoc])⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, by rw [hc, pow_succ, mul_assoc]⟩
      let e₁ : (u.adicCompletionIntegers ⧸
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K)
          ≃ₗ[K] (u.adicCompletionIntegers ⧸ LinearMap.ker φ) :=
        Submodule.quotEquivOfEq _ _ hker.symm
      let e₂ : (u.adicCompletionIntegers ⧸ LinearMap.ker φ) ≃ₗ[K] LinearMap.range φ :=
        φ.quotKerEquivRange
      let e₃ : (LinearMap.range φ : Submodule K _) ≃ₗ[K] N := LinearEquiv.ofEq _ _ hrange
      have hCK : FiniteDimensional K (u.adicCompletionIntegers ⧸
          (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
        have := hCot u πh hπh
        exact Module.Finite.equiv
          (Submodule.Quotient.restrictScalarsEquiv K
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers)).symm
      exact Module.Finite.equiv ((e₁.trans e₂).trans e₃)
    exact Module.Finite.of_submodule_quotient N

theorem finiteDimensional_idealQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) := by
  have := finiteDimensional_restrictScalarsQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K _)

theorem kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
    (hCot : KwF4gRRTateDVRCotangentKFinite K L) :
    KwF4gRRTateDVRQuotPowKFinite K L := by
  intro u _ πh hπh M
  have := finiteDimensional_idealQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (quotPiPowEquivIdealQuot u πh M).symm

theorem kwF4gRRTate_commFinite_of_cotangent [∀ u : Place K L, u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L) :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_DVRQuotPowKFinite
    (kwF4gRRTate_DVRQuotPowKFinite_of_cotangent hCot)

end DVRQuotDischarge

end ModularCurve.KwF4gRRTate

end

end

end

section
section


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.IsLocalRing

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DVRCotangentDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

scoped instance instIsScalarTower_K_toValuationSubring_adicCompletionIntegers :
    IsScalarTower K u.toValuationSubring u.adicCompletionIntegers := by
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  apply Subtype.ext
  change algebraMap K u.adicCompletion k
    = (algebraMap u.toValuationSubring u.adicCompletionIntegers (algebraMap K _ k)).val
  rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
  rfl

theorem span_irreducible_eq_completionIdeal_pow_one
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (Ideal.span {πh} : Ideal u.adicCompletionIntegers)
      = (u.heightOneSpectrum.completionIdeal L) ^ 1 := by
  rw [pow_one, ← hπh.maximalIdeal_eq]

/-- Completion induces a K-algebra equivalence modulo corresponding powers of the local maximal
ideals. -/
def quotientEquivKAlg (n : ℕ) :
    (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n)
      ≃ₐ[K] (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n) :=
  { TateCommFinite.kwF4R1V410a_quotientEquiv u n with
    commutes' := fun k => by
      change TateCommFinite.kwF4R1V410a_quotientEquiv u n (algebraMap K _ k) = algebraMap K _ k
      rw [IsScalarTower.algebraMap_apply K u.toValuationSubring
          (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n),
        Ideal.Quotient.algebraMap_eq,
          TateCommFinite.kwF4R1V410a_quotientEquiv_mk,
        IsScalarTower.algebraMap_apply K u.adicCompletionIntegers
          (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n),
        Ideal.Quotient.algebraMap_eq,
        IsScalarTower.algebraMap_apply K u.toValuationSubring u.adicCompletionIntegers] }

/-- Identifies the quotient of completed integers by an irreducible element with the residue
field over K. -/
def quotSpanIrreducibleEquivResidueField (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))
      ≃ₗ[K] u.ResidueField :=
  (Ideal.quotientEquivAlgOfEq K
      (span_irreducible_eq_completionIdeal_pow_one u πh hπh)).toLinearEquiv.trans
    ((quotientEquivKAlg u 1).symm.toLinearEquiv.trans
      (Ideal.quotientEquivAlgOfEq K
        (pow_one (IsLocalRing.maximalIdeal u.toValuationSubring))).toLinearEquiv)

theorem kwF4gRRTate_DVRCotangentKFinite : KwF4gRRTateDVRCotangentKFinite K L := by
  intro u _ πh hπh
  have : Module.Finite K u.ResidueField := FiniteResidue.finite
  exact Module.Finite.equiv (quotSpanIrreducibleEquivResidueField u πh hπh).symm

theorem kwF4gRRTate_commFinite [∀ u : Place K L, u.FiniteResidue] :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_cotangent kwF4gRRTate_DVRCotangentKFinite

end DVRCotangentDischarge

end ModularCurve.KwF4gRRTate

end

end

end

theorem _root_.AlgebraicCurve.tateCommFinite {K L : Type*} [Field K] [Field L] [Algebra K L]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue] :
    ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_commFinite
end AlgebraicCurves.Differentials.Residues.Proofs.TateCommFinite
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
