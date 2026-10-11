/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstance.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Completion
import AlgebraicCurves.Differentials.Residues.Construction
import AlgebraicCurves.Differentials.Kaehler.Weil

/-!
Results on Canonical.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section PerfectDischarge

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end PerfectDischarge

end AlgebraicCurve

end

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve.Ldgr37Ch

universe u v

section HenselEngine

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]
variable (i : F →+* R)
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))
variable (abar : IsLocalRing.ResidueField R)

include hi

end HenselEngine

section CoefficientEmbedding

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]
variable (i : F →+* R)
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))
variable (abar : IsLocalRing.ResidueField R)

include hi

end CoefficientEmbedding

section SectionIdentity

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]
variable (i : F →+* R)
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))
variable (abar : IsLocalRing.ResidueField R)

include hi

end SectionIdentity

end ModularCurve.Ldgr37Ch

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable [HasCanonicalLocalResidueKStar K F]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

variable (K F)

variable {K F}

variable (K F)

variable {K F}

variable (K F)

variable {K F}

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve

namespace Place

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end DegPos

end Place

namespace Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')

end Restrict

end Place
end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

private theorem ord_nonneg_of_mem_loc {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

private theorem mem_of_ord_nonneg_loc {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem mem_iff_ord_nonneg_loc {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem_loc, v.mem_of_ord_nonneg_loc hf⟩

end Place

variable [HasCanonicalLocalResidueKStar K F]

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

end Place

namespace Place

variable (v : Place K F)

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

namespace CanonicalLocalResidueDataS

variable {v} {σ : v.CoefficientFieldSection} (R : v.CanonicalLocalResidueDataS σ)

end CanonicalLocalResidueDataS

end Place

end AlgebraicCurve

end

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Polynomial

namespace ModularCurve.Ldgr35Cl

open AlgebraicCurve

end ModularCurve.Ldgr35Cl

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace ModularCurve.Ldgr35Cs

open AlgebraicCurve

end ModularCurve.Ldgr35Cs

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial
open AlgebraicCurve
open scoped Polynomial

end

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Polynomial

namespace ModularCurve.Ldgr36Si

open AlgebraicCurve

section Generic

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end Generic

end ModularCurve.Ldgr36Si

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace ModularCurve.Ldgr36Rc

open AlgebraicCurve
open ModularCurve.Ldgr35Cs
open ModularCurve.Ldgr35Cl

section Restriction

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end Restriction

section ReCarve

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end ReCarve

section NoForkTies

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end NoForkTies

section PaymentRewire

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [HasCanonicalLocalResidueKStar K F']

end PaymentRewire

section Supply

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

end Supply

end ModularCurve.Ldgr36Rc

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace ModularCurve.Lg37

open AlgebraicCurve
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs

section CompletionCarrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end CompletionCarrier

section MovedCarrier

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
variable [HasCanonicalLocalResidueKStar K F']

end MovedCarrier

end ModularCurve.Lg37

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial

namespace Mp72a102T1

open AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Ldgr37Ch

open scoped Polynomial

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Engine

end Mp72a102T1

end

noncomputable section

open IsLocalRing Polynomial

open scoped Polynomial

namespace ModularCurve.Mp72a102T3

open AlgebraicCurve ModularCurve.Lg37

section General

variable {R : Type*} [CommRing R] (I : Ideal R)

end General

section Carrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Carrier

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction

end ModularCurve.Mp72a102T3

end

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing Polynomial

namespace Mp72a102T2

open AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Ldgr35Cs

open scoped Polynomial

section ResidueCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end ResidueCalculus

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end RatProduction

end Mp72a102T2

end

open AlgebraicCurve ModularCurve.Lg37 Polynomial IntermediateField Mp72a102T1 Mp72a102T2

namespace ModularCurve.KwNo6Section

section GenericIso

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end GenericIso

section GenericSection

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end GenericSection

end ModularCurve.KwNo6Section

noncomputable section

open IsDedekindDomain IsLocalRing Polynomial

open scoped Polynomial

namespace Mp72a103T2

open AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3
open Mp72a102T2

section Calculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end Calculus

section RatProduction

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]

end RatProduction

end Mp72a103T2

end

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve.KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end ModularCurve.KwNo6Pin

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve.KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section WitnessW
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))
include hℓ

end WitnessW

end ModularCurve.KwNo6Pin

open Polynomial IsLocalRing AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin
open Mp72a102T1

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end AlgebraicCurve
