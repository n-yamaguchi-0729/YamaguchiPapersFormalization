/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientAnnihilator
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroCoefficients
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPowerTorsionAcyclic
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionQuotient
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Local cohomology along an injective chain

The cycle--boundary and boundary--homology short exact sequences are
constructed directly from the differentials. Their coefficient sequences
allow scalar annihilators to be propagated up the chain.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

/-- Concrete cycles in a chain complex of modules. -/
def linearChainCycles (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Submodule R (K.X n) := LinearMap.ker (K.d n (n - 1)).hom

/-- The incoming differential with its values restricted to cycles. -/
def linearChainToCycles (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.X (n + 1) →ₗ[R] linearChainCycles K n :=
  (K.sc' (n + 1) n (n - 1)).moduleCatToCycles

/-- Concrete boundaries as a submodule of cycles. -/
def linearChainBoundaries (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Submodule R (linearChainCycles K n) := LinearMap.range (linearChainToCycles K n)

/-- The short exact sequence from boundaries to cycles to homology. -/
def linearChainBoundaryHomologySequence
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (linearChainBoundaries K n).subtype
    (linearChainBoundaries K n).mkQ
    (LinearMap.exact_subtype_mkQ (linearChainBoundaries K n)).linearMap_comp_eq_zero

theorem linearChainBoundaryHomologySequence_shortExact
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (linearChainBoundaryHomologySequence K n).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (LinearMap.exact_subtype_mkQ (linearChainBoundaries K n))
    (linearChainBoundaries K n).subtype_injective
    (linearChainBoundaries K n).mkQ_surjective

private theorem next_chain_nat (n : ℕ) :
    (ComplexShape.down ℕ).next n = n - 1 := by
  cases n with
  | zero => exact ChainComplex.next_nat_zero
  | succ n => exact ChainComplex.next_nat_succ n

/-- The cycle quotient is the actual homology of the chain complex. -/
def linearChainHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.homology n ≅ (linearChainBoundaryHomologySequence K n).X₃ :=
  ShortComplex.homologyMapIso
      (K.isoSc' (n + 1) n (n - 1) (ChainComplex.prev ℕ n) (next_chain_nat n)) ≪≫
    (K.sc' (n + 1) n (n - 1)).moduleCatHomologyIso

/-- If the incoming chain term is zero, the cycle quotient has no
boundaries, so the homology identifies with the actual cycle submodule. -/
def linearChainTopHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (hz : IsZero (K.X (n + 1))) :
    K.homology n ≅ ModuleCat.of R (linearChainCycles K n) := by
  have hB : linearChainBoundaries K n = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro z
    have hmap : ModuleCat.ofHom (linearChainToCycles K n) = 0 := hz.eq_of_src _ _
    exact congrArg (fun f : K.X (n + 1) ⟶ ModuleCat.of R (linearChainCycles K n) => f z) hmap
  exact linearChainHomologyIso K n ≪≫
    (Submodule.quotEquivOfEqBot (linearChainBoundaries K n) hB).toModuleIso

private theorem linearChainCycleBoundary_comp_eq_zero
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (linearChainToCycles K n).rangeRestrict.comp (linearChainCycles K (n + 1)).subtype = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  exact z.property

/-- The short exact sequence from cycles to a chain term to the preceding
boundaries. -/
def linearChainCycleBoundarySequence
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (linearChainCycles K (n + 1)).subtype
    (linearChainToCycles K n).rangeRestrict
    (linearChainCycleBoundary_comp_eq_zero K n)

theorem linearChainCycleBoundarySequence_shortExact
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (linearChainCycleBoundarySequence K n).ShortExact := by
  apply ModuleCat.shortComplex_shortExact _ _
    (linearChainCycles K (n + 1)).subtype_injective
    (linearChainToCycles K n).surjective_rangeRestrict
  intro b
  constructor
  · intro hb
    refine ⟨⟨b, ?_⟩, rfl⟩
    exact congrArg (fun z : linearChainBoundaries K n => ((z : linearChainCycles K n) : K.X n)) hb
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact z.property

private theorem linearChainCycleBoundary_zero_surjective
    (I : Ideal R) (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hΓ : Function.Surjective ((idealPowerTorsionFunctor I).map (K.d 1 0))) :
    Function.Surjective (derivedLocalCohomologyModuleCoefficientsSecondMap I
      (linearChainCycleBoundarySequence_shortExact K 0) 0) := by
  change Function.Surjective (Ideal.primaryComponent.map I (K.d 1 0).hom) at hΓ
  let S := linearChainCycleBoundarySequence K 0
  let hS := linearChainCycleBoundarySequence_shortExact K 0
  let j : S.X₃ →ₗ[R] K.X 0 :=
    (linearChainCycles K 0).subtype.comp (linearChainBoundaries K 0).subtype
  let e₁ := derivedLocalCohomologyZeroEquivPrimaryComponent I S.X₂
  let e₃ := derivedLocalCohomologyZeroEquivPrimaryComponent I S.X₃
  intro z
  obtain ⟨w, hw⟩ := hΓ ((idealPowerTorsionFunctor I).map (ModuleCat.ofHom j) (e₃ z))
  let y := e₁.symm w
  refine ⟨y, (derivedLocalCohomologyZeroToModule_injective I S.X₃) ?_⟩
  have heval : derivedLocalCohomologyZeroToModule I S.X₂ y = (w : K.X 1) :=
    congrArg Subtype.val (e₁.apply_symm_apply w)
  have hlinear : (K.d 1 0) (w : K.X 1) = j (derivedLocalCohomologyZeroToModule I S.X₃ z) :=
    congrArg Subtype.val hw
  rw [show derivedLocalCohomologyZeroToModule I S.X₃
        (derivedLocalCohomologyModuleCoefficientsSecondMap I hS 0 y) =
      S.g.hom (derivedLocalCohomologyZeroToModule I S.X₂ y) from
        DFunLike.congr_fun (derivedLocalCohomologyZeroToModule_comp_secondMap I hS) y]
  apply Subtype.ext
  apply Subtype.ext
  change (K.d 1 0) (derivedLocalCohomologyZeroToModule I S.X₂ y) =
    j (derivedLocalCohomologyZeroToModule I S.X₃ z)
  rw [heval]
  exact hlinear

private theorem linearChainCycles_localCohomology_one_eq_zero
    (I : Ideal R) (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [Module.Injective R (K.X 1)]
    (hΓ : Function.Surjective ((idealPowerTorsionFunctor I).map (K.d 1 0)))
    (z : derivedLocalCohomologyModule I (ModuleCat.of R (linearChainCycles K 1)) 1) :
    z = 0 := by
  let S := linearChainCycleBoundarySequence K 0
  let hS := linearChainCycleBoundarySequence_shortExact K 0
  let : Module.Injective R S.X₂ := by
    change Module.Injective R (K.X 1)
    infer_instance
  let : Subsingleton (derivedLocalCohomologyModule I S.X₂ 1) :=
    AddCommGrpCat.subsingleton_of_isZero
      (derivedLocalCohomology_isZero_succ_of_injective I S.X₂ 0)
  obtain ⟨w, hw⟩ :=
    (derivedLocalCohomologyModuleCoefficients_afterConnecting_exact I hS 0 z).mp
      (Subsingleton.elim _ _)
  obtain ⟨v, hv⟩ := linearChainCycleBoundary_zero_surjective I K hΓ w
  rw [← hw, ← hv]
  exact (derivedLocalCohomologyModuleCoefficients_beforeConnecting_exact
    I hS 0).apply_apply_eq_zero v

/-- The lower homology annihilator propagates along an injective chain.
Surjectivity of the initial differential on ideal-power torsion supplies
the degree-one base case; each subsequent homology term contributes one
factor of the scalar. -/
theorem linearChainCycles_localCohomology_pow_smul_eq_zero
    (I : Ideal R) (K : ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ j : ℕ, Module.Injective R (K.X j)]
    (hΓ : Function.Surjective ((idealPowerTorsionFunctor I).map (K.d 1 0)))
    (a : R) (n : ℕ)
    (ha : ∀ i : ℕ, i < n → ∀ h : K.homology (i + 1), a • h = 0)
    (z : derivedLocalCohomologyModule I
      (ModuleCat.of R (linearChainCycles K (n + 1))) (n + 1)) :
    a ^ n • z = 0 := by
  induction n with
  | zero =>
      rw [pow_zero, one_smul]
      exact linearChainCycles_localCohomology_one_eq_zero I K hΓ z
  | succ n ih =>
      have hZ : ∀ w : derivedLocalCohomologyModule I
          (ModuleCat.of R (linearChainCycles K (n + 1))) (n + 1), a ^ n • w = 0 :=
        fun w => ih (fun i hi => ha i (Nat.lt_succ_of_lt hi)) w
      let T := linearChainBoundaryHomologySequence K (n + 1)
      let hT := linearChainBoundaryHomologySequence_shortExact K (n + 1)
      have hH : ∀ w : T.X₃, a • w = 0 := by
        intro w
        let e := linearChainHomologyIso K (n + 1)
        apply (ModuleCat.mono_iff_injective e.inv).mp inferInstance
        change e.inv.hom (a • w) = e.inv.hom 0
        rw [map_smul, map_zero]
        exact ha n (Nat.lt_succ_self n) (e.inv w)
      have hB : ∀ w : derivedLocalCohomologyModule I T.X₁ (n + 1),
          a ^ (n + 1) • w = 0 := by
        intro w
        rw [pow_succ']
        exact derivedLocalCohomologyModule_mul_smul_eq_zero_of_shortExact
          I hT n a (a ^ n) hH hZ w
      let : Module.Injective R (linearChainCycleBoundarySequence K (n + 1)).X₂ := by
        change Module.Injective R (K.X (n + 1 + 1))
        infer_instance
      exact derivedLocalCohomologyModule_smul_eq_zero_of_injective_middle
        I (linearChainCycleBoundarySequence_shortExact K (n + 1))
        (n + 1) (a ^ (n + 1)) hB z

end EtaleFundamentalGroups.Purity

end
