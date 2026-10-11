/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CechInjectiveDegreeZero
import Nyll.EtaleFundamentalGroups.Purity.CechLocalizationDegreeZero
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroCoefficients
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDimensionShift
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionQuotient
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionInjectivePresentation
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Čech cohomology and derived local cohomology

The natural degree-zero inclusion identifies Čech cohomology with ideal
power torsion. This is first checked on injectives using the actual
contraction, then descended along an injective presentation by exactness.
The coefficient long exact sequences give the comparison in positive
degrees by dimension shifting.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

private abbrev cechCoefficients (xs : List R) (M : ModuleCat.{u} R) :=
  ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (cechLocalizationComplex xs)

private theorem cechHomologyZero_range_injective
    (xs : List R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    LinearMap.range (cechHomologyZeroToModule xs M).hom =
      Ideal.primaryComponent M (Ideal.ofList xs) := by
  let T := ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList xs))
  let S := (CochainComplex.single₀ (ModuleCat.{u} R)).obj T
  let K := cechCoefficients xs M
  let e : HomotopyEquiv K S := cechInjectiveHomotopyEquiv xs M
  let b : K.homology 0 ⟶ M := cechHomologyZeroToModule xs M
  let h : T ≅ K.homology 0 :=
    (singleObjHomologySelfIso (ComplexShape.up ℕ) 0 T).symm ≪≫
      (e.toHomologyIso 0).symm
  have hinc : e.inv.f 0 ≫ (cechCoefficientZeroIso xs M).hom =
      ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList xs)).subtype :=
    cechInjectiveHomotopyEquiv_inv_f_zero xs M
  have heval : h.hom ≫ b =
      ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList xs)).subtype := by
    change (singleObjHomologySelfIso (ComplexShape.up ℕ) 0 T).inv ≫
      homologyMap e.inv 0 ≫ (CochainComplex.isoHomologyπ₀ K).inv ≫
        K.iCycles 0 ≫ (cechCoefficientZeroIso xs M).hom = _
    rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc, cyclesMap_i_assoc, hinc]
    change ((singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 T).inv ≫
      (CochainComplex.isoHomologyπ₀ S).hom) ≫ (CochainComplex.isoHomologyπ₀ S).inv ≫
        S.iCycles 0 ≫ _ = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    calc
      _ = ((singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 T).inv ≫ S.iCycles 0) ≫
          ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList xs)).subtype :=
        (Category.assoc _ _ _).symm
      _ = (singleObjXSelf (ComplexShape.up ℕ) 0 T).inv ≫
          ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList xs)).subtype :=
        congrArg (fun f : T ⟶ S.X 0 => f ≫
          ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList xs)).subtype)
          (singleObjCyclesSelfIso_inv_iCycles (ComplexShape.up ℕ) 0 T)
      _ = _ := Category.id_comp _
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := h.toLinearEquiv.surjective w
    have he : b (h.hom t) = (t : M) := ConcreteCategory.congr_hom heval t
    change b (h.hom t) ∈ _
    exact he.symm ▸ t.property
  · intro hz
    refine ⟨h.hom ⟨z, hz⟩, ?_⟩
    exact ConcreteCategory.congr_hom heval ⟨z, hz⟩

/-- The natural degree-zero Čech embedding has exactly the expected
ideal-power torsion image for every coefficient module. -/
theorem cechHomologyZeroToModule_range (xs : List R) (M : ModuleCat.{u} R) :
    LinearMap.range (cechHomologyZeroToModule xs M).hom =
      Ideal.primaryComponent M (Ideal.ofList xs) := by
  let E : ModuleCat.{u} R := Injective.under M
  let u : M ⟶ E := Injective.ι M
  have hu : Function.Injective u :=
    (ModuleCat.mono_iff_injective u).mp inferInstance
  let : Module.Injective R E :=
    (Module.injective_iff_injective_object R E).mpr
      (inferInstance : CategoryTheory.Injective E)
  let C := tensorComplexCoefficientFunctor (cechLocalizationComplex xs)
  let S := injectivePresentationShortComplex u.hom
  have hS : S.ShortExact := injectivePresentationShortComplex_shortExact u.hom hu
  let (n : ℕ) : Module.Flat R ((cechLocalizationComplex xs).X n) :=
    cechLocalizationComplex_flat_X xs n
  have hCS := tensorComplexCoefficientFunctor_shortExact (cechLocalizationComplex xs) hS
  have hexact : Function.Exact (homologyMap (C.map S.f) 0).hom
      (homologyMap (C.map S.g) 0).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hCS.homology_exact₂ 0)
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hE : u ((cechHomologyZeroToModule xs M) w) ∈
        Ideal.primaryComponent E (Ideal.ofList xs) := by
      rw [← cechHomologyZero_range_injective xs E]
      exact ⟨homologyMap (C.map u) 0 w,
        ConcreteCategory.congr_hom (cechHomologyZeroToModule_naturality xs u) w⟩
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (M := E)
      (I := Ideal.ofList xs) (u ((cechHomologyZeroToModule xs M) w))).mp hE
    apply (Ideal.primaryComponent_mem (M := M) (I := Ideal.ofList xs) _).mpr
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    apply hu
    rw [map_smul, map_zero]
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := E)
      (s := (((Ideal.ofList xs) ^ n : Ideal R) : Set R))
      (u ((cechHomologyZeroToModule xs M) w))).mp hn a
  · intro hz
    have hzE : u z ∈ LinearMap.range (cechHomologyZeroToModule xs E).hom := by
      rw [cechHomologyZero_range_injective xs E]
      exact Ideal.primaryComponent_map_mem (Ideal.ofList xs) u.hom ⟨z, hz⟩
    obtain ⟨w, hw⟩ := hzE
    have hzero : homologyMap (C.map S.g) 0 w = 0 := by
      apply (ModuleCat.mono_iff_injective (cechHomologyZeroToModule xs S.X₃)).mp inferInstance
      calc
        (cechHomologyZeroToModule xs S.X₃) (homologyMap (C.map S.g) 0 w) =
            S.g ((cechHomologyZeroToModule xs E) w) :=
          ConcreteCategory.congr_hom (cechHomologyZeroToModule_naturality xs S.g) w
        _ = S.g (u z) := congrArg S.g hw
        _ = 0 := ConcreteCategory.congr_hom S.zero z
        _ = (cechHomologyZeroToModule xs S.X₃) 0 :=
          (cechHomologyZeroToModule xs S.X₃).hom.map_zero.symm
    obtain ⟨v, hv⟩ := (hexact w).mp hzero
    refine ⟨v, hu ?_⟩
    calc
      u ((cechHomologyZeroToModule xs M) v) =
          (cechHomologyZeroToModule xs E) (homologyMap (C.map u) 0 v) :=
        (ConcreteCategory.congr_hom (cechHomologyZeroToModule_naturality xs u) v).symm
      _ = (cechHomologyZeroToModule xs E) w := congrArg (cechHomologyZeroToModule xs E) hv
      _ = u z := hw

private def cechHomologyZeroEquivPrimaryComponent (xs : List R) (M : ModuleCat.{u} R) :
    (cechCoefficients xs M).homology 0 ≃ₗ[R]
      Ideal.primaryComponent M (Ideal.ofList xs) := by
  let f : (cechCoefficients xs M).homology 0 →ₗ[R]
      Ideal.primaryComponent M (Ideal.ofList xs) :=
    (cechHomologyZeroToModule xs M).hom.codRestrict _ (fun w => by
      rw [← cechHomologyZeroToModule_range xs M]
      exact LinearMap.mem_range_self _ w)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro w v h
    exact (ModuleCat.mono_iff_injective (cechHomologyZeroToModule xs M)).mp inferInstance
      (congrArg (fun t : Ideal.primaryComponent M (Ideal.ofList xs) => (t : M)) h)
  · intro z
    have hz : (z : M) ∈ LinearMap.range (cechHomologyZeroToModule xs M).hom := by
      rw [cechHomologyZeroToModule_range xs M]
      exact z.property
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩

private def cechLocalCohomologyZeroEquiv (xs : List R) (M : ModuleCat.{u} R) :
    (cechCoefficients xs M).homology 0 ≃ₗ[R]
      derivedLocalCohomologyModule (Ideal.ofList xs) M 0 :=
  (cechHomologyZeroEquivPrimaryComponent xs M).trans
    (derivedLocalCohomologyZeroEquivPrimaryComponent (Ideal.ofList xs) M).symm

private theorem cechLocalCohomologyZeroEquiv_eval (xs : List R) (M : ModuleCat.{u} R)
    (z : (cechCoefficients xs M).homology 0) :
    derivedLocalCohomologyZeroToModule (Ideal.ofList xs) M
      (cechLocalCohomologyZeroEquiv xs M z) = (cechHomologyZeroToModule xs M) z := by
  let e := derivedLocalCohomologyZeroEquivPrimaryComponent (Ideal.ofList xs) M
  calc
    derivedLocalCohomologyZeroToModule (Ideal.ofList xs) M
        (cechLocalCohomologyZeroEquiv xs M z) =
      (e (cechLocalCohomologyZeroEquiv xs M z) : M) :=
        (derivedLocalCohomologyZeroEquivPrimaryComponent_apply_val
          (Ideal.ofList xs) M _).symm
    _ = (cechHomologyZeroEquivPrimaryComponent xs M z : M) :=
      congrArg (fun t : Ideal.primaryComponent M (Ideal.ofList xs) => (t : M))
        (e.apply_symm_apply (cechHomologyZeroEquivPrimaryComponent xs M z))
    _ = (cechHomologyZeroToModule xs M) z := rfl

private theorem cechLocalCohomologyZeroEquiv_secondMap
    (xs : List R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (cechLocalCohomologyZeroEquiv xs S.X₃).toLinearMap.comp
      (homologyMap ((tensorComplexCoefficientFunctor (cechLocalizationComplex xs)).map S.g) 0).hom =
      (derivedLocalCohomologyModuleCoefficientsSecondMap (Ideal.ofList xs) hS 0).comp
        (cechLocalCohomologyZeroEquiv xs S.X₂).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply derivedLocalCohomologyZeroToModule_injective (Ideal.ofList xs) S.X₃
  calc
    derivedLocalCohomologyZeroToModule (Ideal.ofList xs) S.X₃
        (cechLocalCohomologyZeroEquiv xs S.X₃
          (homologyMap
            ((tensorComplexCoefficientFunctor (cechLocalizationComplex xs)).map S.g) 0 z)) =
      (cechHomologyZeroToModule xs S.X₃)
        (homologyMap
          ((tensorComplexCoefficientFunctor (cechLocalizationComplex xs)).map S.g) 0 z) :=
      cechLocalCohomologyZeroEquiv_eval xs S.X₃ _
    _ = S.g ((cechHomologyZeroToModule xs S.X₂) z) :=
      ConcreteCategory.congr_hom (cechHomologyZeroToModule_naturality xs S.g) z
    _ = S.g (derivedLocalCohomologyZeroToModule (Ideal.ofList xs) S.X₂
        (cechLocalCohomologyZeroEquiv xs S.X₂ z)) :=
      congrArg S.g (cechLocalCohomologyZeroEquiv_eval xs S.X₂ z).symm
    _ = derivedLocalCohomologyZeroToModule (Ideal.ofList xs) S.X₃
        (derivedLocalCohomologyModuleCoefficientsSecondMap (Ideal.ofList xs) hS 0
          (cechLocalCohomologyZeroEquiv xs S.X₂ z)) :=
      (DFunLike.congr_fun (derivedLocalCohomologyZeroToModule_comp_secondMap
        (Ideal.ofList xs) hS) (cechLocalCohomologyZeroEquiv xs S.X₂ z)).symm

private theorem cechCoefficients_isZero_homology_succ
    (xs : List R) (M : ModuleCat.{u} R) [Module.Injective R M] (n : ℕ) :
    IsZero ((cechCoefficients xs M).homology (n + 1)) :=
  IsZero.of_iso
    (isZero_single_obj_homology (ComplexShape.up ℕ) 0
      (ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList xs))) (n + 1) (by omega))
    ((cechInjectiveHomotopyEquiv xs M).toHomologyIso (n + 1))

private def cechLocalCohomologyOneEquiv
    (xs : List R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Injective R S.X₂] :
    (cechCoefficients xs S.X₁).homology 1 ≃ₗ[R]
      derivedLocalCohomologyModule (Ideal.ofList xs) S.X₁ 1 := by
  let C := tensorComplexCoefficientFunctor (cechLocalizationComplex xs)
  letI (n : ℕ) : Module.Flat R ((cechLocalizationComplex xs).X n) :=
    cechLocalizationComplex_flat_X xs n
  have hCS := tensorComplexCoefficientFunctor_shortExact (cechLocalizationComplex xs) hS
  let f := (homologyMap (C.map S.g) 0).hom
  let g := (hCS.δ 0 1 rfl).hom
  have hexact : Function.Exact f g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hCS.homology_exact₃ 0 1 rfl)
  have hsurj : Function.Surjective g :=
    (ModuleCat.epi_iff_surjective (hCS.δ 0 1 rfl)).mp
      (hCS.epi_δ 0 1 rfl (cechCoefficients_isZero_homology_succ xs S.X₂ 0))
  let f' := derivedLocalCohomologyModuleCoefficientsSecondMap (Ideal.ofList xs) hS 0
  let g' := derivedLocalCohomologyModuleCoefficientsConnectingMap (Ideal.ofList xs) hS 0
  have hexact' : Function.Exact f' g' :=
    derivedLocalCohomologyModuleCoefficients_beforeConnecting_exact (Ideal.ofList xs) hS 0
  have hsurj' : Function.Surjective g' :=
    derivedLocalCohomologyConnecting_surjective_of_injective (Ideal.ofList xs) hS 0
  let e₂ := cechLocalCohomologyZeroEquiv xs S.X₂
  let e₃ := cechLocalCohomologyZeroEquiv xs S.X₃
  have hrange : (LinearMap.range f).map e₃.toLinearMap = LinearMap.range f' := by
    calc
      (LinearMap.range f).map e₃.toLinearMap = LinearMap.range (e₃.toLinearMap.comp f) :=
        (LinearMap.range_comp f e₃.toLinearMap).symm
      _ = LinearMap.range (f'.comp e₂.toLinearMap) :=
        congrArg LinearMap.range (cechLocalCohomologyZeroEquiv_secondMap xs hS)
      _ = LinearMap.range f' := LinearMap.range_comp_of_range_eq_top f'
        (LinearMap.range_eq_top.mpr e₂.surjective)
  exact hexact.linearEquivOfSurjective hsurj |>.symm.trans
    ((Submodule.Quotient.equiv (LinearMap.range f) (LinearMap.range f') e₃ hrange).trans
      (hexact'.linearEquivOfSurjective hsurj'))

/-- The actual bounded Čech complex computes derived local cohomology,
with a linear comparison in every degree and for every coefficient module. -/
def cechLocalCohomologyLinearEquiv (xs : List R) (M : ModuleCat.{u} R) (n : ℕ) :
    ((((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cechLocalizationComplex xs)).homology n) ≃ₗ[R]
        derivedLocalCohomologyModule (Ideal.ofList xs) M n := by
  induction n generalizing M with
  | zero => exact cechLocalCohomologyZeroEquiv xs M
  | succ n ih =>
    let E : ModuleCat.{u} R := Injective.under M
    let u : M ⟶ E := Injective.ι M
    have hu : Function.Injective u :=
      (ModuleCat.mono_iff_injective u).mp inferInstance
    let S := injectivePresentationShortComplex u.hom
    have hS : S.ShortExact := injectivePresentationShortComplex_shortExact u.hom hu
    letI : Module.Injective R S.X₂ :=
      (Module.injective_iff_injective_object R E).mpr
        (inferInstance : CategoryTheory.Injective E)
    cases n with
    | zero => exact cechLocalCohomologyOneEquiv xs hS
    | succ n =>
      letI (k : ℕ) : Module.Flat R ((cechLocalizationComplex xs).X k) :=
        cechLocalizationComplex_flat_X xs k
      have hCS := tensorComplexCoefficientFunctor_shortExact (cechLocalizationComplex xs) hS
      let eC := hCS.δIso (n + 1) (n + 1 + 1) rfl
        (cechCoefficients_isZero_homology_succ xs S.X₂ n)
        (cechCoefficients_isZero_homology_succ xs S.X₂ (n + 1))
      let eL := LinearEquiv.ofBijective
        (derivedLocalCohomologyModuleCoefficientsConnectingMap (Ideal.ofList xs) hS (n + 1))
        (derivedLocalCohomologyConnecting_bijective_succ_of_injective (Ideal.ofList xs) hS n)
      exact eC.symm.toLinearEquiv.trans ((ih S.X₃).trans eL)

end EtaleFundamentalGroups.Purity

end
