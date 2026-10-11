/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionInjective
import Nyll.EtaleFundamentalGroups.Purity.InjectiveModuleLocalization
import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationComplex
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The principal localization complex of an injective module

The localization sequence splits because its kernel is an injective
primary component. In particular the localized term is injective. The
actual inclusion of the primary component in degree zero is a
quasi-isomorphism between complexes of injectives, hence a homotopy
equivalence.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

private theorem primaryComponent_localization_comp_eq_zero
    (x : R) (M : ModuleCat.{u} R) :
    (LocalizedModule.mkLinearMap (Submonoid.powers x) M).comp
      (Ideal.primaryComponent M (Ideal.span {x})).subtype = 0 := by
  apply LinearMap.ext
  intro z
  apply (ker_localizedModule_mkLinearMap_powers M x).symm.le
  exact z.property

/-- The principal primary component, the module, and its localization. -/
def principalLocalizationSequence (x : R) (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (Ideal.primaryComponent M (Ideal.span {x})).subtype
    (LocalizedModule.mkLinearMap (Submonoid.powers x) M)
    (primaryComponent_localization_comp_eq_zero x M)

theorem principalLocalizationSequence_shortExact
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    (principalLocalizationSequence x M).ShortExact := by
  apply ModuleCat.shortComplex_shortExact _ _
    (Ideal.primaryComponent M (Ideal.span {x})).subtype_injective
    (localizedModule_mkLinearMap_surjective_of_injective M (Submonoid.powers x))
  rw [LinearMap.exact_iff]
  change LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers x) M) =
    LinearMap.range (Ideal.primaryComponent M (Ideal.span {x})).subtype
  rw [Submodule.range_subtype, ker_localizedModule_mkLinearMap_powers]

/-- Localization of an injective module at one element is injective,
as a retract of the original module. -/
theorem moduleInjective_localizedModule_powers
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    Module.Injective R (LocalizedModule (Submonoid.powers x) M) := by
  let S := principalLocalizationSequence x M
  let : Module.Injective R S.X₁ := moduleInjective_primaryComponent (Ideal.span {x}) M
  let : CategoryTheory.Injective S.X₁ := Module.injective_object_of_injective_module R S.X₁
  let : CategoryTheory.Injective S.X₂ := Module.injective_object_of_injective_module R M
  let s := (principalLocalizationSequence_shortExact x M).splittingOfInjective
  let h : Retract S.X₃ S.X₂ := ⟨s.s, S.g, s.s_g⟩
  let : CategoryTheory.Injective S.X₃ := h.injective
  exact Module.injective_module_of_injective_object R S.X₃

/-- The inclusion of principal power torsion into the localization
complex, concentrated in degree zero at the source. -/
def principalLocalizationInclusion (x : R) (M : ModuleCat.{u} R) :
    (CochainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))) ⟶
      principalLocalizationComplex x M :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.span {x})).subtype,
      ModuleCat.hom_ext (primaryComponent_localization_comp_eq_zero x M)⟩

private theorem principalLocalizationInclusion_quasiIsoAt_zero
    (x : R) (M : ModuleCat.{u} R) :
    QuasiIsoAt (principalLocalizationInclusion x M) 0 := by
  let C := principalLocalizationComplex x M
  let S := C.sc' 0 0 1
  let f := principalLocalizationInclusion x M
  apply (quasiIsoAt_iff' f 0 0 1
    CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)).mpr
  apply (ShortComplex.quasiIso_iff_isIso_liftCycles _ rfl rfl ?_).mpr
  · let T : Submodule R S.X₂ := Ideal.primaryComponent S.X₂ (Ideal.span {x})
    have hT : T = LinearMap.ker S.g.hom :=
      (principalLocalizationComplex_ker_d_zero x M).symm
    let k : ModuleCat.of R T ⟶ S.X₂ := ModuleCat.ofHom T.subtype
    have hk : k ≫ S.g = 0 :=
      ModuleCat.hom_ext (primaryComponent_localization_comp_eq_zero x M)
    let e : ModuleCat.of R T ≅ S.cycles :=
      (LinearEquiv.ofEq T (LinearMap.ker S.g.hom) hT).toModuleIso ≪≫
        S.moduleCatCyclesIso.symm
    have he : S.liftCycles k hk = e.hom := by
      apply (cancel_mono S.iCycles).mp
      refine (S.liftCycles_i k hk).trans ?_
      symm
      change ((LinearEquiv.ofEq T (LinearMap.ker S.g.hom) hT).toModuleIso.hom ≫
        S.moduleCatCyclesIso.inv) ≫ S.iCycles = k
      calc
        _ = (LinearEquiv.ofEq T (LinearMap.ker S.g.hom) hT).toModuleIso.hom ≫
            (S.moduleCatCyclesIso.inv ≫ S.iCycles) := Category.assoc _ _ _
        _ = (LinearEquiv.ofEq T (LinearMap.ker S.g.hom) hT).toModuleIso.hom ≫
            S.moduleCatLeftHomologyData.i := congrArg
              (fun g : S.moduleCatLeftHomologyData.K ⟶ S.X₂ =>
                (LinearEquiv.ofEq T (LinearMap.ker S.g.hom) hT).toModuleIso.hom ≫ g)
              S.moduleCatCyclesIso_inv_iCycles
        _ = k := rfl
    change IsIso (S.liftCycles k hk)
    rw [he]
    infer_instance
  · exact C.shape 0 0 (by change ¬ ((0 : ℕ) + 1 = 0); omega)

/-- The torsion inclusion is a quasi-isomorphism for injective
coefficients over a Noetherian ring. -/
theorem principalLocalizationInclusion_quasiIso
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    QuasiIso (principalLocalizationInclusion x M) := by
  constructor
  intro n
  cases n with
  | zero => exact principalLocalizationInclusion_quasiIsoAt_zero x M
  | succ n =>
      apply (quasiIsoAt_iff_exactAt _ _ ?_).mpr
        (principalLocalizationComplex_exactAt_succ x M n)
      apply HomologicalComplex.ExactAt.of_isZero
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- The principal localization complex of an injective module is
homotopy equivalent to its primary component in degree zero. -/
private def principalLocalizationHomotopyData
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    {e : HomotopyEquiv
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))))
      (principalLocalizationComplex x M) // e.hom = principalLocalizationInclusion x M} := by
  letI : Module.Injective R (Ideal.primaryComponent M (Ideal.span {x})) :=
    moduleInjective_primaryComponent (Ideal.span {x}) M
  letI : CategoryTheory.Injective (ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))) :=
    Module.injective_object_of_injective_module R _
  letI : ∀ n, CategoryTheory.Injective
      (((CochainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x})))).X n) := by
    intro n
    cases n with
    | zero => exact inferInstanceAs (CategoryTheory.Injective
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))))
    | succ n => exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).injective
  letI : ∀ n, CategoryTheory.Injective ((principalLocalizationComplex x M).X n) := by
    intro n
    cases n with
    | zero => exact Module.injective_object_of_injective_module R M
    | succ n =>
      cases n with
      | zero =>
          let : Module.Injective R (LocalizedModule (Submonoid.powers x) M) :=
            moduleInjective_localizedModule_powers x M
          exact Module.injective_object_of_injective_module R _
      | succ n => exact (principalLocalizationComplex_isZero_X x M (n + 1 + 1) (by omega)).injective
  have h := (CochainComplex.quasiIso_iff_of_injective
    (principalLocalizationInclusion x M)).mp (principalLocalizationInclusion_quasiIso x M)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- The principal localization contraction with its specified forward map. -/
def principalLocalizationHomotopyEquiv
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    HomotopyEquiv
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))))
      (principalLocalizationComplex x M) :=
  (principalLocalizationHomotopyData x M).val

/-- The forward map of the contraction is the specified torsion inclusion. -/
theorem principalLocalizationHomotopyEquiv_hom
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    (principalLocalizationHomotopyEquiv x M).hom = principalLocalizationInclusion x M := by
  exact (principalLocalizationHomotopyData x M).property

/-- In degree zero the specified forward map is the inclusion of torsion. -/
theorem principalLocalizationHomotopyEquiv_hom_f_zero
    [IsNoetherianRing R] (x : R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    (principalLocalizationHomotopyEquiv x M).hom.f 0 =
      ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.span {x})).subtype := by
  exact (congrArg (fun f => f.f 0) (principalLocalizationHomotopyEquiv_hom x M)).trans
    (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := principalLocalizationComplex x M)
      (X := ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x})))
      (ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.span {x})).subtype)
      (ModuleCat.hom_ext (primaryComponent_localization_comp_eq_zero x M)))

end EtaleFundamentalGroups.Purity

end
