/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionQuotient
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Degree zero of the torsion complex of an injective resolution

The inclusion of a module into its injective resolution identifies its
power-torsion submodule with the degree-zero torsion cycles. Exactness
supplies the preimage of a cycle; injectivity of the inclusion transports
its annihilating power back to the original module. This identifies
degree-zero homology with the existing local-cohomology colimit.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

private def idealPowerTorsionResolutionCyclesZeroEquiv
    (I : Ideal R) {M : ModuleCat.{u} R} (J : InjectiveResolution M) :
    Ideal.primaryComponent M I ≃ₗ[R]
      LinearMap.ker ((derivedLocalCohomologyInjectiveComplex I J).d 0 1).hom := by
  let K : CochainComplex (ModuleCat.{u} R) ℕ := derivedLocalCohomologyInjectiveComplex I J
  have hι : Function.Injective (J.ι.f 0) :=
    (ModuleCat.mono_iff_injective (J.ι.f 0)).mp inferInstance
  let f : Ideal.primaryComponent M I →ₗ[R] LinearMap.ker (K.d 0 1).hom :=
    LinearMap.codRestrict (LinearMap.ker (K.d 0 1).hom)
      ((idealPowerTorsionFunctor I).map (J.ι.f 0)).hom (fun z => by
        apply Subtype.ext
        change J.cocomplex.d 0 1 (J.ι.f 0 (z : M)) = 0
        exact ConcreteCategory.congr_hom J.ι_f_zero_comp_complex_d (z : M))
  apply LinearEquiv.ofBijective f
  constructor
  · intro z w h
    apply Subtype.ext
    apply hι
    exact congrArg (fun a : LinearMap.ker (K.d 0 1).hom =>
      ((show Ideal.primaryComponent (J.cocomplex.X 0) I from
        (a : K.X 0)) : J.cocomplex.X 0)) h
  · intro z
    have hdz : K.d 0 1 (z : K.X 0) = 0 := z.property
    have hdz' : J.cocomplex.d 0 1
        ((show Ideal.primaryComponent (J.cocomplex.X 0) I from
          (z : K.X 0)) : J.cocomplex.X 0) = 0 :=
      congrArg (fun a : K.X 1 =>
        ((show Ideal.primaryComponent (J.cocomplex.X 1) I from a) :
          J.cocomplex.X 1)) hdz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp J.exact₀
      ((show Ideal.primaryComponent (J.cocomplex.X 0) I from
        (z : K.X 0)) : J.cocomplex.X 0) hdz'
    let yM : M := y
    have hyM : (J.ι.f 0).hom yM =
        ((show Ideal.primaryComponent (J.cocomplex.X 0) I from
          (z : K.X 0)) : J.cocomplex.X 0) := hy
    have hyT : yM ∈ Ideal.primaryComponent M I := by
      obtain ⟨n, hn⟩ :=
        (Ideal.primaryComponent_mem (M := J.cocomplex.X 0) (I := I)
          ((show Ideal.primaryComponent (J.cocomplex.X 0) I from
            (z : K.X 0)) : J.cocomplex.X 0)).mp (z : K.X 0).property
      apply (Ideal.primaryComponent_mem (M := M) (I := I) yM).mpr
      refine ⟨n, ?_⟩
      apply (Submodule.mem_torsionBySet_iff (R := R) (M := M)
        (s := ((I ^ n : Ideal R) : Set R)) yM).mpr
      intro a
      change (a : R) • y = 0
      apply hι
      calc
        (J.ι.f 0).hom ((a : R) • y) =
            (a : R) • (J.ι.f 0).hom y := map_smul (J.ι.f 0).hom (a : R) y
        _ = 0 := by
          rw [hy]
          exact (Submodule.mem_torsionBySet_iff (R := R) (M := J.cocomplex.X 0)
            (s := ((I ^ n : Ideal R) : Set R))
            ((show Ideal.primaryComponent (J.cocomplex.X 0) I from
              (z : K.X 0)) : J.cocomplex.X 0)).mp hn a
        _ = (J.ι.f 0).hom 0 := (map_zero (J.ι.f 0).hom).symm
    refine ⟨⟨yM, hyT⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hyM

/-- The degree-zero homology of the torsion injective-resolution complex
is the previously constructed degree-zero local-cohomology module. -/
def derivedLocalCohomologyInjectiveComplexHomologyIsoZero
    (I : Ideal R) {M : ModuleCat.{u} R} (J : InjectiveResolution M) :
    (derivedLocalCohomologyInjectiveComplex I J).homology 0 ≅
      derivedLocalCohomologyModule I M 0 :=
  let K := derivedLocalCohomologyInjectiveComplex I J
  K.isoHomologyπ₀.symm ≪≫
    K.cyclesIsoSc' 0 0 1
      (ComplexShape.prev_eq_self' _ 0 (fun n hn => Nat.succ_ne_zero n hn))
      (ComplexShape.next_eq' _ rfl) ≪≫
    (K.sc' 0 0 1).moduleCatCyclesIso ≪≫
    (idealPowerTorsionResolutionCyclesZeroEquiv I J).symm.toModuleIso ≪≫
    (derivedLocalCohomologyZeroEquivPrimaryComponent I M).symm.toModuleIso

end EtaleFundamentalGroups.Purity

end
