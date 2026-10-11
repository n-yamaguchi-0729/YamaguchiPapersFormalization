/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ChosenLocalization.Core

/-!
# Boundary Away through a finitely presented formally-etale extension

The existing finite-extension transport derives finite presentation from
module finiteness over a Noetherian base.  Maximal-adic completions used by
the one-point inertia construction do not currently carry a global
`IsNoetherianRing` instance.  This file records the exact replacement needed
there: finite presentation of the final chosen factor is supplied directly.

The proof keeps the literal composite away map.  Its formal etaleness is
obtained by localizing the formally-etale upper map; its finite presentation
is the base change of the supplied finite presentation along the away
localization.  No Noetherian hypothesis is used.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uC uD

/-- A finitely presented formally-etale extension of an algebra already
etale away from `f` remains etale for the literal composite away map.

This is the Noetherian-free form of
`localization_awayMap_etale_of_finite_formallyEtale_extension`.  In the
completion application, finite presentation of the chosen factor is
constructed from finite projectivity over the completed root cover and the
finite-free root cover over the completed prefix. -/
theorem
    localization_awayMap_etale_of_finitePresentation_formallyEtale_extension
    {A : Type uA} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra C D] [Algebra A D]
    [IsScalarTower A C D]
    [Module.FinitePresentation A D]
    [Algebra.FormallyEtale C D]
    (f : A)
    (hAway : (Localization.awayMap (algebraMap A C) f).Etale) :
    (Localization.awayMap (algebraMap A D) f).Etale := by
  let fC : C := algebraMap A C f
  let fD : D := algebraMap A D f
  let S := Localization.Away f
  let T := Localization.Away fC
  let U := Localization.Away fD
  let mapST : S →+* T := Localization.awayMap (algebraMap A C) f
  let mapCDU : C →+* U := algebraMap C U
  have hfCUnit : IsUnit (mapCDU fC) := by
    change IsUnit (algebraMap D U (algebraMap C D (algebraMap A C f)))
    rw [← IsScalarTower.algebraMap_apply A C D f]
    exact IsLocalization.Away.algebraMap_isUnit fD
  let mapTU : T →+* U := Localization.awayLift mapCDU fC hfCUnit
  let mapSU : S →+* U := Localization.awayMap (algebraMap A D) f
  let : Algebra S T := mapST.toAlgebra
  let : Algebra T U := mapTU.toAlgebra
  let : IsScalarTower C T U :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change mapCDU c = mapTU (algebraMap C T c)
      simp [mapTU]
  let : IsLocalization
      ((Submonoid.powers fC).map (algebraMap C D)) U := by
    rw [Submonoid.map_powers, show algebraMap C D fC = fD by
      exact (IsScalarTower.algebraMap_apply A C D f).symm]
    infer_instance
  let : Algebra.FormallyEtale T U :=
    Algebra.FormallyEtale.localization_map
      (R := C) (S := D) (Rₘ := T) (Sₘ := U)
      (Submonoid.powers fC)
  have hcomp : mapTU.comp mapST = mapSU := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    calc
      mapTU (mapST (algebraMap A S a)) =
          mapTU (algebraMap C T (algebraMap A C a)) := by
        rw [show mapST (algebraMap A S a) =
            algebraMap C T (algebraMap A C a) by
          simp [mapST, S, T, fC, IsLocalization.Away.map]]
      _ = mapCDU (algebraMap A C a) := by simp [mapTU]
      _ = algebraMap D U (algebraMap C D (algebraMap A C a)) := rfl
      _ = algebraMap D U (algebraMap A D a) := by
        rw [IsScalarTower.algebraMap_apply A C D a]
      _ = mapSU (algebraMap A S a) := by
        simp [mapSU, S, U, fD, IsLocalization.Away.map]
  let : Algebra S U := mapSU.toAlgebra
  let : IsScalarTower A S U :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A U a = mapSU (algebraMap A S a)
      simpa [mapSU, S, U, fD, IsLocalization.Away.map] using
        (IsScalarTower.algebraMap_apply A D U a)
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (DFunLike.congr_fun hcomp x).symm
  let : Algebra.Etale S T := hAway.toAlgebra
  let : Algebra.FormallyEtale S U :=
    Algebra.FormallyEtale.comp S T U
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers f)) U := by
    rw [Algebra.algebraMapSubmonoid_powers]
    change IsLocalization (Submonoid.powers fD) U
    infer_instance
  let : Algebra.IsPushout A D S U :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers f) S D U
  let : Algebra.IsPushout A S D U :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout A D S U)
  let eBase : S ⊗[A] D ≃ₐ[S] U :=
    Algebra.IsPushout.equiv A S D U
  let : Module.FinitePresentation S (S ⊗[A] D) := inferInstance
  let : Module.FinitePresentation S U :=
    Module.FinitePresentation.of_equiv eBase.toLinearEquiv
  let : Algebra.FinitePresentation S U :=
    Algebra.FinitePresentation.of_finitePresentation S U
  exact
    { formallyEtale := inferInstance
      finitePresentation := inferInstance }

end EtaleFundamentalGroups

end
