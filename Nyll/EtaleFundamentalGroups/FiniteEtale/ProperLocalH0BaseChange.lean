/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.LocalKernelBaseChange
import Nyll.EtaleFundamentalGroups.FiniteEtale.CechKernelBaseChangeSurjectivity
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperEtaleClosedFiberSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperGeometricallyReducedSections
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection

/-!
# Proper local H⁰ and arbitrary base change

For a proper flat geometrically reduced family over a Noetherian local ring,
the actual closed-fibre section map is surjective. Its Čech comparison transfers
this surjectivity to the finite free cohomology model. The local kernel theorem
then proves finite projectivity and arbitrary base change for the original H⁰.
The base ring need not be reduced.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.OModulePresheaf

universe u

open AlgebraicCurves.Cohomology.Sheaves.Proofs
  OModulePresheaf_projective_H0_and_bijective_kerBaseChangeHom_of_isReduced_of_finrank_eq
  P2mReducedBaseChangeH0

private theorem finite_projective_H0_of_residue_surjective
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover)
    (hsurj : Function.Surjective
      (TwoChartCech.kerBaseChangeHom ((ofModules f M).d 𝒰 0)
        (IsLocalRing.ResidueField R))) :
    Module.Finite R ((ofModules f M).H0 𝒰) ∧
      Module.Projective R ((ofModules f M).H0 𝒰) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom ((ofModules f M).d 𝒰 0) A) := by
  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    exists_twoTermComplex_kerMapBaseChange_bijective_ofModules f M htriv 𝒰
  let d := (ofModules f M).d 𝒰 0
  have hMap := kerMap_bijective G.d d ι0 ι1 comm (hbij R)
  let e := LinearEquiv.ofBijective (TwoChartCech.kerMap G.d d ι0 ι1 comm) hMap
  let k := IsLocalRing.ResidueField R
  let ek := e.baseChange R k _ _
  have hG : Function.Surjective (TwoChartCech.kerBaseChangeHom G.d k) := by
    intro z
    obtain ⟨y, hy⟩ := hsurj (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm k z)
    obtain ⟨x, hx⟩ := ek.surjective y
    refine ⟨x, (hbij k).1 ?_⟩
    rw [kerMapBaseChange_kerBaseChangeHom]
    exact (congrArg (TwoChartCech.kerBaseChangeHom d k) hx).trans hy
  obtain ⟨hfin, hproj, hbc⟩ :=
    TwoChartCech.finite_projective_ker_and_bijective_baseChange_of_residue_surjective G.d hG
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun A _ _ => ?_⟩
  exact bijective_kerBaseChangeHom_of_transfer G.d d ι0 ι1 comm A
    (hbc A) (hbij A) hMap

/-- Étaleness of the actual closed-fibre section algebra makes structure-sheaf
H⁰ finite projective and compatible with every scalar extension. The total
family need not have geometrically reduced fibres away from the closed point. -/
theorem finite_projective_H0_and_bijective_baseChange_of_proper_flat_of_etale_closedFiber
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] (𝒰 : X.OrderedAffineCover)
    (hEtaleFiber : (pullback.snd f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop.hom.Etale) :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    Module.Finite R ((ofModules f M).H0 𝒰) ∧
      Module.Projective R ((ofModules f M).H0 𝒰) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom ((ofModules f M).d 𝒰 0) A) := by
  intro M
  let k := IsLocalRing.ResidueField R
  let q : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R k))
  let p := pullback.fst f q
  let fₖ := pullback.snd f q
  let scalar : Algebra k Γ(pullback f q, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fₖ.appTop).hom.toAlgebra
  have hEtale : Algebra.Etale k Γ(pullback f q, ⊤) := by
    exact (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv fₖ.appTop).mpr hEtaleFiber
  have hs : Function.Surjective p.appTop :=
    surjective_closedFiber_appTop_of_isProper_of_etale f hEtale
  have hUnit : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) := by
    let e := Scheme.Modules.pullbackUnitIso p
    intro z
    obtain ⟨s, hs⟩ := hs (e.hom.app ⊤ z)
    refine ⟨Scheme.Modules.toUnitSection ⊤ s, ?_⟩
    have hleft (a : Γ((Scheme.Modules.pullback p).obj M, ⊤)) :
        e.inv.app ⊤ (e.hom.app ⊤ a) = a :=
      congrArg (fun k : (Scheme.Modules.pullback p).obj M ⟶
          (Scheme.Modules.pullback p).obj M => k.val.app (Opposite.op ⊤) a) e.hom_inv_id
    apply (show Function.LeftInverse (e.inv.app ⊤) (e.hom.app ⊤) from hleft).injective
    exact (Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
      p ⊤ s).trans hs
  have htriv := (Scheme.Modules.isInvertible_unit X).exists_trivialization
  have hk := surjective_kerBaseChangeHom_of_surjective_pullbackUnit f M 𝒰 htriv k hUnit
  exact finite_projective_H0_of_residue_surjective f M htriv 𝒰 hk

/-- The actual structure-sheaf H⁰ of a proper flat geometrically reduced family
over a Noetherian local ring is finite projective and its canonical kernel
comparison is bijective after every scalar extension. -/
theorem finite_projective_H0_and_bijective_baseChange_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [GeometricallyReduced f] (𝒰 : X.OrderedAffineCover) :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    Module.Finite R ((ofModules f M).H0 𝒰) ∧
      Module.Projective R ((ofModules f M).H0 𝒰) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom ((ofModules f M).d 𝒰 0) A) := by
  exact finite_projective_H0_and_bijective_baseChange_of_proper_flat_of_etale_closedFiber f 𝒰
    (finite_etale_appTop_of_isProper_of_geometricallyReduced_overField
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).2

end AlgebraicGeometry.OModulePresheaf
