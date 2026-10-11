/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.ProC.MaximalQuotients.UniversalProperty
import ProCGroups.Topologies.QuotientMaps
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Instances.ZMod
import Mathlib.GroupTheory.Torsion
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Definition 6.1: orientations and formal Hilbert 90

This module constructs the twisted coefficient representations from a
continuous p-adic orientation and states formal Hilbert 90 using mathlib's
continuous first cohomology and its functorial reduction map. Explicit
continuous cocycles are retained only for the lifting statements; mathlib's
continuous low-degree API does not yet expose them as functions.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.ProC
open ProCGroups.FiniteStepSolvableQuotients
open scoped commutatorElement

universe u

/-- A continuous ℓ-orientation of a topological group. -/
abbrev Orientation (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] :=
  G →ₜ* (PadicInt ℓ)ˣ

/-- The orientation restricted to a subgroup and reduced modulo `ℓ ^ n`.
This is a homomorphism into units, so it gives the prescribed coefficient
action without a separately postulated action. -/
private def finiteOrientationUnits {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ) :
    H →* (ZMod (ℓ ^ n))ˣ :=
  (Units.map (PadicInt.toZModPow n).toMonoidHom).comp
    (θ.toMonoidHom.comp H.subtype)

/-- The actual discrete `ℤ/ℓⁿℤ` coefficient representation for the
orientation, viewed as an integer module so reduction has a common base ring. -/
noncomputable def finiteOrientationTopRep {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ) : TopRep.{u} ℤ H := by
  letI : ContinuousSMul ℤ (ULift.{u} (ZMod (ℓ ^ n))) :=
    ContinuousSMul.induced ULift.moduleEquiv.toLinearMap
  letI : ContinuousConstSMul (ZMod (ℓ ^ n))ˣ (ULift.{u} (ZMod (ℓ ^ n))) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  let action : (ZMod (ℓ ^ n))ˣ →*
      ULift.{u} (ZMod (ℓ ^ n)) ≃L[ℤ] ULift.{u} (ZMod (ℓ ^ n)) :=
    ContinuousLinearEquiv.smulLeft
  let forgetEquiv :
      (ULift.{u} (ZMod (ℓ ^ n)) ≃L[ℤ] ULift.{u} (ZMod (ℓ ^ n))) →*
        (ULift.{u} (ZMod (ℓ ^ n)) →L[ℤ] ULift.{u} (ZMod (ℓ ^ n))) :=
    { toFun := fun e => e.toContinuousLinearMap
      map_one' := by ext x; rfl
      map_mul' := by intro _ _; ext x; rfl }
  exact TopRep.of <| ContRepresentation.ofMonoidHom
    (forgetEquiv.comp (action.comp (finiteOrientationUnits θ H n)))

/-- The twisted coefficient action evaluated on a residue class. -/
theorem finiteOrientationTopRep_action {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ)
    (g : H) (a : ULift.{u} (ZMod (ℓ ^ n))) :
    (finiteOrientationTopRep θ H n).ρ g a =
      ULift.up (PadicInt.toZModPow n (θ (g : G) : PadicInt ℓ) * a.down) := rfl

/-- The natural reduction morphism between twisted coefficient objects. -/
noncomputable def finiteOrientationReduction {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ) (hn : 1 ≤ n) :
    TopRep.res (ContinuousMonoidHom.id H) (finiteOrientationTopRep θ H n) ⟶
      finiteOrientationTopRep θ H 1 := by
  letI : ContinuousSMul ℤ (ULift.{u} (ZMod (ℓ ^ n))) :=
    ContinuousSMul.induced ULift.moduleEquiv.toLinearMap
  letI : ContinuousSMul ℤ (ULift.{u} (ZMod (ℓ ^ 1))) :=
    ContinuousSMul.induced ULift.moduleEquiv.toLinearMap
  let f : ZMod (ℓ ^ n) →L[ℤ] ZMod (ℓ ^ 1) :=
    { toLinearMap :=
        (ZMod.castHom (pow_dvd_pow ℓ hn) (ZMod (ℓ ^ 1))).toAddMonoidHom.toIntLinearMap
      cont := continuous_of_discreteTopology }
  let red : ULift.{u} (ZMod (ℓ ^ n)) →L[ℤ] ULift.{u} (ZMod (ℓ ^ 1)) :=
    (ContinuousLinearEquiv.ulift (R₁ := ℤ) (M₁ := ZMod (ℓ ^ 1))).symm.toContinuousLinearMap.comp
      (f.comp (ContinuousLinearEquiv.ulift (R₁ := ℤ)
        (M₁ := ZMod (ℓ ^ n))).toContinuousLinearMap)
  refine TopRep.ofHom
    { toContinuousLinearMap := red
      isIntertwining' := ?_ }
  intro h
  ext x
  change (ZMod.castHom (pow_dvd_pow ℓ hn) (ZMod (ℓ ^ 1)))
      ((finiteOrientationUnits θ H n h : ZMod (ℓ ^ n)) * x.down) =
    (finiteOrientationUnits θ H 1 h : ZMod (ℓ ^ 1)) *
      (ZMod.castHom (pow_dvd_pow ℓ hn) (ZMod (ℓ ^ 1)) x.down)
  rw [map_mul]
  congr 1
  exact congrArg (fun g : PadicInt ℓ →+* ZMod (ℓ ^ 1) =>
    g (θ (h : G) : PadicInt ℓ))
    (PadicInt.zmod_cast_comp_toZModPow 1 n hn)

/-- A continuous crossed homomorphism with coefficients in `ℤ/ℓⁿℤ`,
twisted by the restriction of an orientation. -/
structure FiniteCocycle {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ) where
  /-- The cocycle values in the finite coefficient ring. -/
  toFun : H → ZMod (ℓ ^ n)
  /-- Continuity of the cocycle value function. -/
  continuous_toFun : Continuous toFun
  /-- The crossed-homomorphism identity for the reduced orientation action. -/
  cocycle : ∀ x y : H,
    toFun (x * y) = toFun x +
      PadicInt.toZModPow n (θ (x : G) : PadicInt ℓ) * toFun y

/-- A continuous crossed homomorphism with p-adic integer coefficients. -/
structure PadicCocycle {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G]
    (θ : Orientation ℓ G) (H : Subgroup G) where
  /-- The cocycle values in the p-adic coefficient ring. -/
  toFun : H → PadicInt ℓ
  /-- Continuity of the cocycle value function. -/
  continuous_toFun : Continuous toFun
  /-- The crossed-homomorphism identity for the orientation action. -/
  cocycle : ∀ x y : H,
    toFun (x * y) = toFun x + (θ (x : G) : PadicInt ℓ) * toFun y

/-- Surjectivity of the actual mathlib map on continuous first cohomology
induced by reduction of the twisted coefficient representation. -/
def HasH1ReductionSurjective {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Orientation ℓ G) (H : Subgroup G) (n : ℕ) (hn : 1 ≤ n) : Prop :=
  Function.Surjective
    (ContinuousCohomology.map.{0,u} (ContinuousMonoidHom.id H)
      (finiteOrientationReduction θ H n hn) 1).hom

/-- Formal Hilbert 90 at every open subgroup, for the given orientation. -/
def FormalHilbert90 {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Orientation ℓ G) : Prop :=
  ∀ H : OpenSubgroup G, ∀ n : ℕ, ∀ hn : 1 ≤ n,
    HasH1ReductionSurjective θ (H : Subgroup G) n hn

/-- The relative lifting condition `H_ℓ` used in the earlier manuscript. -/
def RelativeFormalHilbert90 {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) (θ : Orientation ℓ G) : Prop :=
  ∀ N : OpenNormalSubgroup G, D ≤ (N : Subgroup G) →
    ∀ n : ℕ, ∀ hn : 1 ≤ n,
      HasH1ReductionSurjective θ (N : Subgroup G) n hn

/-- The ℓ-primary factor of the topological abelianization of `D`.
For a profinite abelian group this maximal pro-ℓ quotient is its usual
ℓ-primary component. Mathlib's `CommGroup.primaryComponent` is instead
the subgroup of elements of finite ℓ-power order. -/
abbrev PrimaryAbelianization (ℓ : ℕ) [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) :=
  TopologicalAbelianization D ⧸
    proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
      (TopologicalAbelianization D)

/-- The ℓ-primary factor of the ambient group's abelianization. -/
abbrev GroupPrimaryAbelianization (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  TopologicalAbelianization G ⧸
    proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
      (TopologicalAbelianization G)

/-- The map on topological abelianizations induced by the actual inclusion
of `D` into `G`. -/
def abelianizationInclusion
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) :
    TopologicalAbelianization D →ₜ* TopologicalAbelianization G :=
  TopologicalAbelianization.map
    { toMonoidHom := D.subtype
      continuous_toFun := continuous_subtype_val }

/-- The natural homomorphism on ℓ-primary abelianizations induced by inclusion. -/
noncomputable def primaryInclusionMap (ℓ : ℕ) [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (D : Subgroup G) (hDclosed : IsClosed (D : Set G)) :
    PrimaryAbelianization ℓ D →ₜ* GroupPrimaryAbelianization ℓ G := by
  letI : CompactSpace D := hDclosed.isClosedEmbedding_subtypeVal.compactSpace
  let f := abelianizationInclusion D
  have hmap := map_proCResidualCore_le_of_continuousMonoidHom
    (C := ProCGroups.FiniteGroupClass.pGroup ℓ)
    (ProCGroups.FiniteGroupClass.pGroup_hereditary ℓ) f
  exact ProCGroups.QuotientGroup.mapₜ _ _ f (Subgroup.map_le_iff_le_comap.mp hmap)

/-- Conjugation by `g` induces the canonical map on the ℓ-primary factor. -/
noncomputable def primaryConjugationMap (ℓ : ℕ) [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    [CompactSpace G] (g : G) :
    PrimaryAbelianization ℓ D →ₜ* PrimaryAbelianization ℓ D := by
  letI : CompactSpace D := hDclosed.isClosedEmbedding_subtypeVal.compactSpace
  let e := conjugationTopologicalAbelianizationContinuousAut D g
  let f : TopologicalAbelianization D →ₜ* TopologicalAbelianization D :=
    { toMonoidHom := e.toMulEquiv.toMonoidHom
      continuous_toFun := e.continuous_toFun }
  have hmap := map_proCResidualCore_le_of_continuousMonoidHom
    (C := ProCGroups.FiniteGroupClass.pGroup ℓ)
    (ProCGroups.FiniteGroupClass.pGroup_hereditary ℓ) f
  exact ProCGroups.QuotientGroup.mapₜ _ _ f (Subgroup.map_le_iff_le_comap.mp hmap)

/-- Elements of the ℓ-primary abelianization fixed by a subgroup. -/
def primaryFixedSubgroup (ℓ : ℕ) [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (D : Subgroup G) [D.Normal]
    (hDclosed : IsClosed (D : Set G)) (H : Subgroup G) :
    Subgroup (PrimaryAbelianization ℓ D) where
  carrier := {a | ∀ h : H, primaryConjugationMap ℓ D hDclosed (h : G) a = a}
  one_mem' := by intro h; exact map_one _
  mul_mem' := by
    intro x y hx hy h
    rw [map_mul, hx h, hy h]
  inv_mem' := by
    intro x hx h
    rw [map_inv, hx h]

/-- The closed commutator subgroup `[D,D]`, as a subgroup of the ambient
group. -/
abbrev relativeDerived
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) : Subgroup G :=
  closedDerivedSeries (G := G) D 1

instance relativeDerived_normal
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) [D.Normal] : (relativeDerived D).Normal := by
  change (⁅D, D⁆.topologicalClosure).Normal
  exact Subgroup.is_normal_topologicalClosure ⁅D, D⁆

/-- The actual quotient `G/[D,D]`. -/
abbrev RelativeDerivedQuotient
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) [D.Normal] :=
  G ⧸ relativeDerived D

end Yamaguchi26AbfaithfulGalois
