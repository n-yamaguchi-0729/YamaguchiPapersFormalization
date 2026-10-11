/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Topology.Connected.Basic
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_baseChange_of_field

/-!
# Abelian Scheme Property Bundle of is Pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_of_isPullback
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKcBundleBC

section Transport

variable {R : Type u} [CommRing R] {A B : Scheme.{u}}
  {fA : A ⟶ Spec (CommRingCat.of R)} {fB : B ⟶ Spec (CommRingCat.of R)}
  (e : A ≅ B) (he : e.hom ≫ fB = fA)

include he in
theorem inv_comp_eq : e.inv ≫ fA = fB := by
  rw [← he, e.inv_hom_id_assoc]

/-- The point transported through the forward scheme isomorphism over the base. -/
def toB {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fA) : SchemeHomOver
  t fB :=
  ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩

/-- The point transported through the inverse scheme isomorphism over the base. -/
def ofB {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t fB) : SchemeHomOver
  t fA :=
  ⟨y.1 ≫ e.inv, by rw [Category.assoc, inv_comp_eq e he, y.2]⟩

@[scoped simp] theorem toB_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x :
  SchemeHomOver t fA) :
    (toB e he x).1 = x.1 ≫ e.hom := rfl

@[scoped simp] theorem ofB_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y :
  SchemeHomOver t fB) :
    (ofB e he y).1 = y.1 ≫ e.inv := rfl

@[scoped simp] theorem toB_ofB {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y :
  SchemeHomOver t fB) :
    toB e he (ofB e he y) = y :=
  Subtype.ext (by simp)

@[scoped simp] theorem ofB_toB {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x :
  SchemeHomOver t fA) :
    ofB e he (toB e he x) = x :=
  Subtype.ext (by simp)

theorem toB_schemeHomOverComp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t fA) :
    toB e he (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (toB e he x) :=
  Subtype.ext (by simp)

theorem ofB_schemeHomOverComp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t fB) :
    ofB e he (schemeHomOverComp ψ hψ y) = schemeHomOverComp ψ hψ (ofB e he y) :=
  Subtype.ext (by simp)

/-- The relative group law transported back through the scheme isomorphism. -/
def transportLaw (G : RelativeGroupLaw R fB) : RelativeGroupLaw R fA where
  mul t x y := ofB e he (G.mul t (toB e he x) (toB e he y))
  one t := ofB e he (G.one t)
  inv t x := ofB e he (G.inv t (toB e he x))
  mul_assoc t x y z := by simp only [toB_ofB, G.mul_assoc]
  one_mul t x := by simp only [toB_ofB, G.one_mul, ofB_toB]
  mul_one t x := by simp only [toB_ofB, G.mul_one, ofB_toB]
  inv_mul_cancel t x := by simp only [toB_ofB, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    rw [← ofB_schemeHomOverComp, G.mul_natural t t' ψ hψ, toB_schemeHomOverComp,
      toB_schemeHomOverComp]

end Transport

section Fibres

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  {R' : Type u} [CommRing R'] {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)}
  {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {g : A' ⟶ A}

theorem connectedSpace_of_field {k : Type u} [Field k] {B : Scheme.{u}} {fk : B ⟶ Spec
  (CommRingCat.of k)}
    (hB : AbelianSchemePropertyBundle k fk) : ConnectedSpace B := by
  obtain ⟨s⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  have hs : fk.base ⁻¹' {s} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := hB.connectedFibres s
  rw [hs] at h
  exact connectedSpace_iff_univ.mpr h

theorem isConnected_fibre (hA : AbelianSchemePropertyBundle R f) (hg : IsPullback g f' f ι)
    (s' : ↥(Spec (CommRingCat.of R'))) : _root_.IsConnected (f'.base ⁻¹' {s'}) := by
  let ιk := (Spec (CommRingCat.of R')).fromSpecResidueField s'
  have hk : AbelianSchemePropertyBundle ((Spec (CommRingCat.of R')).residueField s') (pullback.snd
    f (ιk ≫ ι)) :=
    hA.baseChange_of_field (k := (Spec (CommRingCat.of R')).residueField s') (ιk ≫ ι)
  have : ConnectedSpace ↥(pullback f (ιk ≫ ι)) := connectedSpace_of_field hk
  have hsq : IsPullback (pullback.fst f' ιk ≫ g) (pullback.snd f' ιk) f (ιk ≫ ι) :=
    (IsPullback.of_hasPullback f' ιk).paste_horiz hg
  let e : f'.fiber s' ≅ pullback f (ιk ≫ ι) := hsq.isoPullback
  have : ConnectedSpace ↥(f'.fiber s') :=
    (AlgebraicGeometry.Scheme.homeoOfIso e).symm.surjective.connectedSpace
      (AlgebraicGeometry.Scheme.homeoOfIso e).symm.continuous
  rw [← Scheme.Hom.range_fiberι]
  exact isConnected_range (f'.fiberι s').continuous

end Fibres

end P2mKcBundleBC

open _root_.AlgebraicCurves.Geometry in
attribute [local simp]
  AbelianSchemes.Theorems.Proofs.AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.toB_coe
open _root_.AlgebraicCurves.Geometry in
attribute [local simp]
  AbelianSchemes.Theorems.Proofs.AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.ofB_coe
open _root_.AlgebraicCurves.Geometry in
attribute [local simp]
  AbelianSchemes.Theorems.Proofs.AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.toB_ofB
open _root_.AlgebraicCurves.Geometry in
attribute [local simp]
  AbelianSchemes.Theorems.Proofs.AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.ofB_toB


open P2mKcBundleBC in
theorem _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f)
    {R' : Type u} [CommRing R'] {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)}
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {g : A' ⟶ A}
    (hg : IsPullback g f' f ι) :
    AbelianSchemePropertyBundle R' f' where
  smooth := MorphismProperty.of_isPullback hg hA.smooth
  proper := MorphismProperty.of_isPullback hg hA.proper
  connectedFibres := isConnected_fibre hA hg
  hasGroupLaw := by
    obtain ⟨L⟩ := hA.hasGroupLaw
    exact ⟨transportLaw hg.isoPullback (hg.isoPullback_hom_snd) (L.baseChange ι)⟩
end AbelianSchemePropertyBundle_of_isPullback
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation

attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
