/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.HenselianPair
import EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import EtaleFundamentalGroups.GeometricFiber.AlgebraicClosure
import EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction

/-!
# The actual closed-point fundamental group of a henselian local ring

The existing henselian finite étale equivalence and the canonical extension
of a separably closed geometric-point field identify the residue Galois group
with the fundamental group at the actual closed geometric point. An explicit
residue-field isomorphism permits the original residue field to be retained.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (H : Type u) [CommRing H] [HenselianLocalRing H]

/-- Henselian reduction is an equivalence for the native finite étale category. -/
theorem henselianResiduePullback_isEquivalence :
    (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H)))).IsEquivalence := by
  have : MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ (@Etale : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have htransport (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (hP : P = (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (h : (MorphismProperty.Over.pullback P ⊤
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H)))).IsEquivalence) :
      (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H)))).IsEquivalence := by
    subst P
    exact h
  exact htransport _ IsFiniteEtale.eq_inf.symm
    (pullback_isEquivalence_of_henselian (IsLocalRing.maximalIdeal H))

variable (k : Type u) [Field k] (e : IsLocalRing.ResidueField H ≃+* k)

/-- The original closed-point inclusion expressed through its actual residue isomorphism. -/
def henselianClosedPoint : Spec (.of k) ⟶ Spec (.of H) :=
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))

/-- The actual residue isomorphism preserves the henselian pullback equivalence. -/
theorem henselianClosedPoint_pullback_isEquivalence :
    (pullback (henselianClosedPoint H k e)).IsEquivalence := by
  have : (pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H)))).IsEquivalence :=
    henselianResiduePullback_isEquivalence H
  let j : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField H)) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  let i : Spec (.of k) ≅ Spec (.of (IsLocalRing.ResidueField H)) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let E : FiniteEtale (Spec (.of (IsLocalRing.ResidueField H))) ≌
      FiniteEtale (Spec (.of k)) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ i.symm
  have : (pullback j).IsEquivalence := E.isEquivalence_functor
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) j :=
    ⟨fun h hf => MorphismProperty.of_isPullback (P := @IsFiniteEtale) h hf⟩
  have : MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme.{u}) j :=
    ⟨fun _ _ => inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))) :=
    ⟨fun h hf => MorphismProperty.of_isPullback (P := @IsFiniteEtale) h hf⟩
  have : MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))) := ⟨fun _ _ => inferInstance⟩
  let c : pullback (henselianClosedPoint H k e) ≅
      pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))) ⋙ pullback j :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) j
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue H)))
  exact Functor.isEquivalence_of_iso c.symm

variable (C Ω : Type u) [Field C] [Field Ω]
  [Algebra k C] [IsSepClosure k C] [Algebra C Ω] [Algebra k Ω]
  [IsScalarTower k C Ω] [IsSepClosed Ω]

/-- The residue Galois group is the fundamental group at the actual extended
closed geometric point, using the prescribed residue isomorphism. -/
def henselianResidueGaloisEquivFundamentalGroup :
    Gal(C/k) ≃ₜ* π₁ᵉᵗ(ξ k Ω ≫ henselianClosedPoint H k e) := by
  have : PreconnectedSpace (Spec (.of H)) := by
    refine ⟨?_⟩
    intro U V hU hV hcover hneU hneV
    rcases hcover (Set.mem_univ (IsLocalRing.closedPoint H)) with h | h
    · obtain ⟨v, _, hv⟩ := hneV
      exact ⟨v, trivial, (IsLocalRing.specializes_closedPoint v).mem_open hU h, hv⟩
    · obtain ⟨v, _, hv⟩ := hneU
      exact ⟨v, trivial, hv, (IsLocalRing.specializes_closedPoint v).mem_open hV h⟩
  have : ConnectedSpace (Spec (.of H)) := ⟨⟨IsLocalRing.closedPoint H⟩⟩
  have : (pullback (henselianClosedPoint H k e)).IsEquivalence :=
    henselianClosedPoint_pullback_isEquivalence H k e
  exact (absoluteGaloisToExtendedFiberAut k C Ω).trans
    (fundamentalGroupEquivOfPullbackEquivalence (henselianClosedPoint H k e) (ξ k Ω))

/-- The closed-point Galois comparison has the literal compatible field action.
The computation is retained at abstract ring and field structures. -/
theorem henselianResidueGaloisEquivFundamentalGroup_point
    (σ : Gal(C/k)) (ρ : Ω →+* Ω)
    (hρ : ρ.comp (algebraMap C Ω) = (algebraMap C Ω).comp σ.toRingHom)
    (X : FiniteEtale (Spec (.of H)))
    (x : (fiber (ξ k Ω ≫ henselianClosedPoint H k e)).obj X) :
    (fiberObjEquivHom (ξ k Ω ≫ henselianClosedPoint H k e) X
      ((henselianResidueGaloisEquivFundamentalGroup H k e C Ω σ).hom.app X x)).left =
      Spec.map (CommRingCat.ofHom ρ) ≫
        (fiberObjEquivHom (ξ k Ω ≫ henselianClosedPoint H k e) X x).left :=
  fundamentalGroupHom_point_of_point_action (henselianClosedPoint H k e) (ξ k Ω)
    (absoluteGaloisToExtendedFiberAut k C Ω σ) ρ
    (absoluteGaloisToExtendedFiberAut_point k C Ω σ ρ hρ) X x

end AlgebraicGeometry.FiniteEtale
