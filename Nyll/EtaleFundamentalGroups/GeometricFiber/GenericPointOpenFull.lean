/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.StalkSpreadingOpen
import Nyll.SchemeTheory.Etale.UniversalHomeomorphismSections
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The generic-point map from full restriction to nonempty opens

For an irreducible scheme, the residue field of the generic point maps
surjectively onto the spectrum of its actual stalk. The map is a closed
immersion and hence a universal homeomorphism, even for nonreduced schemes.
An etale section over the generic residue field therefore lifts to the
actual stalk and spreads to an open neighborhood by the proved filtered
stalk finite-presentation descent. Fullness of restriction to that open
then gives a global section. The Galois-category section criterion gives
the original fundamental-group surjection and full faithfulness.

The nonempty-open fullness premise is an ordinary intermediate implication;
it is supplied by the geometric-unibranch theorem in the original endpoint.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

/-- The generic residue field covers the entire spectrum of the generic
stalk, without a reducedness assumption. -/
theorem specMap_residue_genericPoint_surjective
    (X : Scheme.{u}) [IrreducibleSpace X] :
    Surjective (Spec.map (X.residue (genericPoint X))) := by
  let q : Spec (X.presheaf.stalk (genericPoint X)) ⟶ X :=
    X.fromSpecStalk (genericPoint X)
  constructor
  intro t
  let s : Spec (X.residueField (genericPoint X)) := default
  refine ⟨s, ?_⟩
  apply q.isEmbedding.injective
  have ht : q t ⤳ genericPoint X := by
    have h := (IsLocalRing.specializes_closedPoint t).map q.continuous
    rw [Scheme.fromSpecStalk_closedPoint] at h
    exact h
  calc
    q (Spec.map (X.residue (genericPoint X)) s) = genericPoint X :=
      (congrArg q (Scheme.SpecMap_residue_apply (genericPoint X) s)).trans
        (Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X))
    _ = q t := ((genericPoint_specializes (q t)).antisymm ht).eq

private theorem exists_section_of_full_pullback
    {X T : Scheme.{u}} (j : T ⟶ X) [(pullback j).Full]
    (W : FiniteEtale X) (a : T ⟶ W.left) (ha : a ≫ W.hom = j) :
    ∃ b : X ⟶ W.left, b ≫ W.hom = 𝟙 X := by
  have : IsFiniteEtale (𝟙 X) := .mk
  let E : FiniteEtale X := mk (𝟙 X)
  let p : Limits.pullback (𝟙 X) j ⟶ T := Limits.pullback.snd (𝟙 X) j
  let v₀ : Limits.pullback (𝟙 X) j ⟶ Limits.pullback W.hom j :=
    Limits.pullback.lift (p ≫ a) p (by rw [Category.assoc, ha])
  let v : (pullback j).obj E ⟶ (pullback j).obj W :=
    MorphismProperty.Over.homMk v₀ (Limits.pullback.lift_snd _ _ _)
  obtain ⟨b, _⟩ := (pullback j).map_surjective v
  exact ⟨b.left, b.w⟩

/-- If restriction to every nonempty open is full, a finite-etale cover
with a section at the generic residue field has a global section. -/
theorem exists_section_of_genericPoint_of_nonemptyOpenFull
    {X : Scheme.{u}} [IrreducibleSpace X]
    (hFull : ∀ (U : X.Opens), (U : Set X).Nonempty → (pullback U.ι).Full)
    (W : FiniteEtale X)
    (a : Spec (X.residueField (genericPoint X)) ⟶ W.left)
    (ha : a ≫ W.hom = X.fromSpecResidueField (genericPoint X)) :
    ∃ b : X ⟶ W.left, b ≫ W.hom = 𝟙 X := by
  let r : Spec (X.residueField (genericPoint X)) ⟶
      Spec (X.presheaf.stalk (genericPoint X)) :=
    Spec.map (X.residue (genericPoint X))
  have : Surjective r := specMap_residue_genericPoint_surjective X
  obtain ⟨a₀, ha₀, _⟩ :=
    Etale.exists_lift_of_integral_universallyInjective_surjective
      r W.hom (X.fromSpecStalk (genericPoint X)) a ha
  obtain ⟨U, hηU, aU, _, haU⟩ :=
    Scheme.exists_open_extension_fromSpecStalk W.hom (genericPoint X) a₀ ha₀
  have : (pullback U.ι).Full := hFull U ⟨genericPoint X, hηU⟩
  exact exists_section_of_full_pullback U.ι W aU haU

/-- The literal generic-point morphism induces a surjection on fundamental
groups whenever all nonempty-open finite-etale restrictions are full. The
chosen geometric point of the generic residue field is retained. -/
theorem genericPoint_fundamentalGroupHom_surjective_of_nonemptyOpenFull
    {X : Scheme.{u}} [IrreducibleSpace X]
    (hFull : ∀ (U : X.Opens), (U : Set X).Nonempty → (pullback U.ι).Full)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ Spec (X.residueField (genericPoint X))) :
    Function.Surjective
      (fundamentalGroupHom (X.fromSpecResidueField (genericPoint X)) ξ) := by
  let G : Scheme.{u} := Spec (X.residueField (genericPoint X))
  let j : G ⟶ X := X.fromSpecResidueField (genericPoint X)
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
    pullback_preservesLimitsOfShape_pempty j
  change Function.Surjective (autHomOfCompIso (pullback j) (pullbackFiberIso j ξ))
  apply ((autHomOfCompIso_surjective_tfae
    (fiber (ξ ≫ j)) (fiber ξ) (pullback j) (pullbackFiberIso j ξ)).out 4 1).mp
  intro W _ hs
  obtain ⟨s⟩ := hs
  have : IsFiniteEtale (𝟙 G) := .mk
  let E : FiniteEtale G := mk (𝟙 G)
  have hE : IsTerminal E :=
    MorphismProperty.Over.mkIdTerminal (@IsFiniteEtale : MorphismProperty Scheme.{u}) G
  let e : E ≅ ⊤_ (FiniteEtale G) := hE.uniqueUpToIso terminalIsTerminal
  let v : E ⟶ (pullback j).obj W := e.hom ≫ s
  let f : W.left ⟶ X := W.hom
  let v₀ : G ⟶ Limits.pullback f j := v.left
  have hv : v₀ ≫ Limits.pullback.snd f j = 𝟙 G := v.w
  let a : G ⟶ W.left := v₀ ≫ Limits.pullback.fst f j
  have ha : a ≫ f = j := by
    change (v₀ ≫ Limits.pullback.fst f j) ≫ f = j
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hv, Category.id_comp]
  obtain ⟨b, hb⟩ := exists_section_of_genericPoint_of_nonemptyOpenFull hFull W a ha
  have : IsFiniteEtale (𝟙 X) := .mk
  let E' : FiniteEtale X := mk (𝟙 X)
  have hE' : IsTerminal E' :=
    MorphismProperty.Over.mkIdTerminal (@IsFiniteEtale : MorphismProperty Scheme.{u}) X
  let e' : E' ≅ ⊤_ (FiniteEtale X) := hE'.uniqueUpToIso terminalIsTerminal
  let b' : E' ⟶ W := MorphismProperty.Over.homMk b hb
  exact ⟨e'.inv ≫ b'⟩

/-- Full faithfulness of the actual generic-residue-field pullback follows
from full restriction to all nonempty opens, with no normality or
reducedness assumption. -/
def genericPointPullbackFullyFaithful_of_nonemptyOpenFull
    {X : Scheme.{u}} [IrreducibleSpace X]
    (hFull : ∀ (U : X.Opens), (U : Set X).Nonempty → (pullback U.ι).Full) :
    (pullback (X.fromSpecResidueField (genericPoint X))).FullyFaithful := by
  let Ω := AlgebraicClosure (X.residueField (genericPoint X))
  let ξ : Spec (.of Ω) ⟶ Spec (X.residueField (genericPoint X)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) Ω))
  let j := X.fromSpecResidueField (genericPoint X)
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
    pullback_preservesLimitsOfShape_pempty j
  have hsurj : Function.Surjective (autHomOfCompIso (pullback j) (pullbackFiberIso j ξ)) :=
    genericPoint_fundamentalGroupHom_surjective_of_nonemptyOpenFull hFull ξ
  exact Classical.choice (((autHomOfCompIso_surjective_tfae
    (fiber (ξ ≫ j)) (fiber ξ) (pullback j) (pullbackFiberIso j ξ)).out 1 2).mp hsurj)

end AlgebraicGeometry.FiniteEtale
