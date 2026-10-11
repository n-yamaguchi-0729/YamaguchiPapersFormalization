/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Fundamental groups and nonempty open immersions

For a normal locally Noetherian integral scheme, restriction to a nonempty
open subscheme induces a surjection on etale fundamental groups.  The proof
uses the connected-object criterion for surjectivity: a connected finite-etale
cover has integral source, so its pullback to a nonempty open remains
connected.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem pullback_preservesTerminal {X U : Scheme.{u}}
    (j : U ⟶ X) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) := by
  let hIdX : IsFiniteEtale (𝟙 X) :=
    MorphismProperty.id_mem @IsFiniteEtale X
  let hIdU : IsFiniteEtale (𝟙 U) :=
    MorphismProperty.id_mem @IsFiniteEtale U
  let TX : FiniteEtale X :=
    @FiniteEtale.mk _ _ (𝟙 X) hIdX
  let TU : FiniteEtale U :=
    @FiniteEtale.mk _ _ (𝟙 U) hIdU
  let (Y : FiniteEtale X) : Unique (Y ⟶ TX) :=
    { default := MorphismProperty.Over.homMk Y.hom (by
        change Y.hom ≫ (𝟙 X : X ⟶ X) = Y.hom
        exact Category.comp_id _)
      uniq := fun b ↦ by
        apply MorphismProperty.Over.Hom.ext
        have hb := b.w
        change b.left ≫ (𝟙 X : X ⟶ X) = Y.hom at hb
        exact (Category.comp_id b.left).symm.trans hb }
  let (Y : FiniteEtale U) : Unique (Y ⟶ TU) :=
    { default := MorphismProperty.Over.homMk Y.hom (by
        change Y.hom ≫ (𝟙 U : U ⟶ U) = Y.hom
        exact Category.comp_id _)
      uniq := fun b ↦ by
        apply MorphismProperty.Over.Hom.ext
        have hb := b.w
        change b.left ≫ (𝟙 U : U ⟶ U) = Y.hom at hb
        exact (Category.comp_id b.left).symm.trans hb }
  have hTX : IsTerminal TX := IsTerminal.ofUnique TX
  have hTU : IsTerminal TU := IsTerminal.ofUnique TU
  let A : FiniteEtale U := (pullback j).obj (⊤_ (FiniteEtale X))
  let B : FiniteEtale U := (pullback j).obj TX
  let eAB : A ≅ B :=
    (pullback j).mapIso (terminalIsTerminal.uniqueUpToIso hTX)
  have : IsIso TX.hom := by
    change IsIso (𝟙 X : X ⟶ X)
    exact CategoryTheory.IsIso.id X
  have hSnd : IsIso (pullback.snd TX.hom j) := inferInstance
  let : IsIso (pullback.snd TX.hom j) := hSnd
  have : IsIso B.hom := by
    change IsIso (pullback.snd TX.hom j)
    exact hSnd
  let eBU₀ : B.left ≅ U := by
    change (Limits.pullback TX.hom j) ≅ U
    exact asIso (pullback.snd TX.hom j)
  let eBU : B ≅ TU :=
    MorphismProperty.Over.isoMk eBU₀ (by
      dsimp only [eBU₀, TU, FiniteEtale.mk_hom]
      exact Category.comp_id _)
  let e : A ≅ TU := eAB ≪≫ eBU
  have hA : IsTerminal A := hTU.ofIso e.symm
  let eTop : A ≅ ⊤_ (FiniteEtale U) :=
    hA.uniqueUpToIso terminalIsTerminal
  let : PreservesLimit (Functor.empty.{0} (FiniteEtale X))
      (pullback j) :=
    preservesTerminal_of_iso (pullback j) eTop
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (pullback j)

/-- Base change of finite-etale covers along an arbitrary scheme morphism
preserves the terminal object.  This is the empty-limit input needed by the
Galois-category criteria for full faithfulness and surjectivity. -/
theorem pullback_preservesLimitsOfShape_pempty
    {X U : Scheme.{u}} (j : U ⟶ X) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
  pullback_preservesTerminal j

/-- If base change along a morphism of connected schemes preserves connected
finite-etale covers, then that base-change functor is fully faithful.

This is the connected-object form of the Galois-category surjectivity
criterion, applied to the actual geometric fiber comparison. -/
theorem pullback_fullyFaithful_of_preserves_connected
    {X U : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace U]
    (j : U ⟶ X)
    (hconnected : ∀ W : FiniteEtale X, IsConnected W →
      IsConnected ((pullback j).obj W)) :
    Nonempty (pullback j).FullyFaithful := by
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
    pullback_preservesLimitsOfShape_pempty j
  let u : U := Classical.choice (inferInstance : Nonempty U)
  let Omega := AlgebraicClosure (U.residueField u)
  let xi : Spec (.of Omega) ⟶ U :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (U.residueField u) Omega)) ≫
      U.fromSpecResidueField u
  exact ((autHomOfCompIso_surjective_tfae
    (fiber (xi ≫ j)) (fiber xi) (pullback j)
    (pullbackFiberIso j xi)).out 3 2).mp hconnected

/-- A nonempty open immersion into a normal locally Noetherian integral
scheme induces a surjection on etale fundamental groups. -/
theorem fundamentalGroupHom_surjective_of_isOpenImmersion
    {X U : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ U) :
    Function.Surjective (fundamentalGroupHom j ξ) := by
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : ConnectedSpace X := inferInstance
  let : ConnectedSpace U := inferInstance
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback j) :=
    pullback_preservesTerminal j
  change Function.Surjective
    (autHomOfCompIso (pullback j) (pullbackFiberIso j ξ))
  apply ((autHomOfCompIso_surjective_tfae
    (fiber (ξ ≫ j)) (fiber ξ) (pullback j)
    (pullbackFiberIso j ξ)).out 3 1).mp
  intro Y hY
  let : IsConnected Y := hY
  exact EtaleFundamentalGroups.pullback_obj_isConnected_of_isOpenImmersion
    j Y

end AlgebraicGeometry.FiniteEtale
