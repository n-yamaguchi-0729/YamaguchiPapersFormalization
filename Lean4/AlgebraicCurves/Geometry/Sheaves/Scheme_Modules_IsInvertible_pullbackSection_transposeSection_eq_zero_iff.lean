/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual

/-!
# Vanishing of a transposed section after pullback

For an invertible source module, the section transposed from a module morphism
vanishes after pullback exactly when the pulled-back morphism vanishes.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff

section E6Coev

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace CoevAux
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {Y : Scheme.{u}}

/-- The equivalence given by tensoring on the left with an invertible module. -/
def tensorLeftEquivalence {Z Z' : Y.Modules} (i : Z' ⊗ Z ≅ 𝟙_ Y.Modules) (j : Z ⊗ Z' ≅ 𝟙_
    Y.Modules) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (tensorLeft Z) (tensorLeft Z')
    ((leftUnitorNatIso Y.Modules).symm ≪≫ (tensoringLeft Y.Modules).mapIso i.symm ≪≫
        tensorLeftTensor Z' Z)
    ((tensorLeftTensor Z Z').symm ≪≫ (tensoringLeft Y.Modules).mapIso j ≪≫ leftUnitorNatIso
        Y.Modules)

/-- The equivalence given by tensoring on the right with an invertible module. -/
def tensorRightEquivalence {Z Z' : Y.Modules} (i : Z' ⊗ Z ≅ 𝟙_ Y.Modules) (j : Z ⊗ Z' ≅ 𝟙_
    Y.Modules) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight Z) (tensorRight Z')
    ((rightUnitorNatIso Y.Modules).symm ≪≫ (tensoringRight Y.Modules).mapIso j.symm ≪≫
        tensorRightTensor Z Z')
    ((tensorRightTensor Z' Z).symm ≪≫ (tensoringRight Y.Modules).mapIso i ≪≫ rightUnitorNatIso
        Y.Modules)

theorem isEquivalence_tensorLeft {Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) :
    (tensorLeft Z).IsEquivalence :=
  (tensorLeftEquivalence (β_ _ _ ≪≫ hZ.dual.2.some) hZ.dual.2.some).isEquivalence_functor

theorem isEquivalence_tensorRight {Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) :
    (tensorRight Z).IsEquivalence :=
  (tensorRightEquivalence (β_ _ _ ≪≫ hZ.dual.2.some) hZ.dual.2.some).isEquivalence_functor

theorem isIso_ev_app (X : Y.Modules) (hX : Scheme.Modules.IsInvertible X) (N : Y.Modules) :
    IsIso ((ihom.ev X).app N) := by
  have := isEquivalence_tensorLeft hX
  let e : ihom X ≅ (tensorLeft X).inv :=
    (ihom.adjunction X).rightAdjointUniq (tensorLeft X).asEquivalence.toAdjunction
  have : (ihom X).Full := Functor.Full.of_iso e.symm
  have : (ihom X).Faithful := Functor.Faithful.of_iso e.symm
  have : IsIso (ihom.adjunction X).counit := Adjunction.counit_isIso_of_R_fully_faithful _
  exact NatIso.isIso_app_of_isIso (ihom.adjunction X).counit N

theorem whiskerRight_eq_zero_iff {L M Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) (f : L
    ⟶ M) :
    f ▷ Z = 0 ↔ f = 0 := by
  have := isEquivalence_tensorRight hZ
  constructor
  · intro h
    apply (tensorRight Z).map_injective
    rw [Functor.map_zero]
    exact h
  · rintro rfl
    exact (tensorRight Z).map_zero _ _

theorem transposeSection_eq_zero_iff' {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ
    : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    s = 0 ↔ φ = 0 := by
  have hiso := isIso_ev_app X hX (𝟙_ Y.Modules)
  rw [← whiskerRight_eq_zero_iff hX.dual.1 φ, ← hs]
  exact (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ _ s hiso).symm

theorem pullbackSection_transposeSection_eq_zero_iff' {Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M :
    Y.Modules}
    (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 := by
  have hiso := isIso_ev_app X hX (𝟙_ Y.Modules)
  have hiso' : IsIso ((Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules))) :=
    let e := (Scheme.Modules.pullback g).mapIso (@asIso _ _ _ _ ((ihom.ev X).app (𝟙_ Y.Modules))
        hiso)
    ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  have h1 : (Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules)) ≫
      (Scheme.Modules.pullback g).map s
      = (Scheme.Modules.pullback g).map (φ ▷ Scheme.Modules.dual X) :=
    ((Scheme.Modules.pullback g).map_comp _ _).symm.trans (congrArg _ hs)
  calc Scheme.Modules.pullbackSection g s = 0
      ↔ (Scheme.Modules.pullback g).map s = 0 := by
        rw [Scheme.Modules.pullbackSection_def]
        let e : (Scheme.Modules.pullback g).obj (𝟙_ Y.Modules) ≅ 𝟙_ Y'.Modules :=
          Scheme.Modules.pullbackUnitIso g
        change e.inv ≫ (Scheme.Modules.pullback g).map s = 0 ↔
          (Scheme.Modules.pullback g).map s = 0
        exact Preadditive.IsIso.comp_left_eq_zero e.inv _
    _ ↔ (Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules)) ≫
        (Scheme.Modules.pullback g).map s = 0 :=
        (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ _ _ hiso').symm
    _ ↔ (Scheme.Modules.pullback g).map (φ ▷ Scheme.Modules.dual X) = 0 :=
        iff_of_eq (congrArg (fun t => t = 0) h1)
    _ ↔ Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) X (Scheme.Modules.dual X) ≫
          ((Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj
              (Scheme.Modules.dual X)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M (Scheme.Modules.dual X) = 0 :=
        iff_of_eq (congrArg (fun t => t = 0) (Functor.Monoidal.map_whiskerRight _ _ _))
    _ ↔ ((Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj
        (Scheme.Modules.dual X)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M (Scheme.Modules.dual X) = 0 :=
        Preadditive.IsIso.comp_left_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual
        X) = 0 :=
        Preadditive.IsIso.comp_right_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map φ = 0 := whiskerRight_eq_zero_iff (hX.dual.1.pullback g) _

end AlgebraicGeometry.Scheme.Modules.CoevAux

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
    _root_.AlgebraicGeometry
    Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.AlgebraicGeometry in
with_weak_namespace Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
open AlgebraicGeometry.Scheme.Modules.CoevAux in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
theorem pullbackSection_transposeSection_eq_zero_iff
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ :
        X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 :=
  pullbackSection_transposeSection_eq_zero_iff' g hX φ s hs

end
end E6Coev
end Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open
  _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
