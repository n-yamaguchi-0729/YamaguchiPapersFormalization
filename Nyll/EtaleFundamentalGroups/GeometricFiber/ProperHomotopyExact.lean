/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperHomotopyNormal
import Nyll.EtaleFundamentalGroups.GeometricFiber.HomotopySequenceMaps
import Nyll.EtaleFundamentalGroups.GaloisCategories.ConnectedSectionDescent
import Nyll.EtaleFundamentalGroups.GaloisCategories.ExactSequence
import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
import Nyll.EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Nyll.ProCGroups.Presentations.Profinite

/-!
# The proper homotopy sequence

The kernel at the middle term is the actual image of the geometric-fibre
fundamental group. Stein descent supplies descent of connected covers;
finite connected-component decomposition then supplies the categorical
exactness criterion. Normality and compactness identify the resulting closed
normal closure with the original image.
-/

noncomputable section
open CategoryTheory Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Exactness at the middle term of the actual fundamental-group sequence
for a proper flat finitely presented family with geometrically reduced
connected fibres over an arbitrary connected base (Stacks Project Tag 0C0J). -/
theorem fundamentalGroupHom_proper_geometricFiber_ker_eq_range
    {X S : Scheme.{u}} [ConnectedSpace S]
    (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyReduced f]
    [GeometricallyConnected f]
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback s f) :
    (fundamentalGroupHom f (xi ≫ Limits.pullback.snd s f)).toMonoidHom.ker =
      (fundamentalGroupHom (Limits.pullback.snd s f) xi).toMonoidHom.range := by
  have hX : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have hFibre : ConnectedSpace ↥(Limits.pullback s f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.fst s f)
  let p : Limits.pullback s f ⟶ X := Limits.pullback.snd s f
  have hTerminal : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  have hsurj := fundamentalGroupHom_surjective_of_flat_geometricallyConnected f (xi ≫ p)
  have hff : Nonempty (pullback f).FullyFaithful :=
    ((autHomOfCompIso_surjective_tfae (fiber ((xi ≫ p) ≫ f)) (fiber (xi ≫ p))
      (pullback f) (pullbackFiberIso f (xi ≫ p))).out 1 2).mp hsurj
  have hcomp := fundamentalGroupHom_geometricFiber_comp_eq_one f s xi
  have hconn (Y : FiniteEtale X) (hY : IsConnected Y)
      (hs : Nonempty (⊤_ (FiniteEtale (Limits.pullback s f)) ⟶ (pullback p).obj Y)) :
      (pullback f).essImage Y := by
    have : IsConnected Y := hY
    have hId : IsFiniteEtale (𝟙 (Limits.pullback s f)) := .mk
    let T : FiniteEtale (Limits.pullback s f) := mk (𝟙 _)
    let hT : IsTerminal T :=
      MorphismProperty.Over.mkIdTerminal (@IsFiniteEtale : MorphismProperty Scheme.{u}) _
    let eT : T ≅ ⊤_ (FiniteEtale (Limits.pullback s f)) :=
      hT.uniqueUpToIso terminalIsTerminal
    let v : T ⟶ (pullback p).obj Y := eT.hom ≫ hs.some
    let l : Limits.pullback s f ⟶ Limits.pullback Y.hom p := v.left
    let a : Limits.pullback s f ⟶ Y.left := l ≫ Limits.pullback.fst Y.hom p
    have hv : l ≫ Limits.pullback.snd Y.hom p = 𝟙 _ := v.w
    have ha : a ≫ Y.hom = p := by
      change (l ≫ Limits.pullback.fst Y.hom p) ≫ Y.hom = p
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hv, Category.id_comp]
    exact essImage_pullback_of_connected_fiber_section f Y s a ha
  have hcriterion := ((autHomOfCompIso_exact_sequence_tfae (pullback f) (pullback p)
    (pullbackFiberIso f (xi ≫ p)) (pullbackFiberIso p xi)).out 3 1).mp (by
      refine ⟨hff, ?_, ?_⟩
      · exact (autHomOfCompIso_comp_eq_one_iff (pullback f) (pullback p)
          (pullbackFiberIso f (xi ≫ p)) (pullbackFiberIso p xi)).1 hcomp
      · intro Y hY
        obtain ⟨A, ⟨e⟩⟩ := essImage_of_trivial_pullback_of_connected_section_descent
          (fiber (xi ≫ p)) (fiber xi) (pullback f) (pullback p)
          (pullbackFiberIso p xi) hconn Y hY
        exact ⟨A, e.hom, inferInstance⟩)
  change (fundamentalGroupHom f (xi ≫ p)).toMonoidHom.ker =
    (fundamentalGroupHom p xi).toMonoidHom.range
  have hker : (fundamentalGroupHom f (xi ≫ p)).toMonoidHom.ker =
      ProCGroups.Presentations.Subgroup.closedNormalClosure
        (Set.range (fundamentalGroupHom p xi)) := hcriterion.2.2
  refine hker.trans ?_
  let h := fundamentalGroupHom p xi
  have hNormal : h.toMonoidHom.range.Normal :=
    fundamentalGroupHom_proper_geometricFiber_range_normal f s xi
  have hclosed : IsClosed (Set.range h) := (isCompact_range h.continuous).isClosed
  apply le_antisymm
  · exact ProCGroups.Presentations.closedNormalClosure_le_closed_normal hclosed (fun _ hx => hx)
  · exact ProCGroups.Presentations.subset_closedNormalClosure (Set.range h)

end AlgebraicGeometry.FiniteEtale
