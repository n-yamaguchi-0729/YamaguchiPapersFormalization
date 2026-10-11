/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.GeometricFiber.ArithmeticSectionFactorization
import EtaleFundamentalGroups.GeometricFiber.ArithmeticNormal
import EtaleFundamentalGroups.GeometricFiber.ArithmeticConnected
import EtaleFundamentalGroups.GeometricFiber.ArithmeticComposite
import EtaleFundamentalGroups.GaloisCategories.SectionFactorizationEpi
import EtaleFundamentalGroups.GaloisCategories.ExactSequence
import ProCGroups.Presentations.Profinite

/-!
# Arithmetic Exact

Exactness at the middle fundamental group for the separable constant
extension of a qcqs scheme whose geometric base change is connected.
-/

noncomputable section
open CategoryTheory Limits CategoryTheory.PreGaloisCategory
universe u
namespace AlgebraicGeometry.FiniteEtale

/-- Exactness at the middle fundamental group for the separable constant
extension of a qcqs scheme whose geometric base change is connected. -/
theorem fundamentalGroupHom_constantField_ker_eq_range
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] [IsSepClosed L]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    (fundamentalGroupHom f (xi ≫ Limits.pullback.snd _ f)).toMonoidHom.ker =
      (fundamentalGroupHom (Limits.pullback.snd _ f) xi).toMonoidHom.range := by
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  let : (pullback p).Faithful := (pullbackFiberIso p xi).faithful_of_comp
  have hsurj := fundamentalGroupHom_surjective_of_connected_constantField k L f (xi ≫ p)
  have hff : Nonempty (pullback f).FullyFaithful :=
    ((autHomOfCompIso_surjective_tfae
      (fiber ((xi ≫ p) ≫ f)) (fiber (xi ≫ p)) (pullback f)
      (pullbackFiberIso f (xi ≫ p))).out 1 2).mp hsurj
  have hcomp := fundamentalGroupHom_constantField_comp_eq_one k L f xi
  have hcriterion := ((autHomOfCompIso_exact_sequence_tfae (pullback f) (pullback p)
    (pullbackFiberIso f (xi ≫ p)) (pullbackFiberIso p xi)).out 3 1).mp
      (by
        refine ⟨hff, ?_, ?_⟩
        · exact (autHomOfCompIso_comp_eq_one_iff (pullback f) (pullback p)
            (pullbackFiberIso f (xi ≫ p)) (pullbackFiberIso p xi)).1 hcomp
        · intro Y hY
          exact exists_epi_of_terminal_section_factorizations (pullback f) (pullback p) Y
            (exists_constantCover_section_factorization k L X f Y) hY)
  change (fundamentalGroupHom f (xi ≫ p)).toMonoidHom.ker =
    (fundamentalGroupHom p xi).toMonoidHom.range
  have hker : (fundamentalGroupHom f (xi ≫ p)).toMonoidHom.ker =
      ProCGroups.Presentations.Subgroup.closedNormalClosure
        (Set.range (fundamentalGroupHom p xi)) := hcriterion.2.2
  refine hker.trans ?_
  let h := fundamentalGroupHom p xi
  let : h.toMonoidHom.range.Normal := fundamentalGroupHom_constantField_range_normal k L f xi
  have hclosed : IsClosed (Set.range h) := (isCompact_range h.continuous).isClosed
  apply le_antisymm
  · exact ProCGroups.Presentations.closedNormalClosure_le_closed_normal
      hclosed (fun _ hx ↦ hx)
  · exact ProCGroups.Presentations.subset_closedNormalClosure (Set.range h)

end AlgebraicGeometry.FiniteEtale
