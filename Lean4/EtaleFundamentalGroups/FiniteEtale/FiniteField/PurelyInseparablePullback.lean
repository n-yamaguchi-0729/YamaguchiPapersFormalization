/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import SchemeTheory.FiniteEtale.UniversalHomeomorphismFullyFaithful
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Fully faithful pullback across purely inseparable extensions
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups

/-- A purely inseparable field extension induces a universally injective map of spectra. -/
theorem purelyInseparable_specMap_universallyInjective
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  apply ((tfae_universallyInjective _).out 1 2).mpr
  intro K _ a b hab
  apply (Spec.preimage_inj a b).mp
  apply CommRingCat.hom_ext
  apply IsPurelyInseparable.injective_comp_algebraMap k L K
  have h := congrArg Spec.preimage hab
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg CommRingCat.Hom.hom h

/-- The coefficient projection of a purely inseparable extension is an
integral, universally injective, surjective scheme morphism. -/
theorem purelyInseparable_constantField_projection_properties
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    let p := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
    IsIntegralHom p ∧ UniversallyInjective p ∧ Surjective p := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : IsIntegralHom φ := (IsIntegralHom.SpecMap_iff).2
    (Algebra.IsIntegral.isIntegral (R := k))
  let : UniversallyInjective φ := purelyInseparable_specMap_universallyInjective k L
  let : Surjective φ := ⟨fun y ↦ ⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))),
    Subsingleton.elim _ _⟩⟩
  exact ⟨inferInstance,
    MorphismProperty.pullback_snd
      (P := (show MorphismProperty Scheme.{u} from @UniversallyInjective)) φ f inferInstance,
    inferInstance⟩

end EtaleFundamentalGroups
namespace AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups

/-- Canonical finite étale pullback is fully faithful for a purely inseparable
constant extension, for arbitrary schemes. -/
def pullbackFullyFaithful_of_purelyInseparable_constant_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    (FiniteEtale.pullback (Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).FullyFaithful := by
  let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  have hp := purelyInseparable_constantField_projection_properties k L X f
  let : IsIntegralHom p := hp.1
  let : UniversallyInjective p := hp.2.1
  let : Surjective p := hp.2.2
  have hbij (A B : FiniteEtale X) :
      Function.Bijective ((FiniteEtale.pullback p).map (X := A) (Y := B)) := by
    have h := pullback_map_bijective_of_integral_universallyInjective_surjective
      p A.toComma B.toComma
    constructor
    · intro a b hab
      apply MorphismProperty.Over.Hom.ext
      have h' := h.1 (congrArg (fun m ↦ (FiniteEtale.forget _).map m) hab)
      exact congrArg Over.Hom.left h'
    · intro a
      obtain ⟨b, hb⟩ := h.2 ((FiniteEtale.forget _).map a)
      refine ⟨MorphismProperty.Over.homMk b.left b.w, ?_⟩
      apply MorphismProperty.Over.Hom.ext
      exact congrArg Over.Hom.left hb
  let : (FiniteEtale.pullback p).Full := ⟨fun {A B} ↦ (hbij A B).2⟩
  let : (FiniteEtale.pullback p).Faithful := ⟨fun {A B} ↦ (hbij A B).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful (FiniteEtale.pullback p)

end AlgebraicGeometry.FiniteEtale
