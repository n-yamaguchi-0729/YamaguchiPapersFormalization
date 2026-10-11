/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.CompleteRegularLocalPurity
import Nyll.EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletion
import Nyll.EtaleFundamentalGroups.Purity.Local.PuncturedFiniteEtaleSections
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompletionDescentFrontier
import Nyll.SchemeTheory.FiniteEtale.AffinizationExtension
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Punctured purity descends from the maximal-adic completion

The completed extension preserves global sections by the prime-pair Hartogs
theorem. Flat base change then descends its finite étale section algebra and
the open immersion into its affinization. The original cover is recovered
as the restriction of this finite étale affinization.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TopologicalSpace

namespace EtaleFundamentalGroups

universe u

/-- Every regular local ring of dimension at least two has punctured purity. -/
theorem hasPuncturedPurity_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : 2 ≤ ringKrullDim R) : FiniteEtale.HasPuncturedPurity R := by
  let C := AdicCompletion (maximalIdeal R) R
  let : IsRegularLocalRing C := maximalAdicCompletion_isRegularLocalRing R
  let : IsDomain C := IsRegularLocalRing.isDomain C
  let : Module.FaithfullyFlat R C := maximalAdicCompletion_faithfullyFlat R
  have hdimC : 2 ≤ ringKrullDim C := by
    rw [maximalAdicCompletion_ringKrullDim_eq R]
    exact hdim
  have hpure := hasPuncturedPurity_of_complete_isRegularLocalRing C hdimC
  apply (FiniteEtale.hasPuncturedPurity_iff R).mpr
  intro Y
  let f : Y.left ⟶ Scheme.puncturedSpectrum R := Y.hom
  let : IsFiniteEtale f := Y.prop
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion C) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : NoetherianSpace (Scheme.puncturedSpectrum R) :=
    (Scheme.puncturedSpectrumOpen R).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let g : Spec (.of C) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  let h : Scheme.puncturedSpectrum C ⟶ Scheme.puncturedSpectrum R :=
    maximalAdicCompletionPuncturedSpectrumMorphism R
  have hg : Flat g ∧ Surjective g :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap R C))).mpr
      ((RingHom.faithfullyFlat_algebraMap_iff (R := R) (S := C)).mpr inferInstance)
  let : Flat g := hg.1
  let : Surjective g := hg.2
  let : CompactSpace Y.left :=
    (quasiCompact_iff_compactSpace f).mp inferInstance
  obtain ⟨V, ⟨e⟩⟩ := exists_maximalAdicCompletion_extension_of_hasPuncturedPurity R hpure Y
  let p : V.left ⟶ Spec (.of C) := V.hom
  let : IsFiniteEtale p := V.prop
  let eY : pullback p (Scheme.puncturedSpectrumInclusion C) ≅
      pullback f h :=
    ((FiniteEtale.forget (Scheme.puncturedSpectrum C)) ⋙
      Over.forget (Scheme.puncturedSpectrum C)).mapIso e
  have heY : eY.inv ≫ pullback.snd p (Scheme.puncturedSpectrumInclusion C) =
      pullback.snd f h := e.inv.hom.w
  have hb : IsPullback (pullback.fst f h)
      (pullback.snd f h ≫ Scheme.puncturedSpectrumInclusion C)
      (f ≫ (Scheme.puncturedSpectrumOpen R).ι) g :=
    (IsPullback.of_hasPullback f h).paste_vert
      (maximalAdicCompletionPuncturedSpectrumMorphism_isPullback R)
  let eP := hb.isoPullback
  let j : pullback (f ≫ (Scheme.puncturedSpectrumOpen R).ι) g ⟶ V.left :=
    eP.inv ≫ eY.inv ≫ pullback.fst p (Scheme.puncturedSpectrumInclusion C)
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (eP.inv ≫ eY.inv ≫
      pullback.fst p (Scheme.puncturedSpectrumInclusion C)))
  let : IsIso (p ⁻¹ᵁ Scheme.puncturedSpectrumOpen C).ι.appTop :=
    isIso_punctured_finiteEtale_inclusion_appTop C hdimC p
  let eOpen := pullbackRestrictIsoRestrict p (Scheme.puncturedSpectrumOpen C)
  let : IsIso eY.inv.appTop := Scheme.Γ.map_isIso eY.inv.op
  let : IsIso eP.inv.appTop := Scheme.Γ.map_isIso eP.inv.op
  have heOpen : (pullbackRestrictIsoRestrict p
      (Scheme.puncturedSpectrumOpen C)).hom ≫
        (p ⁻¹ᵁ Scheme.puncturedSpectrumOpen C).ι =
      pullback.fst p (Scheme.puncturedSpectrumInclusion C) :=
    pullbackRestrictIsoRestrict_hom_ι p (Scheme.puncturedSpectrumOpen C)
  let : IsIso (pullback.fst p (Scheme.puncturedSpectrumInclusion C)).appTop := by
    rw [← heOpen, Scheme.Hom.comp_appTop]
    exact IsIso.comp_isIso'
      (isIso_punctured_finiteEtale_inclusion_appTop C hdimC p)
      (Scheme.Γ.map_isIso eOpen.hom.op)
  let : IsIso j.appTop := by
    dsimp only [j]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    infer_instance
  have hj : j ≫ p = pullback.snd
      (f ≫ (Scheme.puncturedSpectrumOpen R).ι) g := by
    calc
      j ≫ p = eP.inv ≫ eY.inv ≫
          (pullback.fst p (Scheme.puncturedSpectrumInclusion C) ≫ p) := by
        simp only [j, Category.assoc]
      _ = eP.inv ≫ eY.inv ≫
          (pullback.snd p (Scheme.puncturedSpectrumInclusion C) ≫
            Scheme.puncturedSpectrumInclusion C) := by rw [pullback.condition]
      _ = eP.inv ≫
          (pullback.snd f h ≫ Scheme.puncturedSpectrumInclusion C) := by
        rw [← Category.assoc eY.inv, heY]
      _ = _ := hb.isoPullback_inv_snd
  obtain ⟨Z, ⟨eZ⟩⟩ := exists_finiteEtale_extension_of_flat_baseChange
    (Scheme.puncturedSpectrumOpen R) f g p j hj
  exact ⟨Z, ⟨eZ⟩⟩

end EtaleFundamentalGroups
