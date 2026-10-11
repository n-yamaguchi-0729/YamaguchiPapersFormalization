/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncture
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import SchemeTheory.FiniteEtale.StrictLocalSections
import SchemeTheory.LocalGeometry.PuncturedSpectrum
import SchemeTheory.LocalGeometry.PuncturedSpectrumFlat
import SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-!
# Descent of finite étale sections from the actual punctured strict stalk

If the puncture of the actual geometric étale stalk of a local ring is
connected, every finite étale section on the original puncture extends
uniquely over the original local spectrum. The extension is first built
over the actual strictly local stalk. Its two restrictions to the fpqc
double overlap agree on a dense open obtained by flat going-down. The
unramified separated equalizer makes them equal on the entire overlap, so
the native fpqc effective epimorphism descends the actual section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Connectedness of the actual punctured strict stalk gives unique extension
of finite étale sections over the punctured local spectrum. -/
theorem existsUnique_section_of_connected_geometricStalk_puncture
    {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) [IsLocalHom φ]
    [ConnectedSpace
      (Scheme.puncturedSpectrum (geometricStalk (Spec.map (CommRingCat.ofHom φ))))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f] [Etale f]
    (s : Scheme.puncturedSpectrum R ⟶ X)
    (hs : s ≫ f = Scheme.puncturedSpectrumInclusion R) :
    ∃! t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Scheme.puncturedSpectrumInclusion R ≫ t = s := by
  let H : Type u := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let hRing : CommRing H := (geometricStalk (Spec.map (CommRingCat.ofHom φ))).commRing
  have hHenselian : HenselianLocalRing H :=
    geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom φ))
  have hResidue : IsSepClosed (IsLocalRing.ResidueField H) :=
    geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom φ))
  let π : Spec (.of H) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let jR : Scheme.puncturedSpectrum R ⟶ Spec (.of R) :=
    Scheme.puncturedSpectrumInclusion R
  let jH : Scheme.puncturedSpectrum H ⟶ Spec (.of H) := Scheme.puncturedSpectrumInclusion H
  let e : pullback π jR ≅ Scheme.puncturedSpectrum H :=
    geometricStalkPuncturedSpectrumPullbackIso φ
  have hej : e.hom ≫ jH = pullback.fst π jR :=
    geometricStalkPuncturedSpectrumPullbackIso_hom_inclusion φ
  have heij : e.inv ≫ pullback.fst π jR = jH := by
    rw [← hej, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let q : Scheme.puncturedSpectrum H ⟶ Scheme.puncturedSpectrum R :=
    e.inv ≫ pullback.snd π jR
  have hq : q ≫ jR = jH ≫ π := by
    change (e.inv ≫ pullback.snd π jR) ≫ jR = jH ≫ π
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, heij]
  have hflatSurj : Flat π ∧ Surjective π :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (geometricStalkStructureMap φ))).mpr
        (geometricStalkStructureMap_faithfullyFlat φ)
  have : Flat π := hflatSurj.1
  have : Surjective π := hflatSurj.2
  have : QuasiCompact π := inferInstance
  have : Flat q := by change Flat (e.inv ≫ pullback.snd π jR); infer_instance
  have : Surjective q := by change Surjective (e.inv ≫ pullback.snd π jR); infer_instance
  have : QuasiCompact q := by change QuasiCompact (e.inv ≫ pullback.snd π jR); infer_instance
  let sH : Scheme.puncturedSpectrum H ⟶ pullback f π :=
    pullback.lift (q ≫ s) jH (by rw [Category.assoc, hs]; exact hq)
  let pH : pullback f π ⟶ Spec (.of H) := pullback.snd f π
  have hsH : sH ≫ pH = jH := pullback.lift_snd _ _ _
  obtain ⟨σ, hσ, hσunique⟩ :=
    AlgebraicGeometry.FiniteEtale.existsUnique_section_of_connected_of_strictHenselian
      H pH jH sH hsH
  let a : Spec (.of H) ⟶ X := σ ≫ pullback.fst f π
  have ha : a ≫ f = π := by
    change (σ ≫ pullback.fst f π) ≫ f = π
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ.1, Category.id_comp]
  have haj : jH ≫ a = q ≫ s := by
    change jH ≫ (σ ≫ pullback.fst f π) = q ≫ s
    rw [← Category.assoc, hσ.2]
    exact pullback.lift_fst _ _ _
  let d₁ : pullback π π ⟶ Spec (.of H) := pullback.fst π π
  let d₂ : pullback π π ⟶ Spec (.of H) := pullback.snd π π
  let k : pullback d₁ jH ⟶ pullback π π := pullback.fst d₁ jH
  let l : pullback d₁ jH ⟶ Scheme.puncturedSpectrum H := pullback.snd d₁ jH
  have hkd₁ : k ≫ d₁ = l ≫ jH := pullback.condition
  have hd : d₁ ≫ π = d₂ ≫ π := pullback.condition
  have hkd₂ : (k ≫ d₂) ≫ π = (l ≫ q) ≫ jR := by
    rw [Category.assoc, ← hd, ← Category.assoc, hkd₁,
      Category.assoc, ← hq, ← Category.assoc]
  let b : pullback d₁ jH ⟶ pullback π jR :=
    pullback.lift (k ≫ d₂) (l ≫ q) hkd₂
  let l₂ : pullback d₁ jH ⟶ Scheme.puncturedSpectrum H := b ≫ e.hom
  have hl₂j : l₂ ≫ jH = k ≫ d₂ := by
    change (b ≫ e.hom) ≫ jH = k ≫ d₂
    rw [Category.assoc, hej]
    exact pullback.lift_fst _ _ _
  have hl₂q : l₂ ≫ q = l ≫ q := by
    change (b ≫ e.hom) ≫ (e.inv ≫ pullback.snd π jR) = l ≫ q
    rw [Category.assoc, ← Category.assoc e.hom e.inv, e.hom_inv_id, Category.id_comp]
    exact pullback.lift_snd _ _ _
  have hlocal : k ≫ (d₁ ≫ a) = k ≫ (d₂ ≫ a) := by
    calc
      k ≫ (d₁ ≫ a) = l ≫ (jH ≫ a) := by rw [← Category.assoc, hkd₁, Category.assoc]
      _ = (l ≫ q) ≫ s := by rw [haj, ← Category.assoc]
      _ = (l₂ ≫ q) ≫ s := congrArg (fun z => z ≫ s) hl₂q.symm
      _ = l₂ ≫ (jH ≫ a) := by rw [Category.assoc, ← haj]
      _ = k ≫ (d₂ ≫ a) := by rw [← Category.assoc, hl₂j, Category.assoc]
  have : Flat d₁ := inferInstanceAs (Flat (pullback.fst π π))
  have : IsDominant k := by
    constructor
    change Dense (Set.range (pullback.fst d₁ jH))
    rw [Scheme.Pullback.range_fst]
    change Dense (d₁ ⁻¹' Set.range (Scheme.puncturedSpectrumOpen H).ι)
    rw [Scheme.Opens.range_ι]
    exact Scheme.dense_preimage_puncturedSpectrumOpen_of_flat H d₁
  have hoverlap : d₁ ≫ a = d₂ ≫ a := by
    let α : Over.mk (d₁ ≫ π) ⟶ Over.mk f :=
      Over.homMk (d₁ ≫ a) (by
        change (d₁ ≫ a) ≫ f = d₁ ≫ π
        rw [Category.assoc, ha])
    let β : Over.mk (d₁ ≫ π) ⟶ Over.mk f :=
      Over.homMk (d₂ ≫ a) (by
        change (d₂ ≫ a) ≫ f = d₁ ≫ π
        rw [Category.assoc, ha]
        exact hd.symm)
    let i : Over.mk (k ≫ (d₁ ≫ π)) ⟶ Over.mk (d₁ ≫ π) := Over.homMk k rfl
    have hi : i ≫ α = i ≫ β := Over.OverMorphism.ext hlocal
    have htargetEtale : Etale (Over.mk f).hom := inferInstanceAs (Etale f)
    have htargetFinite : IsFinite (Over.mk f).hom := inferInstanceAs (IsFinite f)
    have hsourceDominant : IsDominant i.left := inferInstanceAs (IsDominant k)
    have h := AlgebraicGeometry.Over.hom_ext_of_isDominant_of_unramified α β i hi
    exact congrArg (fun z : Over.mk (d₁ ≫ π) ⟶ Over.mk f => z.left) h
  have hcompat {Y : Scheme.{u}} (g₁ g₂ : Y ⟶ Spec (.of H)) (hg : g₁ ≫ π = g₂ ≫ π) :
      g₁ ≫ a = g₂ ≫ a := by
    have h := congrArg (fun z : pullback π π ⟶ X => pullback.lift g₁ g₂ hg ≫ z) hoverlap
    change pullback.lift g₁ g₂ hg ≫ (pullback.fst π π ≫ a) =
      pullback.lift g₁ g₂ hg ≫ (pullback.snd π π ≫ a) at h
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  let t : Spec (.of R) ⟶ X := EffectiveEpi.desc π a hcompat
  have ht : π ≫ t = a := EffectiveEpi.fac π a hcompat
  have htf : t ≫ f = 𝟙 _ := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, ht, ha, Category.comp_id]
  have htj : jR ≫ t = s := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, hq, Category.assoc, ht, haj]
  refine ⟨t, ⟨htf, htj⟩, ?_⟩
  intro τ hτ
  let τH : Spec (.of H) ⟶ pullback f π :=
    pullback.lift (π ≫ τ) (𝟙 _) (by rw [Category.assoc, hτ.1, Category.comp_id,
      Category.id_comp])
  have hτH : τH ≫ pullback.snd f π = 𝟙 _ ∧ jH ≫ τH = sH := by
    refine ⟨pullback.lift_snd _ _ _, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        ← hq, Category.assoc, hτ.2]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
      exact hsH.symm
  have hτeq : τH = σ := hσunique τH hτH
  apply (cancel_epi π).mp
  rw [ht]
  have h := congrArg (fun z : Spec (.of H) ⟶ pullback f π => z ≫ pullback.fst f π) hτeq
  exact (pullback.lift_fst _ _ _).symm.trans h

end EtaleFundamentalGroups.StrictHenselian
