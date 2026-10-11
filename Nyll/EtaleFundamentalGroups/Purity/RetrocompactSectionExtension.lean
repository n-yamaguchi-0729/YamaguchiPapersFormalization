/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.ClosedComplementStalkSection
import Nyll.SchemeTheory.Descent.RetrocompactAffineChartStalkSpreading
import Nyll.SchemeTheory.Etale.MaximalSectionExtension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Global section extension over a retrocompact dense open

Every missing point is closed, so the original open pulls back to its
actual local puncture. Connectedness of the punctured strict stalk gives
a local section; retrocompact compatible spreading gives a neighborhood
section. The already constructed maximum extension therefore covers X.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicGeometry.FiniteEtale

/-- Finite etale sections extend globally under the original hypotheses
of Stacks 0BSA, without any finite-component or Noetherian hypothesis. -/
theorem exists_section_of_retrocompact_closed_complement
    {X Y : Scheme.{u}}
    (U : X.Opens) [QuasiCompact U.ι] (hU : Dense (U : Set X))
    (hclosed : ∀ x : X, x ∉ U → IsClosed ({x} : Set X))
    (Ω : X → Type u) [∀ x : X, Field (Ω x)] [∀ x : X, IsSepClosed (Ω x)]
    (φ : ∀ x : X, X.presheaf.stalk x →+* Ω x) [∀ x : X, IsLocalHom (φ x)]
    (hconn : ∀ x : X, x ∉ U → ConnectedSpace (Scheme.puncturedSpectrum
      (geometricStalk (Spec.map (CommRingCat.ofHom (φ x))))))
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (s : U.toScheme ⟶ Y) (hs : s ≫ f = U.ι) :
    ∃ t : X ⟶ Y, t ≫ f = 𝟙 X ∧ U.ι ≫ t = s := by
  obtain ⟨V, hUV, b, hbf, hbu, hmax⟩ :=
    Etale.exists_maximal_open_section_extension f U hU s hs
  have hV : V = ⊤ := by
    apply top_unique
    intro z _
    by_contra hzV
    have hzU : z ∉ U := fun hz => hzV (hUV hz)
    have : ConnectedSpace (Scheme.puncturedSpectrum
        (geometricStalk (Spec.map (CommRingCat.ofHom (φ z))))) := hconn z hzU
    obtain ⟨a, haf, has⟩ :=
      exists_stalk_section_of_closed_complement U hclosed z hzU (φ z) f s hs
    obtain ⟨A, hA, hzA, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := z) trivial
    obtain ⟨W, hzW, c, hcf, hcs⟩ :=
      Scheme.exists_compatible_open_extension_fromSpecStalk_of_quasiCompact_affineNeighborhood
        f U s hs z A hA hzA a haf has
    exact hzV ((hmax W c hcf hcs) hzW)
  let e : V.toScheme ≅ X := X.isoOfEq hV ≪≫ X.topIso
  have he : e.hom = V.ι := X.isoOfEq_hom_ι hV
  let t : X ⟶ Y := e.inv ≫ b
  have htf : t ≫ f = 𝟙 X := by
    change (e.inv ≫ b) ≫ f = 𝟙 X
    rw [Category.assoc, hbf, ← he, e.inv_hom_id]
  have hUi : U.ι ≫ e.inv = X.homOfLE hUV := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, he, Scheme.homOfLE_ι]
  refine ⟨t, htf, ?_⟩
  change U.ι ≫ (e.inv ≫ b) = s
  rw [← Category.assoc, hUi, hbu]

end AlgebraicGeometry.FiniteEtale
