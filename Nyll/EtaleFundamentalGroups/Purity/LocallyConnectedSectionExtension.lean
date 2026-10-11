/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.GenericComplementStalkSection
import Nyll.SchemeTheory.Descent.AffineChartCompatibleStalkSpreading
import Nyll.SchemeTheory.Etale.MaximalSectionExtension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sober

/-!+# Finite etale section extension from punctured strict-stalk connectedness

For a scheme whose quasi-compact opens have finitely many irreducible
components, a finite etale section on a dense open extends globally when
the punctured strict stalk at each missing point is connected. A maximum
extension is constructed by gluing, and a generic complement point would
produce a larger compatible neighborhood, a contradiction.

The strict stalks are the existing geometric stalks for arbitrary chosen
separably closed residue geometric points. No reducedness, normality,
Noetherianity of rings, or retrocompactness of the dense open is imposed.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicGeometry.FiniteEtale

/-- The actual global finite etale section extension used for Stacks 0BQG,
and hence for the topologically Noetherian statement 0BQF. -/
theorem exists_section_of_connected_punctured_strict_stalks
    {X Y : Scheme.{u}}
    (hfin : ∀ A : X.Opens, IsCompact (A : Set X) →
      (irreducibleComponents A.toScheme).Finite)
    (U : X.Opens) (hU : Dense (U : Set X))
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
    let zC : {z : X // z ∉ V} := ⟨z, hzV⟩
    have hclosed : IsClosed {z : X | z ∉ V} := V.isOpen.isClosed_compl
    have : QuasiSober {z : X // z ∉ V} :=
      hclosed.isClosedEmbedding_subtypeVal.quasiSober
    let Z : irreducibleComponents {z : X // z ∉ V} :=
      ⟨irreducibleComponent zC, irreducibleComponent_mem_irreducibleComponents zC⟩
    let ξ : genericPoints {z : X // z ∉ V} := genericPoints.ofComponent Z
    have hξU : ξ.1.1 ∉ U := fun h => ξ.1.2 (hUV h)
    have : ConnectedSpace (Scheme.puncturedSpectrum
        (geometricStalk (Spec.map (CommRingCat.ofHom (φ ξ.1.1))))) := hconn ξ.1.1 hξU
    obtain ⟨a, haf, hab⟩ :=
      exists_stalk_section_of_generic_complement V ξ (φ ξ.1.1) f b hbf
    obtain ⟨A, hA, hξA, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := ξ.1.1) trivial
    obtain ⟨W, hξW, c, hcf, hcb⟩ :=
      Scheme.exists_compatible_open_extension_fromSpecStalk_of_affineNeighborhood
        f V b hbf ξ.1.1 A hA hξA (hfin A hA.isCompact) a haf hab
    have hcu : X.homOfLE (show U ⊓ W ≤ U from inf_le_left) ≫ s =
        X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ c := by
      have hUWVW : U ⊓ W ≤ V ⊓ W := inf_le_inf hUV le_rfl
      have h := congrArg
        (fun m : (V ⊓ W).toScheme ⟶ Y => X.homOfLE hUWVW ≫ m) hcb
      have h' : X.homOfLE (show U ⊓ W ≤ V from inf_le_left.trans hUV) ≫ b =
          X.homOfLE (show U ⊓ W ≤ W from inf_le_right) ≫ c := by
        simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using h
      rw [← hbu, ← Category.assoc, Scheme.homOfLE_homOfLE]
      exact h'
    exact ξ.1.2 ((hmax W c hcf hcu) hξW)
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
