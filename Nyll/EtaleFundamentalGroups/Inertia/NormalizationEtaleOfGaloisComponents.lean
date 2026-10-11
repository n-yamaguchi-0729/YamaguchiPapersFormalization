/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationComponentPoint
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étaleness from the actual normalized Galois components

Every normalization point lifts to a normalized component of the pulled-back
cover. These component inclusions are open immersions, and therefore supply
an actual open cover on which étaleness can be checked.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Étaleness of every pointed normalized Galois component implies étaleness
of the actual normalization of the entire pulled-back cover. -/
theorem etale_normalization_of_galoisComponents
    {U V S : Scheme.{u}} [ConnectedSpace U] [ConnectedSpace V]
    (b : U ⟶ V) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) (W : FiniteEtale V) (hW : IsGalois W)
    (f : ((FiniteEtale.pullback b).obj W).left ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hcomponent : ∀ (w : (fiber (xi ≫ b)).obj W)
      (Z : FiniteEtale U) (i : Z ⟶ (FiniteEtale.pullback b).obj W)
      (v : (fiber xi).obj Z),
      (fiber xi).map i v = transportedPointOfCompIso (FiniteEtale.pullback b)
        (pullbackFiberIso b xi) W w →
      IsGalois Z → Mono i → Etale (i.left ≫ f).fromNormalization) :
    Etale f.fromNormalization := by
  have hlocal : ∀ x : f.normalization,
      ∃ (N : Scheme.{u}) (j : N ⟶ f.normalization),
        IsOpenImmersion j ∧ x ∈ Set.range j ∧ Etale (j ≫ f.fromNormalization) := by
    intro x
    let q := f.normalization.fromSpecResidueField x
    obtain ⟨Z, i, qZ, v, w, hi, hZ, hq, hv⟩ :=
      exists_galoisNormalizationComponent_geometricPoint b xi W hW f q
    let : Mono i := hi
    let j := normalizationComponentInclusion f i
    have hbase : j ≫ f.fromNormalization = (i.left ≫ f).fromNormalization :=
      Scheme.Hom.normalizationDesc_comp _ _ _ _
    refine ⟨(i.left ≫ f).normalization, j, inferInstance, ?_, ?_⟩
    · let t : Spec (f.normalization.residueField x) := Classical.choice inferInstance
      refine ⟨qZ t, ?_⟩
      exact (congrArg (fun k => k t) hq).trans
        (Scheme.fromSpecResidueField_apply x t)
    · rw [hbase]
      exact hcomponent w Z i v hv hZ hi
  choose N j hj hcover hEtale using hlocal
  let cover : f.normalization.OpenCover :=
    { I₀ := f.normalization
      X := N
      f := j
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => ⟨x, hcover x⟩, hj⟩ }
  exact IsZariskiLocalAtSource.of_openCover (P := @Etale) cover hEtale

end EtaleFundamentalGroups.Inertia
