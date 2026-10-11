/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat


/-!
# Faithful flatness of an actual pointed affine étale neighborhood

An affine étale neighborhood of the closed geometric point of a local ring is
faithfully flat over that ring. The actual evaluation map to the chosen field
shows that the image of the maximal ideal remains proper. Together with
étaleness of the neighborhood this is the ideal criterion for faithful flatness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The actual sections map of a pointed affine étale neighborhood is étale
and faithfully flat over the local base ring. -/
theorem affineNeighborhood_structure_etale_faithfullyFlat
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) [IsLocalHom φ]
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
    [IsAffine V.left] :
    let β := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
    β.Etale ∧ β.FaithfullyFlat := by
  let β : R →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  let : IsAffine ((𝟭 Scheme).obj V.left) := inferInstanceAs (IsAffine V.left)
  let : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of R))).obj V.right) := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  have hβ : β.Etale := by
    change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
          inferInstance)
    · exact HasRingHomProperty.appTop (P := @Etale) V.hom inferInstance
  refine ⟨hβ, ?_⟩
  let : Algebra R Γ(V.left, ⊤) := β.toAlgebra
  let : Algebra.Etale R Γ(V.left, ⊤) := hβ
  let s := Spec.map (CommRingCat.ofHom φ)
  let g : Γ(V.left, ⊤) →+* Ω :=
    (geometricStalkEvaluation s).hom.comp (geometricStalkGerm s V v).hom
  have hg : g.comp β = φ := by
    let γ : Γ(V.left, ⊤) →+* geometricStalk s := (geometricStalkGerm s V v).hom
    let ε : geometricStalk s →+* Ω := (geometricStalkEvaluation s).hom
    have hγ : γ.comp β = geometricStalkStructureMap φ :=
      geometricStalkGerm_comp_structure φ V v
    exact (RingHom.comp_assoc β γ ε).trans
      ((congrArg (fun k : R →+* geometricStalk s => ε.comp k) hγ).trans
        (geometricStalkStructureMap_evaluation φ))
  change Module.FaithfullyFlat R Γ(V.left, ⊤)
  refine ⟨fun m hm => ?_⟩
  rw [Ideal.smul_top_eq_map]
  intro htop
  have hker : m ≤ RingHom.ker (g.comp β) := by
    intro r hr
    rw [RingHom.mem_ker, hg]
    by_contra hn
    have hu : IsUnit r := (inferInstance : IsLocalHom φ).map_nonunit r
      (isUnit_iff_ne_zero.mpr hn)
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hr hu)
  have hle : Ideal.map β m ≤ RingHom.ker g := Ideal.map_le_iff_le_comap.mpr hker
  have htop' : Ideal.map β m = ⊤ :=
    (Submodule.restrictScalars_eq_top_iff R _ _).mp htop
  rw [htop', top_le_iff] at hle
  exact RingHom.ker_ne_top g hle

end EtaleFundamentalGroups.StrictHenselian
