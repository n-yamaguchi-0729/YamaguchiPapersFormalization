/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.RegularPairHartogs
import Nyll.SchemeTheory.RingTheory.DepthTwoRegularPair
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RingHom.Flat

/-!
# Global sections over punctures of depth at least two

The actual restriction map on a finite flat scheme over a Noetherian local
ring of depth at least two is an isomorphism. A regular pair in the base
stays regular in its flat section algebra, so Hartogs extension applies.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing RingTheory

namespace EtaleFundamentalGroups

universe u

/-- Hartogs extension for finite flat covers of a local spectrum of depth
at least two. -/
theorem restrict_punctured_finiteFlat_bijective_of_two_le_depth
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsFinite p] [Flat p] :
    Function.Bijective (X.presheaf.map
      (homOfLE (show p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R ≤ ⊤ from le_top)).op) := by
  let : IsAffine X := isAffine_of_isAffineHom p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let : NoetherianSpace X := noetherianSpace_of_isAffine (X := X)
  let c : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop
  let : Algebra R Γ(X, ⊤) := c.hom.toAlgebra
  let : Module.Flat R Γ(X, ⊤) :=
    (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)).comp
      p.flat_appTop
  obtain ⟨x, hxmem, y, hymem, hxy, hyx⟩ :=
    SchemeTheory.exists_regular_pair_of_two_le_depth R hdepth
  have transfer (rs : List R) (h : Sequence.IsWeaklyRegular R rs) :
      Sequence.IsWeaklyRegular Γ(X, ⊤) (rs.map (algebraMap R Γ(X, ⊤))) := by
    apply (Sequence.isWeaklyRegular_map_algebraMap_iff Γ(X, ⊤) Γ(X, ⊤) rs).mpr
    exact ((TensorProduct.lid R Γ(X, ⊤)).isWeaklyRegular_congr rs).mp
      h.isWeaklyRegular_rTensor
  have hxy' := transfer [x, y] hxy
  have hyx' := transfer [y, x] hyx
  simp only [List.map_cons, List.map_nil, Sequence.isWeaklyRegular_cons_iff] at hxy' hyx'
  have hbasic {r : R} (hr : r ∈ maximalIdeal R) :
      X.basicOpen (algebraMap R Γ(X, ⊤) r) ≤
        p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R := by
    change X.basicOpen (p.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) ≤ _
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    apply Scheme.Hom.preimage_mono p
    intro q hq
    apply (Scheme.mem_puncturedSpectrumOpen_iff R q).mpr
    intro hqclosed
    subst q
    exact hq hr
  apply restrict_bijective_of_regular_pair X
    (algebraMap R Γ(X, ⊤) x) (algebraMap R Γ(X, ⊤) y)
    hxy'.1 hyx'.1 hxy'.2.1
    (p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R)
    (NoetherianSpace.isCompact _) ?_ (hbasic hxmem) (hbasic hymem)
  intro A B _ _ _ _ _ _
  exact NoetherianSpace.isCompact _

/-- The open immersion over the puncture preserves the actual global
section object of a finite flat cover. -/
theorem isIso_punctured_finiteFlat_inclusion_appTop_of_two_le_depth
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsFinite p] [Flat p] :
    IsIso (p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R).ι.appTop := by
  let V := p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R
  have hcomp : V.ι.appTop ≫ V.topIso.hom =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    change X.presheaf.map (homOfLE
      (show V.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
      X.presheaf.map (eqToHom V.ι_image_top.symm).op = _
    rw [← Functor.map_comp]
    congr 1
  let : IsIso (V.ι.appTop ≫ V.topIso.hom) := by
    rw [hcomp, ConcreteCategory.isIso_iff_bijective]
    exact restrict_punctured_finiteFlat_bijective_of_two_le_depth R hdepth p
  exact IsIso.of_isIso_comp_right V.ι.appTop V.topIso.hom

end EtaleFundamentalGroups
