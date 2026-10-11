/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalPrimePair
import Nyll.SchemeTheory.Affine.PrimePairHartogs
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RingHom.Flat

/-!
# Global sections of punctured finite étale covers

On a finite étale scheme over a regular local ring of dimension at least
two, restriction to the inverse image of the puncture preserves all global
sections. The proof uses the actual flat algebra of global sections and
the prime parameters supplied by regularity.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- Hartogs extension for the actual punctured open of a finite étale cover. -/
theorem restrict_punctured_finiteEtale_bijective
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : 2 ≤ ringKrullDim R)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsFiniteEtale p] :
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
  obtain ⟨x, y, hxmem, hymem, hx, hy, hxy⟩ :=
    exists_primePair_of_isRegularLocalRing R hdim
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
  apply restrict_bijective_of_primePair X hx hy hxy
    (p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R)
    (NoetherianSpace.isCompact _) ?_ (hbasic hxmem) (hbasic hymem)
  intro A B _ _ _ _ _ _
  exact NoetherianSpace.isCompact _

/-- The punctured inclusion induces an isomorphism on its actual global
section objects, including the open-subscheme restriction identification. -/
theorem isIso_punctured_finiteEtale_inclusion_appTop
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : 2 ≤ ringKrullDim R)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsFiniteEtale p] :
    IsIso (p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R).ι.appTop := by
  let V := p ⁻¹ᵁ Scheme.puncturedSpectrumOpen R
  have hcomp : V.ι.appTop ≫ V.topIso.hom =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    change X.presheaf.map (homOfLE
      (show V.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
      X.presheaf.map (eqToHom V.ι_image_top.symm).op = _
    rw [← Functor.map_comp]
    congr 1
  have hbij := restrict_punctured_finiteEtale_bijective R hdim p
  let : IsIso (V.ι.appTop ≫ V.topIso.hom) := by
    rw [hcomp, ConcreteCategory.isIso_iff_bijective]
    exact hbij
  exact IsIso.of_isIso_comp_right V.ι.appTop V.topIso.hom

end EtaleFundamentalGroups
