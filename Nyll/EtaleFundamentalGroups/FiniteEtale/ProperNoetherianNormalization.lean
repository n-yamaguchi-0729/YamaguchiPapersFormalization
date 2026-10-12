/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperNoetherianSectionAlgebra
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.Morphisms.ProperNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.RingHom.Finite

/-!
# The finite étale factor of a proper reduced family

For a proper flat geometrically reduced family over a locally Noetherian
scheme, the actual native relative normalization has finite étale second
map. On an affine base this follows from the computed section algebra and
the actual section isomorphism of the first map. The native normalization
comparison under smooth base change then supplies the affine-open descent.

This proves the locally Noetherian case of the finite étale conclusion in
Stacks Project Tag 0BUN, using the native relative normalization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

private theorem finite_etale_appTop_of_proper_flat_affine_noetherian
    {X S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f] :
    f.appTop.hom.Finite ∧ f.appTop.hom.Etale := by
  have hNoetherian : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have hReduced : GeometricallyReduced (f ≫ S.isoSpec.hom) :=
    ((show MorphismProperty Scheme.{u} from @GeometricallyReduced).cancel_right_of_respectsIso
      f S.isoSpec.hom).mpr inferInstance
  have hIso : IsIso S.isoSpec.hom.appTop :=
    (Scheme.Γ.mapIso S.isoSpec.op).isIso_hom
  have h := finite_etale_appTop_of_proper_flat_geometricallyReduced_noetherian
    (f ≫ S.isoSpec.hom)
  rw [Scheme.Hom.comp_appTop] at h
  exact ⟨(RingHom.finite_respectsIso.cancel_left_isIso S.isoSpec.hom.appTop f.appTop).mp h.1,
    (RingHom.Etale.respectsIso.cancel_left_isIso S.isoSpec.hom.appTop f.appTop).mp h.2⟩

private theorem finite_etale_fromNormalization_of_proper_flat_affine_noetherian
    {X S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f] :
    IsFiniteEtale f.fromNormalization := by
  have h := finite_etale_appTop_of_proper_flat_affine_noetherian f
  have hApp : f.fromNormalization.appTop ≫ f.toNormalization.appTop = f.appTop := by
    rw [← Scheme.Hom.comp_appTop, f.toNormalization_fromNormalization]
  have hFinite : f.fromNormalization.appTop.hom.Finite := by
    apply (RingHom.finite_respectsIso.cancel_right_isIso
      f.fromNormalization.appTop f.toNormalization.appTop).mp
    change (f.fromNormalization.appTop ≫ f.toNormalization.appTop).hom.Finite
    rw [hApp]
    exact h.1
  have hEtale : f.fromNormalization.appTop.hom.Etale := by
    apply (RingHom.Etale.respectsIso.cancel_right_isIso
      f.fromNormalization.appTop f.toNormalization.appTop).mp
    change (f.fromNormalization.appTop ≫ f.toNormalization.appTop).hom.Etale
    rw [hApp]
    exact h.2
  exact (HasAffineProperty.iff_of_isAffine
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    (Q := affineAnd RingHom.FiniteEtale) (f := f.fromNormalization)).mpr
    ⟨inferInstance, (RingHom.FiniteEtale.iff_finite_and_etale _).mpr ⟨hEtale, hFinite⟩⟩

/-- The actual second map of relative normalization is finite étale for a
proper flat geometrically reduced family over a locally Noetherian base.
No section-algebra comparison or étaleness is supplied as an input. -/
theorem finite_etale_fromNormalization_of_proper_flat_geometricallyReduced_noetherian
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyReduced f] :
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization := by
  have hLocality : IsZariskiLocalAtTarget
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  have hIsoRespect : MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := hLocality.toRespects
  have hLocal (i : S.affineCover.I₀) :
      IsFiniteEtale (S.affineCover.pullbackHom f.fromNormalization i) := by
    let g := S.affineCover.f i
    let p := pullback.snd f g
    have hFiniteEtale := finite_etale_fromNormalization_of_proper_flat_affine_noetherian p
    let c := f.normalizationPullback g
    have hComp : c ≫ pullback.snd f.fromNormalization g = p.fromNormalization :=
      f.normalizationPullback_snd g
    have hCompEtale : IsFiniteEtale (c ≫ pullback.snd f.fromNormalization g) :=
      hComp.symm ▸ hFiniteEtale
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) c _).mp hCompEtale
  have hFiniteEtale : IsFiniteEtale f.fromNormalization :=
    (IsZariskiLocalAtTarget.iff_of_openCover
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (f := f.fromNormalization) S.affineCover).mpr hLocal
  exact ⟨hFiniteEtale.toIsFinite, hFiniteEtale.toEtale⟩

end AlgebraicGeometry
