/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryHeightOneEtale
import Nyll.SchemeTheory.Divisors.StalkAwayComplement
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationComponent
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Height-one étaleness of actual normalized stalk components

The principal complement square identifies the actual pulled-back finite
cover. Normalization commutes with the stalk base change, and normalized
component inclusions are open immersions. These comparisons transport the
height-one étaleness of the global normalization to each chosen component.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

private theorem etale_pullback_snd_source_comp
    {J N X T : Scheme.{0}} (g : N ⟶ X) (b : T ⟶ X) (j : J ⟶ N)
    [Etale (pullback.snd g b)] [Etale j] :
    Etale (pullback.snd (j ≫ g) b) := by
  let e := pullbackRightPullbackFstIso g b j
  have ht : Etale (e.inv ≫ pullback.snd j (pullback.fst g b) ≫ pullback.snd g b) :=
    inferInstance
  exact (pullbackRightPullbackFstIso_inv_snd_snd g b j) ▸ ht

private theorem etale_iterated_pullback_snd
    {N X S T : Scheme.{0}} (g : N ⟶ X) (b : S ⟶ X) (a : T ⟶ S)
    [Etale (pullback.snd g (a ≫ b))] :
    Etale (pullback.snd (pullback.snd g b) a) := by
  let e := pullbackLeftPullbackSndIso g b a
  have ht : Etale (e.hom ≫ pullback.snd g (a ≫ b)) := inferInstance
  exact (pullbackLeftPullbackSndIso_hom_snd g b a) ▸ ht

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- Every actual finite-etale component of the principal stalk pullback has
étale normalization after base change to a height-one boundary prime. The
component need only be a monomorphism of covers. -/
theorem normalization_stalkComponent_heightOne_etale_of_componentStalks
    (D : X.EffectiveCartierDivisor) (W : FiniteEtale D.1.supportComplement)
    (hgeneric : ∀ E : Component D,
      Etale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
        (X.fromSpecStalk (componentPoint D E))))
    (x : X) (d : X.presheaf.stalk x) (hd : D.1.stalkIdeal x = Ideal.span {d})
    [ConnectedSpace (Spec (.of (Localization.Away d)))]
    (Y : FiniteEtale (Spec (.of (Localization.Away d))))
    (i : Y ⟶ (FiniteEtale.pullback
      (D.1.stalkAwayToSupportComplement x d hd)).obj W) [Mono i]
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hp : p.height = 1) (hDp : D.1.stalkIdeal x ≤ p) :
    Etale (pullback.snd
      ((show Y.left ⟶ Spec (.of (Localization.Away d)) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) (Localization.Away d)))).fromNormalization
      (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p))))) := by
  let c := D.1.stalkAwayToSupportComplement x d hd
  let A := (FiniteEtale.pullback c).obj W
  let a := Spec.map (CommRingCat.ofHom
    (algebraMap (X.presheaf.stalk x) (Localization.Away d)))
  let b := X.fromSpecStalk x
  let ap := Spec.map (CommRingCat.ofHom
    (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p)))
  let F : W.left ⟶ X := W.hom ≫ D.1.supportComplement.ι
  let f : A.left ⟶ Spec (X.presheaf.stalk x) :=
    (show A.left ⟶ Spec (.of (Localization.Away d)) from A.hom) ≫ a
  have H : IsPullback (pullback.fst W.hom c) f F b :=
    (IsPullback.of_hasPullback W.hom c).paste_vert
      (D.1.isPullback_stalkAwayToSupportComplement x d hd)
  let e : pullback F b ≅ A.left := (IsPullback.of_hasPullback F b).isoIsPullback _ _ H
  have he : e.hom ≫ f = pullback.snd F b :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec (X.presheaf.stalk x))
      (IsPullback.of_hasPullback F b) H
  let en := normalizationSourceIso (pullback.snd F b) f e he
  let : IsIso (F.normalizationPullback b) := isIso_normalizationPullback_fromSpecStalk F x
  let ef : f.normalization ≅ pullback F.fromNormalization b :=
    en.symm ≪≫ asIso (F.normalizationPullback b)
  have hef : ef.hom ≫ pullback.snd F.fromNormalization b = f.fromNormalization := by
    change (en.inv ≫ F.normalizationPullback b) ≫ pullback.snd F.fromNormalization b = _
    rw [Category.assoc, Scheme.Hom.normalizationPullback_snd]
    exact (Iso.inv_comp_eq en).mpr (normalizationSourceIso_hom_fromNormalization _ _ _ _).symm
  let j := normalizationComponentInclusion f i
  have hj : j ≫ f.fromNormalization = (i.left ≫ f).fromNormalization :=
    Scheme.Hom.normalizationDesc_comp _ _ _ _
  let m := j ≫ ef.hom
  have hm : m ≫ pullback.snd F.fromNormalization b = (i.left ≫ f).fromNormalization := by
    change (j ≫ ef.hom) ≫ pullback.snd F.fromNormalization b = _
    rw [Category.assoc, hef]
    exact hj
  have hglobal : Etale (pullback.snd F.fromNormalization (ap ≫ b)) :=
    normalization_heightOne_etale_of_componentStalks D W hgeneric x p hp hDp
  have hwhole : Etale (pullback.snd (pullback.snd F.fromNormalization b) ap) :=
    etale_iterated_pullback_snd F.fromNormalization b ap
  have hcomponent : Etale (pullback.snd (i.left ≫ f).fromNormalization ap) := by
    have ht : Etale (pullback.snd (m ≫ pullback.snd F.fromNormalization b) ap) :=
      etale_pullback_snd_source_comp (pullback.snd F.fromNormalization b) ap m
    exact Eq.mp (congrArg (fun k => Etale (pullback.snd k ap)) hm) ht
  have hi : i.left ≫ f = (show Y.left ⟶ Spec (.of (Localization.Away d)) from Y.hom) ≫ a :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ a) i.w)
  exact Eq.mp (congrArg (fun k : Y.left ⟶ Spec (X.presheaf.stalk x) =>
    Etale (pullback.snd k.fromNormalization ap)) hi) hcomponent

/-- Every actual finite-etale component of the principal stalk pullback has
étale normalization after base change to a height-one boundary prime. The
component need only be a monomorphism of covers. -/
theorem boundaryUnramified_stalkComponent_normalization_heightOne_etale
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W)
    (x : X) (d : X.presheaf.stalk x) (hd : D.1.stalkIdeal x = Ideal.span {d})
    [ConnectedSpace (Spec (.of (Localization.Away d)))]
    (Y : FiniteEtale (Spec (.of (Localization.Away d))))
    (i : Y ⟶ (FiniteEtale.pullback
      (D.1.stalkAwayToSupportComplement x d hd)).obj W) [Mono i]
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hp : p.height = 1) (hDp : D.1.stalkIdeal x ≤ p) :
    Etale (pullback.snd
      ((show Y.left ⟶ Spec (.of (Localization.Away d)) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) (Localization.Away d)))).fromNormalization
      (Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p))))) := by
  exact normalization_stalkComponent_heightOne_etale_of_componentStalks D W
    (boundaryUnramified_normalization_componentStalk_etale D hreg W hW hU)
    x d hd Y i p hp hDp

end Yamaguchi26SolvableCoverings
