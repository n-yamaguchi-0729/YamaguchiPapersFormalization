/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryLocalEtale
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationEtaleOfGaloisComponents
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Nyll.EtaleFundamentalGroups.Inertia.CartierLocalFractionFieldPullback
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization

/-!
# Étaleness of the actual normalization over a generic boundary stalk

The normalized local Galois components cover the normalization of the whole
fraction-field pullback. The actual Cartier-complement pullback and
normalization-localization isomorphisms then identify this with the base
change of the original cover's relative normalization to the DVR stalk.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]
  (D : X.EffectiveCartierDivisor) (E : Component D)
  [IsDomain (X.presheaf.stalk (componentPoint D E))]
  [IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E))]
  [ConnectedSpace D.1.supportComplement]

local notation "R" => X.presheaf.stalk (componentPoint D E)
local notation "K" => FractionRing R
local notation "c" =>
  Scheme.IdealSheafData.IsEffectiveCartier.fractionStalkToSupportComplement
    (Subtype.property D) (componentPoint D E)
local notation "a₀" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The normalization of the entire fraction-stalk pullback is étale over
the generic boundary DVR, without selecting a component in the conclusion. -/
theorem boundaryUnramified_fractionPullback_normalization_etale
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W) :
    Etale (((show ((FiniteEtale.pullback c).obj W).left ⟶ Spec (.of K) from
      ((FiniteEtale.pullback c).obj W).hom) ≫ a₀).fromNormalization) := by
  let xi : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let A := (FiniteEtale.pullback c).obj W
  let f : A.left ⟶ Spec (.of R) := (show A.left ⟶ Spec (.of K) from A.hom) ≫ a₀
  apply etale_normalization_of_galoisComponents c xi W hW f
  intro w Z i v hiv hZ hi
  have hZet : Etale (((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀).fromNormalization) :=
    boundaryUnramified_localComponent_normalization_etale D E xi W hW hU w Z i v hiv hZ hi
  have hiw : i.left ≫ (show A.left ⟶ Spec (.of K) from A.hom) =
      (show Z.left ⟶ Spec (.of K) from Z.hom) := i.w
  have he : (Iso.refl Z.left).hom ≫ ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀) =
      i.left ≫ f := by
    exact (Category.id_comp _).trans
      ((congrArg (fun k => k ≫ a₀) hiw).symm.trans (Category.assoc _ _ _))
  let e := normalizationSourceIso (i.left ≫ f)
    ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀) (Iso.refl Z.left) he
  have ht : Etale (e.hom ≫ ((show Z.left ⟶ Spec (.of K) from Z.hom) ≫ a₀).fromNormalization) :=
    inferInstance
  rw [normalizationSourceIso_hom_fromNormalization] at ht
  exact ht

/-- The actual base change of the original relative normalization to the
generic boundary DVR is étale. No comparison isomorphism is an input. -/
theorem boundaryUnramified_normalization_stalk_etale
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W) :
    Etale (Limits.pullback.snd
      (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (X.fromSpecStalk (componentPoint D E))) := by
  let A := (FiniteEtale.pullback c).obj W
  let F : W.left ⟶ X := W.hom ≫ D.1.supportComplement.ι
  let b : Spec (.of R) ⟶ X := X.fromSpecStalk (componentPoint D E)
  let f : A.left ⟶ Spec (.of R) := (show A.left ⟶ Spec (.of K) from A.hom) ≫ a₀
  have hx : componentPoint D E ∈ D.1.support :=
    D.1.range_subschemeι.le ⟨E.property.1.genericPoint, rfl⟩
  have H : IsPullback (Limits.pullback.fst W.hom c) f F b :=
    (IsPullback.of_hasPullback W.hom c).paste_vert
      (D.2.isPullback_fractionStalkToSupportComplement (componentPoint D E) hx)
  let e : Limits.pullback F b ≅ A.left :=
    (IsPullback.of_hasPullback F b).isoIsPullback _ _ H
  have he : e.hom ≫ f = Limits.pullback.snd F b :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec (.of R))
      (IsPullback.of_hasPullback F b) H
  let en := normalizationSourceIso (Limits.pullback.snd F b) f e he
  have hf : Etale f.fromNormalization :=
    boundaryUnramified_fractionPullback_normalization_etale D E W hW hU
  have hPB : Etale (Limits.pullback.snd F b).fromNormalization := by
    have ht : Etale (en.hom ≫ f.fromNormalization) := inferInstance
    rw [normalizationSourceIso_hom_fromNormalization] at ht
    exact ht
  let : IsIso (F.normalizationPullback b) :=
    isIso_normalizationPullback_fromSpecStalk F (componentPoint D E)
  have heq : Limits.pullback.snd F.fromNormalization b =
      inv (F.normalizationPullback b) ≫ (Limits.pullback.snd F b).fromNormalization := by
    exact (IsIso.inv_hom_id_assoc (F.normalizationPullback b)
      (Limits.pullback.snd F.fromNormalization b)).symm.trans
        (congrArg (fun k => inv (F.normalizationPullback b) ≫ k)
          (Scheme.Hom.normalizationPullback_snd F b))
  change Etale (Limits.pullback.snd F.fromNormalization b)
  rw [heq]
  infer_instance

end Yamaguchi26SolvableCoverings
