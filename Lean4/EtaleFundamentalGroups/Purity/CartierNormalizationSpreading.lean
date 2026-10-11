/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PrincipalNormalizationSpreading
import EtaleFundamentalGroups.Inertia.NormalizationOpenStalk
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import SchemeTheory.Divisors.AffineComplement
import SchemeTheory.Divisors.Basic
import SchemeTheory.FiniteEtale.Basic
import SchemeTheory.Affine.ChartStalkLocalization
import SchemeTheory.RingTheory.RegularLocalTrace
import SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Spreading finite étale normalization along a Cartier boundary

Choose actual principal Cartier charts. Stalk-localization isomorphisms,
normalization under open base change, and the principal complement square
transport the given local finite étaleness to the affine normalization.
The principal spreading theorem and locality on the target then give finite
étaleness of the original relative normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups

universe u

private theorem finiteEtale_pullback_snd_comp
    {N X S T : Scheme.{u}} (g : N ⟶ X) (b : S ⟶ X) (a : T ⟶ S)
    [IsFiniteEtale (pullback.snd g b)] :
    IsFiniteEtale (pullback.snd g (a ≫ b)) := by
  let e := pullbackLeftPullbackSndIso g b a
  have ht : IsFiniteEtale (e.inv ≫ pullback.snd (pullback.snd g b) a) := ⟨⟩
  exact (pullbackLeftPullbackSndIso_inv_snd_snd g b a) ▸ ht

private theorem finiteEtale_iterated_pullback_snd
    {N X S T : Scheme.{u}} (g : N ⟶ X) (b : S ⟶ X) (a : T ⟶ S)
    [IsFiniteEtale (pullback.snd g (a ≫ b))] :
    IsFiniteEtale (pullback.snd (pullback.snd g b) a) := by
  let e := pullbackLeftPullbackSndIso g b a
  have ht : IsFiniteEtale (e.hom ≫ pullback.snd g (a ≫ b)) := ⟨⟩
  exact (pullbackLeftPullbackSndIso_hom_snd g b a) ▸ ht

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

private theorem finiteEtale_normalization_affineChart
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    (W : FiniteEtale D.1.supportComplement)
    (hboundary : ∀ x : X, x ∈ D.1.support →
      IsFiniteEtale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
        (X.fromSpecStalk x)))
    {U : X.Opens} (hU : IsAffineOpen U) (d : Γ(X, U))
    (hd : D.1.ideal ⟨U, hU⟩ = Ideal.span {d}) :
    IsFiniteEtale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      hU.fromSpec) := by
  let R := Γ(X, U)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let A := Localization.Away d
  let c := D.1.affineAwayToSupportComplement hU d hd
  let V := (FiniteEtale.pullback c).obj W
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := hU.fromSpec
  let F : W.left ⟶ X := W.hom ≫ D.1.supportComplement.ι
  let g : V.left ⟶ Spec (.of A) := V.hom
  let f : V.left ⟶ Spec R := g ≫ a
  have H : IsPullback (pullback.fst W.hom c) f F b :=
    (IsPullback.of_hasPullback W.hom c).paste_vert
      (D.1.isPullback_affineAwayToSupportComplement hU d hd)
  let e : pullback F b ≅ V.left := (IsPullback.of_hasPullback F b).isoIsPullback _ _ H
  have he : e.hom ≫ f = pullback.snd F b :=
    IsPullback.isoIsPullback_hom_snd W.left (Spec R)
      (IsPullback.of_hasPullback F b) H
  let en := normalizationSourceIso (pullback.snd F b) f e he
  let ef : f.normalization ≅ pullback F.fromNormalization b :=
    en.symm ≪≫ asIso (F.normalizationPullback b)
  have hef : ef.hom ≫ pullback.snd F.fromNormalization b = f.fromNormalization := by
    change (en.inv ≫ F.normalizationPullback b) ≫ pullback.snd F.fromNormalization b = _
    rw [Category.assoc, Scheme.Hom.normalizationPullback_snd]
    exact (Iso.inv_comp_eq en).mpr (normalizationSourceIso_hom_fromNormalization _ _ _ _).symm
  have hnormal (p : Ideal R) [p.IsPrime] (hp : d ∈ p) :
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    let q : Spec R := ⟨p, inferInstance⟩
    have hy : hU.fromSpec q ∈ D.1.support :=
      (D.1.fromSpec_mem_support_iff_of_ideal_eq_span hU d hd q).mpr hp
    let : IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec q)) := hreg _ hy
    let : IsRegularLocalRing (Localization.AtPrime p) :=
      IsRegularLocalRing.of_ringEquiv (hU.stalkIsoLocalization q).commRingCatIsoToRingEquiv
    exact ⟨IsRegularLocalRing.isDomain (Localization.AtPrime p),
      SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime p)⟩
  have hlocal (p : PrimeSpectrum R) :
      IsFiniteEtale (pullback.snd f.fromNormalization
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))))) := by
    let q : Spec R := p
    let ap := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))
    let l := Spec.map (hU.stalkIsoLocalization q).hom
    have hs : IsFiniteEtale (pullback.snd F.fromNormalization
        (X.fromSpecStalk (hU.fromSpec q))) := by
      by_cases hy : hU.fromSpec q ∈ D.1.support
      · exact hboundary _ hy
      · exact finiteEtale_normalization_stalk_of_mem_open D.1.supportComplement W _ hy
    have hcomp : IsFiniteEtale (pullback.snd F.fromNormalization
        (l ≫ X.fromSpecStalk (hU.fromSpec q))) :=
      finiteEtale_pullback_snd_comp F.fromNormalization _ l
    have hp : IsFiniteEtale (pullback.snd F.fromNormalization (ap ≫ b)) :=
      Eq.mp (congrArg (fun k => IsFiniteEtale (pullback.snd F.fromNormalization k))
        (hU.SpecMap_stalkIsoLocalization_fromSpecStalk q)) hcomp
    have hwhole : IsFiniteEtale (pullback.snd (pullback.snd F.fromNormalization b) ap) :=
      finiteEtale_iterated_pullback_snd F.fromNormalization b ap
    let m := pullback.map f.fromNormalization ap (pullback.snd F.fromNormalization b) ap
      ef.hom (𝟙 _) (𝟙 _) ((Category.comp_id _).trans hef.symm)
      ((Category.comp_id ap).trans (Category.id_comp ap).symm)
    have hm : m ≫ pullback.snd (pullback.snd F.fromNormalization b) ap =
        pullback.snd f.fromNormalization ap :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    have ht : IsFiniteEtale (m ≫ pullback.snd (pullback.snd F.fromNormalization b) ap) := ⟨⟩
    exact hm ▸ ht
  have hf : IsFiniteEtale f.fromNormalization :=
    finiteEtale_normalization_of_principal_factorization R d A g hnormal hlocal
  have ht : IsFiniteEtale (ef.inv ≫ f.fromNormalization) := ⟨⟩
  have hi : ef.inv ≫ f.fromNormalization = pullback.snd F.fromNormalization b :=
    (Iso.inv_comp_eq ef).mpr hef.symm
  exact hi ▸ ht

/-- A finite étale cover of a Cartier complement extends by its actual
relative normalization when that normalization is finite étale at every
boundary stalk. Only regularity along the boundary is used. -/
theorem finiteEtale_normalization_of_cartier_boundary_stalks
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    (W : FiniteEtale D.1.supportComplement)
    (hboundary : ∀ x : X, x ∈ D.1.support →
      IsFiniteEtale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
        (X.fromSpecStalk x))) :
    IsFiniteEtale (W.hom ≫ D.1.supportComplement.ι).fromNormalization := by
  choose U hx d hregular hd using D.2
  let cover : X.OpenCover :=
    { I₀ := X
      X := fun x => Spec Γ(X, (U x).1)
      f := fun x => (U x).2.fromSpec
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨?_, fun x => (U x).2.isOpenImmersion_fromSpec⟩
        intro x
        refine ⟨x, ?_⟩
        rw [(U x).2.range_fromSpec]
        exact hx x }
  let : IsZariskiLocalAtTarget (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance |>.1
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFiniteEtale) cover
  intro x
  exact finiteEtale_normalization_affineChart D hreg W hboundary (U x).2 (d x) (hd x)

end EtaleFundamentalGroups
