/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.PrimeAtPrimeEquiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Stalk map of an affine normalization

The stalk map of the affine normalization `Spec (integralClosure A L) ⟶ Spec A`
at a normalization prime is the prime-local map obtained after first localizing
the base and then normalizing.  This file records the comparison as an
isomorphism in the arrow category, so properties of the literal stalk map can
be transported without replacing either endpoint by an unspecified ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

open CategoryTheory
open AlgebraicGeometry

universe u uK

/-- A commutative square whose vertical maps are open immersions identifies
the stalk-map arrows of its two horizontal maps. -/
noncomputable def arrowStalkMapIsoOfOpenSquare
    {S Z X Y : Scheme.{u}}
    (i : S ⟶ Z) (f : Z ⟶ Y) (g : S ⟶ X) (j : X ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) (s : S) :
    Arrow.mk (f.stalkMap (i s)) ≅ Arrow.mk (g.stalkMap s) :=
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by
        rw [← Scheme.Hom.comp_apply, h]
        rfl) ≪≫
      asIso (j.stalkMap (g s)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq rfl) ≪≫
      asIso (i.stalkMap s))
    (by
      simp [← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ h,
        TopCat.Presheaf.stalkCongr_hom]
      rfl)

/-- On an affine chart of the base, the stalk map of the global relative
normalization is the stalk map of the affine integral-closure morphism.  The
point on the global normalization is supplied by its canonical normalization
open cover, so the prime of the integral closure is retained literally. -/
noncomputable def normalizationChartStalkArrowIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    (Q : PrimeSpectrum
      (letI := (f.app U).hom.toAlgebra
       integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) :
    letI := (f.app U).hom.toAlgebra
    Arrow.mk
        (f.fromNormalization.stalkMap
          (f.normalizationOpenCover.f ⟨U, hU⟩ Q)) ≅
      Arrow.mk
        ((Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Y, U)
            (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))))).stalkMap Q) := by
  dsimp only
  let i := f.normalizationOpenCover.f ⟨U, hU⟩
  let g := Spec.map (f.normalizationDiagramMap.app (.op U))
  let j := hU.fromSpec
  haveI : IsOpenImmersion i :=
    f.normalizationOpenCover.map_prop ⟨U, hU⟩
  haveI : IsOpenImmersion j := inferInstance
  exact arrowStalkMapIsoOfOpenSquare i f.fromNormalization g j
    (f.ι_fromNormalization ⟨U, hU⟩) Q

/-- Literal prime-local form of `normalizationChartStalkArrowIso`: the
global relative-normalization stalk map is identified with the localization
of the affine integral-closure algebra map at `Q` and its contraction. -/
noncomputable def normalizationChartStalkPrimeLocalizationArrowIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    (Q : PrimeSpectrum
      (letI := (f.app U).hom.toAlgebra
       integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) :
    letI := (f.app U).hom.toAlgebra
    let C := integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
    let φ : Γ(Y, U) →+* C := algebraMap Γ(Y, U) C
    Arrow.mk
        (f.fromNormalization.stalkMap
          (f.normalizationOpenCover.f ⟨U, hU⟩ Q)) ≅
      Arrow.mk (CommRingCat.ofHom
        (Localization.localRingHom
          (Q.comap φ).asIdeal Q.asIdeal φ rfl)) := by
  dsimp only
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  let e₁ := normalizationChartStalkArrowIso f hU Q
  let e₂ := Scheme.arrowStalkMapSpecIso
    (CommRingCat.ofHom
      (algebraMap Γ(Y, U)
        (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)))) Q
  exact e₁ ≪≫ e₂

variable {A : Type u} {K : Type uK} {L : Type u}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- At a prime `Q` of the affine normalization, the literal stalk map of
`Spec (integralClosure A L) ⟶ Spec A` is isomorphic to the local map at the
canonically transported prime of the normalization after base localization.
-/
noncomputable def integralClosureSpecStalkArrowIso
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    let P := Q.under A
    letI : P.IsPrime := inferInstance
    letI : Q.LiesOver P := inferInstance
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let q := localizedNormalizationPrime (K := K) (L := L) P Q
    letI : q.IsMaximal :=
      localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
    Arrow.mk
        ((Spec.map (CommRingCat.ofHom
          (algebraMap A (integralClosure A L)))).stalkMap
            (⟨Q, inferInstance⟩ : PrimeSpectrum (integralClosure A L))) ≅
      Arrow.mk (CommRingCat.ofHom
        (R := Localization.AtPrime P) (S := Localization.AtPrime q)
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime q))) := by
  dsimp only
  let P := Q.under A
  letI : P.IsPrime := inferInstance
  letI : Q.LiesOver P := inferInstance
  letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let q := localizedNormalizationPrime (K := K) (L := L) P Q
  letI : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let E : Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime q :=
    integralClosurePrimeLocalizationAlgEquiv
      (K := K) (L := L) P Q
  refine (Scheme.arrowStalkMapSpecIso
      (CommRingCat.ofHom (algebraMap A (integralClosure A L)))
      (⟨Q, inferInstance⟩ : PrimeSpectrum (integralClosure A L))) ≪≫
    Arrow.isoMk (Iso.refl _) E.toRingEquiv.toCommRingCatIso ?_
  ext x
  change (algebraMap (Localization.AtPrime P) (Localization.AtPrime q)) x =
    E (Localization.localRingHom P Q
      (algebraMap A (integralClosure A L)) rfl x)
  rw [← Localization.AtPrime.algebraMap_eq]
  exact (E.commutes x).symm

end EtaleFundamentalGroups

end
