/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.StalkMap

/-!
# Stalk comparison through an isomorphism over the base

An isomorphism from a global normalization to the spectrum of a literal
integral closure transports the global stalk map to the canonical
prime-local map.  This is the bridge used after an affine-chart
normalization comparison has been constructed.
-/

noncomputable section

namespace EtaleFundamentalGroups

open CategoryTheory
open AlgebraicGeometry

universe u uK

/-- If `Z` and `S` are isomorphic over `X`, the stalk map from `Z` at the
point corresponding to `s : S` is isomorphic, as an arrow of commutative
rings, to the stalk map from `S` at `s`. -/
noncomputable def arrowStalkMapIsoOfIsoOver
    {Z S X : Scheme.{u}} (e : Z ≅ S)
    (f : Z ⟶ X) (g : S ⟶ X) (h : e.hom ≫ g = f) (s : S) :
    Arrow.mk (f.stalkMap (e.inv s)) ≅ Arrow.mk (g.stalkMap s) := by
  rw [← h]
  let z := e.inv s
  let eComp :
      Arrow.mk ((e.hom ≫ g).stalkMap z) ≅
        Arrow.mk (g.stalkMap (e.hom z)) :=
    Arrow.isoMk'
      ((e.hom ≫ g).stalkMap z) (g.stalkMap (e.hom z))
      (Iso.refl _)
      (asIso (e.hom.stalkMap z)).symm
      (by
        rw [Scheme.Hom.stalkMap_comp]
        simp)
  have hs : e.hom (e.inv s) = s := by
    change (e.inv ≫ e.hom) s = (𝟙 S) s
    rw [e.inv_hom_id]
  exact eComp ≪≫ g.arrowStalkMapIsoOfEq hs

variable {A : Type u} {K : Type uK} {L : Type u}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- A global morphism which is identified over `Spec A` with the spectrum of
`integralClosure A L` has, at the point corresponding to `Q`, the canonical
local map obtained by normalizing after localization at `Q.under A`.
-/
noncomputable def integralClosureStalkArrowIsoOfIsoOver
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of A))
    (e : Z ≅ Spec (.of (integralClosure A L)))
    (h : e.hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap A (integralClosure A L))) = z)
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
        (z.stalkMap
          (e.inv (⟨Q, inferInstance⟩ :
            PrimeSpectrum (integralClosure A L)))) ≅
      Arrow.mk (CommRingCat.ofHom
        (R := Localization.AtPrime P) (S := Localization.AtPrime q)
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime q))) := by
  dsimp only
  exact arrowStalkMapIsoOfIsoOver e z
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (integralClosure A L)))) h
      (⟨Q, inferInstance⟩ : PrimeSpectrum (integralClosure A L)) ≪≫
    integralClosureSpecStalkArrowIso (K := K) (L := L) Q

end EtaleFundamentalGroups

end
