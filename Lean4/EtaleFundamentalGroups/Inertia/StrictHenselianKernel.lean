/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.CartierGenericPoint
import EtaleFundamentalGroups.StrictHenselian.FundamentalGroup
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition


/-!
# Strict-Henselian generic inertia lies in the boundary kernel

The actual local generic morphism factors through the spectrum of its
geometric etale stalk after composition with the open inclusion. The latter
spectrum has trivial fundamental group. Comparing the two factorizations
therefore kills its local generic inertia in the ambient scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem image_le_ker_of_trivial_factorization
    {T U S X : Scheme.{u}}
    (j : T ⟶ U) (i : U ⟶ X) (q : T ⟶ S) (b : S ⟶ X)
    (h : j ≫ i = q ≫ b)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ T) [Subsingleton π₁ᵉᵗ(point ≫ q)] :
    fundamentalGroupImageOfMorphism j point ≤
      (fundamentalGroupHom i (point ≫ j)).toMonoidHom.ker := by
  rintro _ ⟨a, rfl⟩
  apply MonoidHom.mem_ker.mpr
  change fundamentalGroupHom i (point ≫ j) (fundamentalGroupHom j point a) = 1
  have heta : (point ≫ q) ≫ b = (point ≫ j) ≫ i := by
    rw [Category.assoc, ← h, ← Category.assoc]
  have he := fundamentalGroupHom_comp_conj_of_common_composite
    j i q b (j ≫ i) rfl h point ((point ≫ j) ≫ i) rfl heta a
  have hlocal : fundamentalGroupHom q point a = 1 := Subsingleton.elim _ _
  have hone {v w : Spec (.of Ω) ⟶ X} (e : v = w) :
      e ▸ (1 : π₁ᵉᵗ(v)) = (1 : π₁ᵉᵗ(w)) := by
    cases e
    rfl
  simpa only [hlocal, map_one, hone] using he

/-- The fundamental-group image of the fraction field of the actual
geometric etale stalk over a normal local domain is killed by the
Cartier-complement inclusion. -/
theorem geometricStalkFractionField_image_le_boundaryKernel
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ]
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (point : Spec (.of Ω') ⟶
      Spec (.of (FractionRing (StrictHenselian.geometricStalk
        (Spec.map (CommRingCat.ofHom φ)))))) :
    fundamentalGroupImageOfMorphism
        (StrictHenselian.geometricStalkFractionFieldToComplement D x φ) point ≤
      (fundamentalGroupHom D.1.supportComplement.ι
        (point ≫ StrictHenselian.geometricStalkFractionFieldToComplement D x φ)).toMonoidHom.ker :=
    by
  let S := StrictHenselian.geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let j := StrictHenselian.geometricStalkFractionFieldToComplement D x φ
  let q : Spec (.of (FractionRing S)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))
  let b : Spec S ⟶ X :=
    Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap φ)) ≫
      X.fromSpecStalk x
  let : Subsingleton π₁ᵉᵗ(point ≫ q) :=
    StrictHenselian.subsingleton_fundamentalGroup_geometricStalk
      (Spec.map (CommRingCat.ofHom φ)) (point ≫ q)
  apply image_le_ker_of_trivial_factorization j D.1.supportComplement.ι q b _ point
  have hcomp := Spec.map_comp
    (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap φ))
    (CommRingCat.ofHom (algebraMap S (FractionRing S)))
  exact (StrictHenselian.geometricStalkFractionFieldToComplement_comp_ι D x φ).trans
    ((congrArg (fun k : Spec (.of (FractionRing S)) ⟶ Spec (X.presheaf.stalk x) =>
      k ≫ X.fromSpecStalk x) hcomp).trans (Category.assoc _ _ _))

end EtaleFundamentalGroups.Inertia
