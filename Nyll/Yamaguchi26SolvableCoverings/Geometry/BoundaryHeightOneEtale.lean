/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryLocalNormalizationEtale
import Nyll.SchemeTheory.Divisors.ComponentStalkBranch
import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR
import Nyll.SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Height-one étaleness over arbitrary boundary stalks

A height-one prime containing the Cartier ideal represents a generic point of
an actual component of the boundary. The previously constructed étale
normalization over that component's DVR therefore remains étale after passing
to the chosen prime localization of the original stalk.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups

namespace Yamaguchi26SolvableCoverings

private theorem localizationAtPrimeTo_factor
    (X : Scheme.{0}) (x : X) (q : Spec (X.presheaf.stalk x))
    [hq : q.asIdeal.IsPrime] :
    (Spec.map (Spec.stalkIso (X.presheaf.stalk x) q).hom ≫
      Spec.map ((X.fromSpecStalk x).stalkMap q)) ≫
        X.fromSpecStalk (X.fromSpecStalk x q) =
      Scheme.localizationAtPrimeTo X x q.asIdeal := by
  rw [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk (X.fromSpecStalk x) (x := q),
    ← Category.assoc, Spec.fromSpecStalk_eq (X.presheaf.stalk x) q, ← Spec.map_comp]
  have h : ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
      (Spec (X.presheaf.stalk x)).presheaf.germ ⊤ q trivial) ≫
        (Spec.stalkIso (X.presheaf.stalk x) q).hom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (Localization.AtPrime q.asIdeal)) := by
    have hbase : CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (Localization.AtPrime q.asIdeal)) ≫ (Spec.stalkIso (X.presheaf.stalk x) q).inv =
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.germ ⊤ q trivial :=
      Spec.algebraMap_stalkIso_inv (R := X.presheaf.stalk x) q
    exact (congrArg (fun k => k ≫ (Spec.stalkIso (X.presheaf.stalk x) q).hom)
      hbase.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun k => CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime q.asIdeal)) ≫ k)
            (Iso.inv_hom_id (Spec.stalkIso (X.presheaf.stalk x) q))).trans
              (Category.comp_id _)))
  exact congrArg (fun k => Spec.map k ≫ X.fromSpecStalk x) h

private theorem etale_pullback_snd_comp
    {N X S T : Scheme.{0}} (g : N ⟶ X) (b : S ⟶ X) (l : T ⟶ S)
    [Etale (pullback.snd g b)] : Etale (pullback.snd g (l ≫ b)) := by
  let H := (IsPullback.of_hasPullback (pullback.snd g b) l).paste_horiz
    (IsPullback.of_hasPullback g b)
  let e := (IsPullback.of_hasPullback g (l ≫ b)).isoIsPullback _ _ H
  have he : e.hom ≫ pullback.snd (pullback.snd g b) l =
      pullback.snd g (l ≫ b) :=
    IsPullback.isoIsPullback_hom_snd N T
      (IsPullback.of_hasPullback g (l ≫ b)) H
  have ht : Etale (e.hom ≫ pullback.snd (pullback.snd g b) l) := inferInstance
  exact he ▸ ht

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- Height-one points on a Cartier boundary come from its generic component
points. Etaleness of the actual normalization at those component stalks
therefore supplies every height-one stalk localization needed by purity. -/
theorem normalization_heightOne_etale_of_componentStalks
    (D : X.EffectiveCartierDivisor) (W : FiniteEtale D.1.supportComplement)
    (hgeneric : ∀ E : Component D,
      Etale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
        (X.fromSpecStalk (componentPoint D E))))
    (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hp : p.height = 1) (hDp : D.1.stalkIdeal x ≤ p) :
    Etale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (Scheme.localizationAtPrimeTo X x p)) := by
  let q : Spec (X.presheaf.stalk x) := ⟨p, inferInstance⟩
  obtain ⟨Z, hZ, hZq⟩ := D.2.exists_componentGenericPoint_eq_fromSpecStalk x q hp hDp
  let E : Component D := ⟨Z, hZ⟩
  have hE : D.1.componentGenericPoint Z hZ = componentPoint D E :=
    D.1.componentGenericPoint_eq Z hZ
  have hEq : componentPoint D E = X.fromSpecStalk x q := hE.symm.trans hZq
  let g := (W.hom ≫ D.1.supportComplement.ι).fromNormalization
  have hEt : Etale (pullback.snd g (X.fromSpecStalk (X.fromSpecStalk x q))) := by
    apply Eq.mp (congrArg (fun y : X => Etale (pullback.snd g (X.fromSpecStalk y))) hEq)
    exact hgeneric E
  let l := Spec.map (Spec.stalkIso (X.presheaf.stalk x) q).hom ≫
    Spec.map ((X.fromSpecStalk x).stalkMap q)
  have ht : Etale (pullback.snd g (l ≫ X.fromSpecStalk (X.fromSpecStalk x q))) :=
    etale_pullback_snd_comp g _ l
  exact Eq.mp (congrArg (fun b => Etale (pullback.snd g b))
    (localizationAtPrimeTo_factor X x q (hq := q.isPrime))) ht

/-- Trivial finite boundary inertia gives etaleness at each component stalk;
the domain and DVR structures are transported to the paper's component point. -/
theorem boundaryUnramified_normalization_componentStalk_etale
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W) (E : Component D) :
    Etale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (X.fromSpecStalk (componentPoint D E))) := by
  have hE : D.1.componentGenericPoint E.val E.property = componentPoint D E :=
    D.1.componentGenericPoint_eq E.val E.property
  have hLocal : ∃ hDomain : IsDomain (X.presheaf.stalk (componentPoint D E)),
      let : IsDomain (X.presheaf.stalk (componentPoint D E)) := hDomain
      IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) := by
    apply Eq.mp (congrArg (fun y : X => ∃ hDomain : IsDomain (X.presheaf.stalk y),
      let : IsDomain (X.presheaf.stalk y) := hDomain
      IsDiscreteValuationRing (X.presheaf.stalk y)) hE)
    exact ⟨isDomain_stalk_componentGenericPoint D hreg E.val E.property,
      isDiscreteValuationRing_stalk_componentGenericPoint D hreg E.val E.property⟩
  obtain ⟨hDomain, hDVR⟩ := hLocal
  let : IsDomain (X.presheaf.stalk (componentPoint D E)) := hDomain
  let : IsDiscreteValuationRing (X.presheaf.stalk (componentPoint D E)) := hDVR
  exact boundaryUnramified_normalization_stalk_etale D E W hW hU

/-- The actual relative normalization is étale over every height-one prime
localization of a stalk whose prime contains the Cartier boundary ideal. -/
theorem boundaryUnramified_normalization_heightOne_etale
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [ConnectedSpace D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (hU : IsBoundaryUnramified D W)
    (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hp : p.height = 1) (hDp : D.1.stalkIdeal x ≤ p) :
    Etale (pullback.snd (W.hom ≫ D.1.supportComplement.ι).fromNormalization
      (Scheme.localizationAtPrimeTo X x p)) := by
  exact normalization_heightOne_etale_of_componentStalks D W
    (boundaryUnramified_normalization_componentStalk_etale D hreg W hW hU) x p hp hDp

end Yamaguchi26SolvableCoverings
