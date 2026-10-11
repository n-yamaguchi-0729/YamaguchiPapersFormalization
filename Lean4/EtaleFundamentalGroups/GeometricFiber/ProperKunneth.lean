/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.Schemes.Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
import EtaleFundamentalGroups.GeometricFiber.ProperHomotopyExact
import EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import ProCGroups.Topologies.ContinuousMulEquiv

/-!
# The pointed proper Künneth comparison

For a proper smooth geometrically connected scheme over a separably closed
field and a connected locally Noetherian second factor, the actual pair of
projection homomorphisms is an isomorphism on fundamental groups at any
rational basepoint. The proof identifies the rational fibre with the first
factor and applies the proper homotopy sequence to the second projection.
-/

noncomputable section

open CategoryTheory Limits
open AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem pair_bijective_of_exact
    {D H B C : Type*} [Group D] [Group H] [Group B] [Group C]
    (i : D →* H) (p : H →* B) (q : H →* C)
    (hq : Function.Surjective q) (hexact : q.ker = i.range)
    (hpi : Function.Bijective (p.comp i)) : Function.Bijective (p.prod q) := by
  constructor
  · intro a b hab
    have hpa : p a = p b := congrArg Prod.fst hab
    have hqa : q a = q b := congrArg Prod.snd hab
    have hqdiv : a / b ∈ q.ker := by
      change q (a / b) = 1
      rw [map_div, hqa, div_self']
    obtain ⟨c, hc⟩ := hexact ▸ hqdiv
    have hpc : (p.comp i) c = (p.comp i) 1 := by
      change p (i c) = (p.comp i) 1
      rw [hc, map_div, hpa, div_self', map_one]
    have hc1 : c = 1 := hpi.1 hpc
    have hab1 : a / b = 1 := by rw [← hc, hc1, map_one]
    exact div_eq_one.mp hab1
  · rintro ⟨b, c⟩
    obtain ⟨a, ha⟩ := hq c
    obtain ⟨d, hd⟩ := hpi.2 (b / p a)
    change p (i d) = b / p a at hd
    refine ⟨i d * a, Prod.ext ?_ ?_⟩
    · change p (i d * a) = b
      rw [map_mul, hd, div_mul_cancel]
    · have hid : q (i d) = 1 := by
        change i d ∈ q.ker
        rw [hexact]
        exact ⟨d, rfl⟩
      change q (i d * a) = c
      rw [map_mul, hid, one_mul, ha]

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

private def rationalProductFiberIso
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    Limits.pullback y (Limits.pullback.snd f g) ≅ X := by
  let p₁ : Limits.pullback f g ⟶ X := Limits.pullback.fst f g
  let p₂ : Limits.pullback f g ⟶ Y := Limits.pullback.snd f g
  let j : Limits.pullback y p₂ ⟶ Limits.pullback f g := Limits.pullback.snd y p₂
  let r : Limits.pullback y p₂ ⟶ Spec (.of K) := Limits.pullback.fst y p₂
  let s : X ⟶ Limits.pullback f g :=
    Limits.pullback.lift (𝟙 X) (f ≫ y) (by rw [Category.id_comp, Category.assoc, hy,
      Category.comp_id])
  have hs₁ : s ≫ p₁ = 𝟙 X := Limits.pullback.lift_fst _ _ _
  have hs₂ : s ≫ p₂ = f ≫ y := Limits.pullback.lift_snd _ _ _
  let t : X ⟶ Limits.pullback y p₂ := Limits.pullback.lift f s hs₂.symm
  have ht₁ : t ≫ r = f := Limits.pullback.lift_fst _ _ _
  have ht₂ : t ≫ j = s := Limits.pullback.lift_snd _ _ _
  have hjr : j ≫ p₁ ≫ f = r := by
    rw [Limits.pullback.condition, ← Category.assoc,
      ← Limits.pullback.condition (f := y) (g := p₂), Category.assoc, hy, Category.comp_id]
  refine ⟨j ≫ p₁, t, ?_, ?_⟩
  · apply Limits.pullback.hom_ext
    · change ((j ≫ p₁) ≫ t) ≫ r = (𝟙 _) ≫ r
      rw [Category.assoc, ht₁, Category.assoc, hjr, Category.id_comp]
    · change ((j ≫ p₁) ≫ t) ≫ j = (𝟙 _) ≫ j
      rw [Category.assoc, ht₂, Category.id_comp]
      apply Limits.pullback.hom_ext
      · change ((j ≫ p₁) ≫ s) ≫ p₁ = j ≫ p₁
        rw [Category.assoc, hs₁, Category.comp_id]
      · change ((j ≫ p₁) ≫ s) ≫ p₂ = j ≫ p₂
        rw [Category.assoc, hs₂, Category.assoc, ← Category.assoc p₁ f y,
          ← Category.assoc j (p₁ ≫ f) y, hjr]
        exact Limits.pullback.condition
  · change t ≫ (j ≫ p₁) = 𝟙 X
    rw [← Category.assoc, ht₂, hs₁]

private theorem pair_bijective_at_rational_fiber
    [IsSepClosed K] [ConnectedSpace Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Spec (.of K)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (g : Y ⟶ Spec (.of K))
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (xi : Spec (.of K) ⟶ Limits.pullback y (Limits.pullback.snd f g)) :
    Function.Bijective
      ((fundamentalGroupHom (Limits.pullback.fst f g)
          (xi ≫ Limits.pullback.snd y (Limits.pullback.snd f g))).prod
        (fundamentalGroupHom (Limits.pullback.snd f g)
          (xi ≫ Limits.pullback.snd y (Limits.pullback.snd f g)))) := by
  have : GeometricallyReduced f :=
    REDsol.geometricallyReduced_of_smooth f
  let p₁ : Limits.pullback f g ⟶ X := Limits.pullback.fst f g
  let p₂ : Limits.pullback f g ⟶ Y := Limits.pullback.snd f g
  let j : Limits.pullback y p₂ ⟶ Limits.pullback f g := Limits.pullback.snd y p₂
  let q : Limits.pullback y p₂ ⟶ X := j ≫ p₁
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : ConnectedSpace ↥(Limits.pullback f g) :=
    GeometricallyConnected.connectedSpace p₂ p₂.isOpenMap
  have : ConnectedSpace ↥(Limits.pullback y p₂) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.fst y p₂)
  let e : Limits.pullback y p₂ ≅ X := rationalProductFiberIso f g y hy
  let E : FiniteEtale X ≌ FiniteEtale (Limits.pullback y p₂) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
  have : (pullback q).IsEquivalence := E.isEquivalence_functor
  have hq : Function.Bijective (fundamentalGroupHom q xi) :=
    fundamentalGroupHom_bijective_of_pullback_isEquivalence q xi
  have hpoint : (xi ≫ j) ≫ p₁ = xi ≫ q := Category.assoc xi j p₁
  have ht : Function.Injective
      (fun a : π₁ᵉᵗ((xi ≫ j) ≫ p₁) => (hpoint ▸ a : π₁ᵉᵗ(xi ≫ q))) := by
    exact (eq_rec_on_bijective (C := fun eta : Spec (.of K) ⟶ X => π₁ᵉᵗ(eta)) hpoint).injective
  have hcomp (a : π₁ᵉᵗ(xi)) :=
    fundamentalGroupHom_comp_of_eq j p₁ q rfl xi hpoint a
  have hrestriction : Function.Bijective
      ((fundamentalGroupHom p₁ (xi ≫ j)).toMonoidHom.comp
        (fundamentalGroupHom j xi).toMonoidHom) := by
    constructor
    · intro a b hab
      change fundamentalGroupHom p₁ (xi ≫ j) (fundamentalGroupHom j xi a) =
        fundamentalGroupHom p₁ (xi ≫ j) (fundamentalGroupHom j xi b) at hab
      apply hq.1
      rw [← hcomp a, ← hcomp b, hab]
    · intro b
      obtain ⟨a, ha⟩ := hq.2 (hpoint ▸ b)
      exact ⟨a, ht ((hcomp a).trans ha)⟩
  exact pair_bijective_of_exact (fundamentalGroupHom j xi).toMonoidHom
    (fundamentalGroupHom p₁ (xi ≫ j)).toMonoidHom
    (fundamentalGroupHom p₂ (xi ≫ j)).toMonoidHom
    (fundamentalGroupHom_surjective_of_flat_geometricallyConnected p₂ (xi ≫ j))
    (fundamentalGroupHom_proper_geometricFiber_ker_eq_range p₂ y xi)
    hrestriction

/-- The actual pair of projection maps is bijective at a rational point of
a product with a proper smooth geometrically connected first factor. -/
theorem fundamentalGroupHom_proper_product_bijective
    [IsSepClosed K] [ConnectedSpace Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Spec (.of K)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (g : Y ⟶ Spec (.of K))
    (z : Spec (.of K) ⟶ Limits.pullback f g)
    (hz : (z ≫ Limits.pullback.snd f g) ≫ g = 𝟙 _) :
    Function.Bijective
      ((fundamentalGroupHom (Limits.pullback.fst f g) z).prod
        (fundamentalGroupHom (Limits.pullback.snd f g) z)) := by
  let y : Spec (.of K) ⟶ Y := z ≫ Limits.pullback.snd f g
  let xi : Spec (.of K) ⟶ Limits.pullback y (Limits.pullback.snd f g) :=
    Limits.pullback.lift (𝟙 _) z (Category.id_comp y)
  have hxi : xi ≫ Limits.pullback.snd y (Limits.pullback.snd f g) = z :=
    Limits.pullback.lift_snd _ _ _
  have h := pair_bijective_at_rational_fiber f g y hz xi
  exact Eq.mp (congrArg (fun eta : Spec (.of K) ⟶ Limits.pullback f g =>
    Function.Bijective ((fundamentalGroupHom (Limits.pullback.fst f g) eta).prod
      (fundamentalGroupHom (Limits.pullback.snd f g) eta))) hxi) h

/-- The proper Künneth isomorphism has the original projection homomorphisms
as its two coordinates, with their native geometric basepoints. -/
def fundamentalGroupEquivProperProduct
    [IsSepClosed K] [ConnectedSpace Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Spec (.of K)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (g : Y ⟶ Spec (.of K))
    (z : Spec (.of K) ⟶ Limits.pullback f g)
    (hz : (z ≫ Limits.pullback.snd f g) ≫ g = 𝟙 _) :
    π₁ᵉᵗ(z) ≃ₜ* (π₁ᵉᵗ(z ≫ Limits.pullback.fst f g) ×
      π₁ᵉᵗ(z ≫ Limits.pullback.snd f g)) := by
  let p := (fundamentalGroupHom (Limits.pullback.fst f g) z).prod
    (fundamentalGroupHom (Limits.pullback.snd f g) z)
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    p.toMonoidHom p.continuous_toFun
    (fundamentalGroupHom_proper_product_bijective f g z hz)

/-- The Künneth equivalence evaluates by the two actual projection maps. -/
theorem fundamentalGroupEquivProperProduct_apply
    [IsSepClosed K] [ConnectedSpace Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Spec (.of K)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (g : Y ⟶ Spec (.of K))
    (z : Spec (.of K) ⟶ Limits.pullback f g)
    (hz : (z ≫ Limits.pullback.snd f g) ≫ g = 𝟙 _) (a : π₁ᵉᵗ(z)) :
    fundamentalGroupEquivProperProduct f g z hz a =
      (fundamentalGroupHom (Limits.pullback.fst f g) z a,
        fundamentalGroupHom (Limits.pullback.snd f g) z a) := by
  rfl

end AlgebraicGeometry.FiniteEtale
