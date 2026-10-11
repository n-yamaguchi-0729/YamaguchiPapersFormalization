/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Kmf2 Fiber Spec Tensor Stalk Leg1 Affine Datum
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

/-- Identify the scheme-theoretic fiber of an affine scheme map with the spectrum of the
residue-field tensor product. -/
noncomputable def kmf2_fiberSpecTensorIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p ≅
      Spec (CommRingCat.of (p.asIdeal.Fiber S)) :=
  pullbackSymmetry _ _ ≪≫
    (pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
        (CommRingCat.of R) p).symm rfl ≪≫
      asIso (pullback.map _ _ _ _
        (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv) (𝟙 _) (𝟙 _)
        (by simp) (by simp))) ≪≫
    pullbackSpecIso R p.asIdeal.ResidueField S

/-- The tensor-product inclusion of the target ring corresponds to the original fiber inclusion. -/
theorem kmf2_fiberSpecTensorIso_hom_includeRight
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (kmf2_fiberSpecTensorIso R S p).hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := p.asIdeal.ResidueField) (B := S)))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let e := Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv
  let g₀ := (Spec (CommRingCat.of R)).fromSpecResidueField p
  have he : g₀ = e ≫ g :=
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of R) p).symm
  let a := pullback.congrHom he (rfl : f = f)
  let b := asIso (pullback.map (e ≫ g) f g f e (𝟙 _) (𝟙 _)
    (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]))
  let c := pullbackSpecIso R p.asIdeal.ResidueField S
  let j := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom)
  have hc : c.hom ≫ j = pullback.snd g f :=
    pullbackSpecIso_hom_snd R p.asIdeal.ResidueField S
  have hb : b.hom ≫ pullback.snd g f = pullback.snd (e ≫ g) f := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have ha : a.hom ≫ pullback.snd (e ≫ g) f = pullback.snd g₀ f := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hbc : (a.hom ≫ b.hom) ≫ c.hom ≫ j = pullback.snd g₀ f :=
    (congrArg (fun k => (a.hom ≫ b.hom) ≫ k) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => a.hom ≫ k) hb).trans ha))
  change ((pullbackSymmetry f g₀).hom ≫ ((a.hom ≫ b.hom) ≫ c.hom)) ≫ j = pullback.fst f g₀
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (pullbackSymmetry f g₀).hom ≫ k)
      ((Category.assoc _ _ _).trans hbc)).trans
      (pullbackSymmetry_hom_comp_snd f g₀))

/-- Comapping the prime of a fiber point along the target-ring inclusion recovers its image
prime. -/
theorem kmf2_fiberSpecTensorIso_point_comap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    (((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal).comap
        (Algebra.TensorProduct.includeRight
          (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom =
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w).asIdeal := by
  have h1 : Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := p.asIdeal.ResidueField) (B := S))))
        ((kmf2_fiberSpecTensorIso R S p).hom w) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w := by
    rw [← Scheme.Hom.comp_apply, kmf2_fiberSpecTensorIso_hom_includeRight]
  have h2 := congrArg PrimeSpectrum.asIdeal h1
  exact h2

/-- The stalk at a fiber point is the localization of the residue-field tensor product at its
corresponding prime. -/
theorem kmf2_fiberStalk_localizationAtPrime
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    let q : PrimeSpectrum (p.asIdeal.Fiber S) := (kmf2_fiberSpecTensorIso R S p).hom w
    Nonempty
      (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p).presheaf.stalk w ≃+*
        Localization.AtPrime q.asIdeal) := by
  let q : PrimeSpectrum (p.asIdeal.Fiber S) := (kmf2_fiberSpecTensorIso R S p).hom w
  exact ⟨(asIso ((kmf2_fiberSpecTensorIso R S p).hom.stalkMap
    w)).commRingCatIsoToRingEquiv.symm.trans
    ((StructureSheaf.stalkIso (p.asIdeal.Fiber S) q).symm.toRingEquiv)⟩

/-- For an affine point, construct the prime over its original prime and identify its fiber
stalk with the prime localization. -/
theorem kmf2_fiberStalkLeg1_affineDatum
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (x : Spec (CommRingCat.of S)) :
    let p : PrimeSpectrum R := Spec.map (CommRingCat.ofHom (algebraMap R S)) x
    ∃ (Q : Ideal (p.asIdeal.Fiber S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeRight
        (R := R)
        (A := p.asIdeal.ResidueField)
        (B := S)).toRingHom = x.asIdeal ∧
      Nonempty
        (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
            (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x) ≃+*
          Localization.AtPrime Q) := by
  refine ⟨((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).asIdeal,
    ((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).2, ?_, ?_⟩
  · exact (kmf2_fiberSpecTensorIso_point_comap R S
      (show PrimeSpectrum R from Spec.map (CommRingCat.ofHom (algebraMap R S)) x)
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).trans
      (congrArg (fun z : Spec (CommRingCat.of S) => z.asIdeal)
        (Scheme.Hom.fiberι_asFiber (Spec.map (CommRingCat.ofHom (algebraMap R S))) x))
  · exact kmf2_fiberStalk_localizationAtPrime R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)
/--
info: 'kmf2_fiberSpecTensorIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberSpecTensorIso
/--
info: 'kmf2_fiberSpecTensorIso_hom_includeRight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberSpecTensorIso_hom_includeRight
/--
info: 'kmf2_fiberSpecTensorIso_point_comap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberSpecTensorIso_point_comap
/--
info: 'kmf2_fiberStalk_localizationAtPrime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberStalk_localizationAtPrime
/--
info: 'kmf2_fiberStalkLeg1_affineDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiberStalkLeg1_affineDatum

end
