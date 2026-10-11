/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Basic
import SchemeTheory.Morphisms.EtaleRadicial
import EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Reduced
import EtaleFundamentalGroups.FiniteEtale.FiniteField.FieldFrobeniusFactorization

/-!
# Pure Inseparable Affine

The Frobenius power on every algebra, including the zero algebra.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups

variable (k : Type u) [Field k] (p n : ℕ) [ExpChar k p]

/-- The Frobenius power on every algebra, including the zero algebra. -/
def algebraFrobeniusPower (R : Type u) [CommRing R] [Algebra k R] : R →+* R := by
  classical
  by_cases h : Nontrivial R
  · let : ExpChar R p := expChar_of_injective_algebraMap (algebraMap k R).injective p
    exact iterateFrobenius R p n
  · exact RingHom.id R

theorem algebraFrobeniusPower_apply (R : Type u) [CommRing R] [Algebra k R] (x : R) :
    algebraFrobeniusPower k p n R x = x ^ p ^ n := by
  classical
  unfold algebraFrobeniusPower
  split_ifs with h
  · rfl
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact Subsingleton.elim _ _

theorem algebraFrobeniusPower_naturality
    (R B : Type u) [CommRing R] [Algebra k R] [CommRing B] [Algebra k B] (f : R →+* B) :
    f.comp (algebraFrobeniusPower k p n R) =
      (algebraFrobeniusPower k p n B).comp f := by
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, algebraFrobeniusPower_apply, map_pow]

private theorem specAlgebraFrobeniusPower_surjective
    (R : Type u) [CommRing R] [Algebra k R] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraFrobeniusPower k p n R))) := by
  constructor
  intro x
  refine ⟨x, PrimeSpectrum.ext (Ideal.ext fun r ↦ ?_)⟩
  change algebraFrobeniusPower k p n R r ∈ x.asIdeal ↔ r ∈ x.asIdeal
  rw [algebraFrobeniusPower_apply]
  exact x.isPrime.pow_mem_iff_mem (p ^ n) (expChar_pow_pos k p n)

private theorem specAlgebraFrobeniusPower_universallyInjective
    (R : Type u) [CommRing R] [Algebra k R] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraFrobeniusPower k p n R))) := by
  apply ((tfae_universallyInjective _).out 1 2).mpr
  intro K _ a b hab
  apply (Spec.preimage_inj a b).mp
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  let a' : R →+* K := (Spec.preimage a).hom
  let b' : R →+* K := (Spec.preimage b).hom
  let : ExpChar K p := expChar_of_injective_ringHom
    (a'.comp (algebraMap k R)).injective p
  have heq : a' (r ^ p ^ n) = b' (r ^ p ^ n) := by
    have h := congrArg Spec.preimage hab
    rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at h
    have h' := congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of K ↦ m.hom r) h
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      algebraFrobeniusPower_apply] using h'
  exact (iterateFrobenius_inj K p n) (by
    simpa only [iterateFrobenius_def, map_pow] using heq)

private abbrev affineCoordinateAlgebra (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Algebra k Γ(X, ⊤) :=
  (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

/-- Frobenius power on an affine scheme over a field. -/
def affineSchemeFrobeniusPower (X : Scheme.{u}) [IsAffine X]
    (f : X ⟶ Spec (.of k)) : X ⟶ X :=
  letI : Algebra k Γ(X, ⊤) := affineCoordinateAlgebra k X f
  X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    (algebraFrobeniusPower k p n Γ(X, ⊤))) ≫ X.isoSpec.inv

theorem affineSchemeFrobeniusPower_naturality
    (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (a : X ⟶ Y) :
    a ≫ affineSchemeFrobeniusPower k p n Y g =
      affineSchemeFrobeniusPower k p n X f ≫ a := by
  let : Algebra k Γ(X, ⊤) := affineCoordinateAlgebra k X f
  let : Algebra k Γ(Y, ⊤) := affineCoordinateAlgebra k Y g
  have hw : Spec.map (a.appTop) ≫
      Spec.map (CommRingCat.ofHom (algebraFrobeniusPower k p n Γ(Y, ⊤))) =
    Spec.map (CommRingCat.ofHom (algebraFrobeniusPower k p n Γ(X, ⊤))) ≫
      Spec.map (a.appTop) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact algebraFrobeniusPower_naturality k p n Γ(Y, ⊤) Γ(X, ⊤) a.appTop.hom
  dsimp only [affineSchemeFrobeniusPower]
  rw [← Scheme.isoSpec_hom_naturality_assoc, reassoc_of% hw,
    Scheme.isoSpec_inv_naturality]
  simp only [Category.assoc]

private theorem affineSchemeFrobeniusPower_surjective
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (.of k)) :
    Surjective (affineSchemeFrobeniusPower k p n X f) := by
  let : Algebra k Γ(X, ⊤) := affineCoordinateAlgebra k X f
  let : Surjective (Spec.map (CommRingCat.ofHom
      (algebraFrobeniusPower k p n Γ(X, ⊤)))) :=
    specAlgebraFrobeniusPower_surjective k p n Γ(X, ⊤)
  dsimp only [affineSchemeFrobeniusPower]
  infer_instance

private theorem affineSchemeFrobeniusPower_universallyInjective
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (.of k)) :
    UniversallyInjective (affineSchemeFrobeniusPower k p n X f) := by
  let : Algebra k Γ(X, ⊤) := affineCoordinateAlgebra k X f
  dsimp only [affineSchemeFrobeniusPower]
  apply MorphismProperty.comp_mem (W := @UniversallyInjective)
  · infer_instance
  · exact MorphismProperty.comp_mem (W := @UniversallyInjective) _ _
      (specAlgebraFrobeniusPower_universallyInjective k p n Γ(X, ⊤)) inferInstance

/-- Relative Frobenius, with the actual scheme pullback as its target. -/
def affineSchemeRelativeFrobenius
    (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y]
    (g : Y ⟶ Spec (.of k)) (a : X ⟶ Y) :
    X ⟶ pullback (affineSchemeFrobeniusPower k p n Y g) a :=
  pullback.lift a (affineSchemeFrobeniusPower k p n X (a ≫ g))
    (affineSchemeFrobeniusPower_naturality k p n X Y (a ≫ g) g a)

/-- Relative Frobenius on affine étale schemes is invertible, including empty schemes. -/
theorem affineSchemeRelativeFrobenius_isIso
    (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y]
    (g : Y ⟶ Spec (.of k)) (a : X ⟶ Y) [Etale a] :
    IsIso (affineSchemeRelativeFrobenius k p n X Y g a) := by
  let φ := affineSchemeFrobeniusPower k p n Y g
  let q : X ⟶ pullback φ a := affineSchemeRelativeFrobenius k p n X Y g a
  have hf : q ≫ pullback.fst φ a = a := pullback.lift_fst _ _ _
  have hs : q ≫ pullback.snd φ a =
      affineSchemeFrobeniusPower k p n X (a ≫ g) := pullback.lift_snd _ _ _
  have hπinj : Function.Injective (pullback.snd φ a) :=
    (affineSchemeFrobeniusPower_universallyInjective k p n Y g).universally_injective
      _ _ _ (IsPullback.of_hasPullback φ a).flip
  let : UniversallyInjective q := by
    apply ((tfae_universallyInjective q).out 1 2).mpr
    intro K _ x y hxy
    have hX : ∀ (K : Type u) [Field K], Function.Injective
        (fun t : Spec (.of K) ⟶ X ↦
          t ≫ affineSchemeFrobeniusPower k p n X (a ≫ g)) :=
      ((tfae_universallyInjective _).out 1 2).mp
        (affineSchemeFrobeniusPower_universallyInjective k p n X (a ≫ g))
    apply hX K
    change x ≫ affineSchemeFrobeniusPower k p n X (a ≫ g) =
      y ≫ affineSchemeFrobeniusPower k p n X (a ≫ g)
    change x ≫ q = y ≫ q at hxy
    rw [← hs, ← Category.assoc, ← Category.assoc, hxy]
  let : Surjective q := by
    constructor
    intro z
    obtain ⟨x, hx⟩ := (affineSchemeFrobeniusPower_surjective k p n X (a ≫ g)).surj
      (pullback.snd φ a z)
    refine ⟨x, hπinj ?_⟩
    rw [← Scheme.Hom.comp_apply, hs]
    exact hx
  let : Etale (q ≫ pullback.fst φ a) := hf.symm ▸ inferInstanceAs (Etale a)
  let : Etale q := Etale.of_comp q (pullback.fst φ a)
  exact Etale.isIso_of_universallyInjective_of_surjective q

/-- Pullback by Frobenius recovers each actual finite étale cover of an affine scheme. -/
def affineFrobeniusPullbackObjIso
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (.of k))
    (Z : AlgebraicGeometry.FiniteEtale X) :
    Z ≅ (AlgebraicGeometry.FiniteEtale.pullback
      (affineSchemeFrobeniusPower k p n X f)).obj Z := by
  let a : Z.left ⟶ X := Z.hom
  let : IsAffine Z.left := isAffine_of_isAffineHom a
  let q := affineSchemeRelativeFrobenius k p n Z.left X f Z.hom
  let : IsIso q := affineSchemeRelativeFrobenius_isIso k p n Z.left X f Z.hom
  refine MorphismProperty.Over.isoMk
    (asIso q ≪≫ pullbackSymmetry (affineSchemeFrobeniusPower k p n X f) Z.hom) ?_
  change (q ≫ (pullbackSymmetry _ _).hom) ≫ pullback.snd Z.hom _ = Z.hom
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullback.lift_fst _ _ _

private theorem affineSchemeFrobeniusPower_spec
    (R : Type u) [CommRing R] [Algebra k R] (f : Spec (.of R) ⟶ Spec (.of k)) :
    affineSchemeFrobeniusPower k p n (Spec (.of R)) f =
      Spec.map (CommRingCat.ofHom (algebraFrobeniusPower k p n R)) := by
  let : Algebra k Γ(Spec (.of R), ⊤) := affineCoordinateAlgebra k (Spec (.of R)) f
  dsimp only [affineSchemeFrobeniusPower]
  rw [Scheme.isoSpec_Spec_hom, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (Scheme.ΓSpecIso (.of R)).hom.hom
    (algebraFrobeniusPower k p n Γ(Spec (.of R), ⊤)
      ((Scheme.ΓSpecIso (.of R)).inv.hom r)) = algebraFrobeniusPower k p n R r
  rw [algebraFrobeniusPower_apply, map_pow, algebraFrobeniusPower_apply]
  exact congrArg (· ^ p ^ n) (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (.of R)).inv_hom_id r)


/-- Every finite étale cover after a finite purely inseparable constant extension
has an actual model over the original affine scheme. -/
theorem exists_affine_purelyInseparable_model
    (L : Type u) [Field L] [Algebra k L] [IsPurelyInseparable k L]
    [FiniteDimensional k L] (X : Scheme.{u}) [IsAffine X]
    (f : X ⟶ Spec (.of k))
    (Z : AlgebraicGeometry.FiniteEtale
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ M : AlgebraicGeometry.FiniteEtale X,
      Nonempty ((AlgebraicGeometry.FiniteEtale.pullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj M ≅ Z) := by
  let p := ringExpChar k
  let : ExpChar L p := expChar_of_injective_algebraMap (algebraMap k L).injective p
  obtain ⟨n, σ, hσL, hσk⟩ := exists_purelyInseparable_frobenius_factorization k L p
  let φ : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let τ : Spec (.of k) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom σ)
  let XL : Scheme.{u} := pullback φ f
  let q : XL ⟶ X := pullback.snd φ f
  let fL : XL ⟶ Spec (.of k) := q ≫ f
  have hτφ : τ ≫ φ = affineSchemeFrobeniusPower k p n (Spec (.of k)) (𝟙 _) := by
    rw [affineSchemeFrobeniusPower_spec]
    dsimp only [τ, φ]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change σ.comp (algebraMap k L) = algebraFrobeniusPower k p n k
    rw [hσk]
    exact RingHom.ext fun x ↦ (algebraFrobeniusPower_apply k p n k x).symm
  have hφτ : φ ≫ τ = affineSchemeFrobeniusPower k p n (Spec (.of L)) φ := by
    rw [affineSchemeFrobeniusPower_spec]
    dsimp only [τ, φ]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change (algebraMap k L).comp σ = algebraFrobeniusPower k p n L
    rw [hσL]
    exact RingHom.ext fun x ↦ (algebraFrobeniusPower_apply k p n L x).symm
  let s : X ⟶ XL := pullback.lift (f ≫ τ) (affineSchemeFrobeniusPower k p n X f) (by
    rw [Category.assoc, hτφ]
    exact affineSchemeFrobeniusPower_naturality k p n X (Spec (.of k)) f (𝟙 _) f)
  have hqs : q ≫ s = affineSchemeFrobeniusPower k p n XL fL := by
    apply pullback.hom_ext
    · change (q ≫ s) ≫ pullback.fst φ f = _
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        ← pullback.condition, Category.assoc, hφτ]
      exact affineSchemeFrobeniusPower_naturality k p n XL (Spec (.of L)) fL φ
        (pullback.fst φ f)
    · change (q ≫ s) ≫ pullback.snd φ f = _
      rw [Category.assoc, pullback.lift_snd]
      exact affineSchemeFrobeniusPower_naturality k p n XL X fL f q
  refine ⟨(AlgebraicGeometry.FiniteEtale.pullback s).obj Z, ⟨?_⟩⟩
  exact AlgebraicGeometry.FiniteEtale.finiteEtalePullbackCompObjIso q s
    (affineSchemeFrobeniusPower k p n XL fL) hqs Z ≪≫
      (affineFrobeniusPullbackObjIso k p n XL fL Z).symm

end EtaleFundamentalGroups
