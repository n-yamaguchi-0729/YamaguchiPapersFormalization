/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Nyll.EtaleCohomology.Classical.KummerRootCover
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Geometric local surjectivity in the actual étale Kummer sequence

A global unit has an nth root on an actual finite étale surjective cover
when n is positive and invertible. We pull the explicit affine root cover
back along the canonical map to the spectrum of global sections. Thus the
construction works on arbitrary schemes, without choosing affine charts.

This proves epimorphy of the actual power morphism on the small étale
multiplicative-group sheaf. The kernel gives the actual roots-of-unity
sheaf and an actual short exact Kummer sequence.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.Abelian

namespace EtaleCohomology

/-- An actual unit on any scheme acquires an actual root on a finite étale
surjective cover. -/
theorem exists_finiteEtale_unit_root (X : Scheme.{u}) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) (a : (Γ(X, ⊤) : Type u)ˣ) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsFiniteEtale f ∧ Function.Surjective f ∧
      (∀ x : X, f.finrank x = n) ∧ ∃ b : (Γ(Y, ⊤) : Type u)ˣ,
        b ^ n = Units.map f.appTop.hom.toMonoidHom a := by
  let R : CommRingCat.{u} := Γ(X, ⊤)
  let A : CommRingCat.{u} := .of (kummerRootAlgebra n a)
  let φ : R ⟶ A := CommRingCat.ofHom (algebraMap R A)
  let q : Spec A ⟶ Spec R := Spec.map φ
  have : IsFiniteEtale q := kummerRootCover_isFiniteEtale n a hnX
  have : Surjective q := ⟨kummerRootCover_surjective hn a⟩
  let Y : Scheme.{u} := pullback q X.toSpecΓ
  let f : Y ⟶ X := pullback.snd q X.toSpecΓ
  let ψ : A ⟶ Γ(Y, ⊤) :=
    (Scheme.ΓSpecIso A).inv ≫ (pullback.fst q X.toSpecΓ).appTop
  have hψ : φ ≫ ψ = f.appTop := by
    dsimp only [ψ, f, q]
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
      pullback.condition, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  let b : (Γ(Y, ⊤) : Type u)ˣ :=
    Units.map ψ.hom.toMonoidHom (kummerRootUnit hn a)
  refine ⟨Y, f, inferInstance, f.surjective, ?_, b, ?_⟩
  · intro x
    exact (Scheme.Hom.finrank_pullback_snd q X.toSpecΓ x).trans
      (kummerRootCover_finrank hn a (X.toSpecΓ x))
  · dsimp only [b]
    rw [← map_pow, kummerRootUnit_pow]
    apply Units.ext
    exact congrArg (fun k : R ⟶ Γ(Y, ⊤) => k (a : R)) hψ

/-- Local power lifts retain their actual finite étale cover and degree. -/
theorem exists_finiteEtale_power_lift (X : Scheme.{u}) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) (V : X.Etale)
    (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op V)) :
    ∃ (W : X.Etale) (g : W ⟶ V), IsFiniteEtale g.left ∧
      Function.Surjective g.left ∧ (∀ x : V.left, g.left.finrank x = n) ∧
      ∃ t : (etaleMultiplicativeGroupSheaf X).obj.obj (op W),
        (etaleMultiplicativeGroupPower X n).hom.app (op W) t =
          (etaleMultiplicativeGroupSheaf X).obj.map g.op s := by
  let a : (Γ(V.left, ⊤) : Type u)ˣ :=
    (etaleMultiplicativeGroupSectionsEquiv X V s).toMul
  have hnV : IsUnit (n : Γ(V.left, ⊤)) := by
    simpa only [map_natCast] using hnX.map V.hom.appTop.hom
  obtain ⟨Y, f, hf, hs, hd, b, hb⟩ := exists_finiteEtale_unit_root V.left hn hnV a
  have : Etale f := hf.toEtale
  let W : X.Etale := Scheme.Etale.mk (f ≫ V.hom)
  let g : W ⟶ V := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f rfl
  refine ⟨W, g, hf, hs, hd,
    (etaleMultiplicativeGroupSectionsEquiv X W).symm (Additive.ofMul b), ?_⟩
  apply (etaleMultiplicativeGroupSectionsEquiv X W).injective
  rw [etaleMultiplicativeGroupPower_apply]
  change Additive.ofMul (b ^ n) =
    Additive.ofMul (Units.map f.appTop.hom.toMonoidHom a)
  exact congrArg Additive.ofMul hb

/-- The actual small-étale power morphism is locally surjective because
the geometric root cover supplies local preimages. -/
theorem etaleMultiplicativeGroupPower_isLocallySurjective (X : Scheme.{u})
    {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (etaleMultiplicativeGroupPower X n).hom := by
  constructor
  intro V s
  obtain ⟨W, g, _, hs, _, t, ht⟩ := exists_finiteEtale_power_lift X hn hnX V s
  let S : Sieve V := Presheaf.imageSieve (etaleMultiplicativeGroupPower X n).hom s
  have hg : S g := ⟨t, ht⟩
  have hS : S ∈ (X.smallPretopology
      (P := show MorphismProperty Scheme.{u} from @Etale)
      (Q := show MorphismProperty Scheme.{u} from @Etale)).toGrothendieck V := by
    apply (Scheme.mem_toGrothendieck_smallPretopology
      (P := show MorphismProperty Scheme.{u} from @Etale)
      (Q := show MorphismProperty Scheme.{u} from @Etale) V S).mpr
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨W, g, y, hg, inferInstance, hy⟩
  rw [← Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
    X (le_refl _)] at hS
  exact hS

theorem etaleMultiplicativeGroupPower_epi (X : Scheme.{u}) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Epi (etaleMultiplicativeGroupPower X n) := by
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (etaleMultiplicativeGroupPower X n).hom :=
    etaleMultiplicativeGroupPower_isLocallySurjective X hn hnX
  infer_instance

/-- The actual roots-of-unity sheaf, as the kernel of the actual power map. -/
abbrev etaleRootsOfUnitySheaf (X : Scheme.{u}) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  kernel (etaleMultiplicativeGroupPower X n)

/-- The actual Kummer complex on the small étale site. -/
abbrev etaleKummerComplex (X : Scheme.{u}) (n : ℕ) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk (kernel.ι (etaleMultiplicativeGroupPower X n))
    (etaleMultiplicativeGroupPower X n) (kernel.condition _)

/-- The actual Kummer sequence is short exact when n is invertible. -/
theorem etaleKummerComplex_shortExact (X : Scheme.{u}) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    (etaleKummerComplex X n).ShortExact := by
  have : Epi (etaleMultiplicativeGroupPower X n) :=
    etaleMultiplicativeGroupPower_epi X hn hnX
  unfold etaleKummerComplex
  exact { exact := ShortComplex.exact_kernel (etaleMultiplicativeGroupPower X n) }

/-- The actual Ext connecting class of a unit section in the Kummer sequence. -/
def etaleKummerBoundary (X : Scheme.{u}) {n : ℕ} (hn : 0 < n)
    (hnX : IsUnit (n : Γ(X, ⊤))) (V : X.Etale)
    (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op V)) :
    Sheaf.H'.{u} (etaleRootsOfUnitySheaf X n) 1 V :=
  (Ext.mk₀ ((freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V
    (etaleMultiplicativeGroupSheaf X)).symm s)).comp
      (etaleKummerComplex_shortExact X hn hnX).extClass (zero_add 1)

/-- The connecting class vanishes exactly when the unit already has a
root on the given étale object. -/
theorem etaleKummerBoundary_eq_zero_iff (X : Scheme.{u}) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) (V : X.Etale)
    (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op V)) :
    etaleKummerBoundary X hn hnX V s = 0 ↔
      ∃ t, (etaleMultiplicativeGroupPower X n).hom.app (op V) t = s := by
  let P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let e : (P ⟶ etaleMultiplicativeGroupSheaf X) ≃
      (etaleMultiplicativeGroupSheaf X).obj.obj (op V) :=
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V
      (etaleMultiplicativeGroupSheaf X)
  let a : P ⟶ etaleMultiplicativeGroupSheaf X := e.symm s
  let S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleKummerComplex X n
  have hS : S.ShortExact := etaleKummerComplex_shortExact X hn hnX
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ a) rfl h
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective P S.X₂).surjective b
    have ht : t ≫ S.g = a :=
      (Ext.mk₀_bijective P S.X₃).injective (by
        simpa only [Ext.mk₀_comp_mk₀] using hb)
    refine ⟨e t, ?_⟩
    change S.g.hom.app (op V) (e t) = s
    rw [← freeAbelianSheafYonedaHomEquiv_postcomp, ht]
    exact e.apply_symm_apply s
  · rintro ⟨t, ht⟩
    let b : P ⟶ S.X₂ := e.symm t
    have hb : b ≫ S.g = a := by
      apply e.injective
      rw [freeAbelianSheafYonedaHomEquiv_postcomp]
      change S.g.hom.app (op V) (e (e.symm t)) = e (e.symm s)
      rw [e.apply_symm_apply, e.apply_symm_apply]
      exact ht
    change (Ext.mk₀ a).comp hS.extClass (zero_add 1) = 0
    rw [← hb, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero]

/-- Naturality uses the actual restriction map of the actual cohomology
presheaf. -/
theorem etaleKummerBoundary_restrict (X : Scheme.{u}) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) {V W : X.Etale}
    (f : W ⟶ V) (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op V)) :
    ((etaleRootsOfUnitySheaf X n).cohomologyPresheaf 1).map f.op
      (etaleKummerBoundary X hn hnX V s) =
        etaleKummerBoundary X hn hnX W
          ((etaleMultiplicativeGroupSheaf X).obj.map f.op s) := by
  let P : X.Etale ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    freeAbelianSheafYoneda X.smallEtaleTopology
  let F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    etaleMultiplicativeGroupSheaf X
  let eV : (P.obj V ⟶ F) ≃ F.obj.obj (op V) :=
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V F
  let eW : (P.obj W ⟶ F) ≃ F.obj.obj (op W) :=
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology W F
  let a : P.obj V ⟶ F := eV.symm s
  let b : P.obj W ⟶ F := eW.symm (F.obj.map f.op s)
  have hab : P.map f ≫ a = b := by
    apply eW.injective
    rw [freeAbelianSheafYonedaHomEquiv_precomp]
    change F.obj.map f.op (eV (eV.symm s)) = eW (eW.symm (F.obj.map f.op s))
    rw [eV.apply_symm_apply, eW.apply_symm_apply]
  change (Ext.mk₀ (P.map f)).comp
    ((Ext.mk₀ a).comp (etaleKummerComplex_shortExact X hn hnX).extClass (zero_add 1))
      (zero_add 1) = _
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hab]
  rfl

/-- The actual Kummer class is killed by an actual finite étale cover of
degree exactly n, not merely by an unspecified local covering. -/
theorem exists_degree_n_cover_killing_etaleKummerBoundary
    (X : Scheme.{u}) {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤)))
    (V : X.Etale) (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op V)) :
    ∃ (W : X.Etale) (g : W ⟶ V), IsFiniteEtale g.left ∧
      Function.Surjective g.left ∧ (∀ x : V.left, g.left.finrank x = n) ∧
      ((etaleRootsOfUnitySheaf X n).cohomologyPresheaf 1).map g.op
        (etaleKummerBoundary X hn hnX V s) = 0 := by
  obtain ⟨W, g, hf, hs, hd, t, ht⟩ := exists_finiteEtale_power_lift X hn hnX V s
  refine ⟨W, g, hf, hs, hd, ?_⟩
  rw [etaleKummerBoundary_restrict]
  exact (etaleKummerBoundary_eq_zero_iff X hn hnX W _).mpr ⟨t, ht⟩

end EtaleCohomology
