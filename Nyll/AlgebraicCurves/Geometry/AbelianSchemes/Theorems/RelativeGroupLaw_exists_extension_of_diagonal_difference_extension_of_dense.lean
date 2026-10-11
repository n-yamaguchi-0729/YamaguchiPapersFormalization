/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Ring.Equiv
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.Set
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sober
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Nyll.AlgebraicCurves.Geometry.Schemes.isOpen_irreducibleComponent_of_isDomain_stalk

/-!
# Relative Group Law exists extension of diagonal difference extension of dense
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense

universe u

noncomputable section


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw)

namespace RelativeGroupLaw

export _root_.GoodReductionJacobian.RelativeGroupLaw (one mul_natural mul)

namespace WeilExtField
namespace DESC

open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian


section Setup

variable {R : Type u} [CommRing R]
  {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (t : T ⟶ Spec (CommRingCat.of R))
  (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f)
  (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)

/--
The open intersection on which both the difference extension and the second-coordinate section
are defined.
-/
def Zop : (pullback t t).Opens := W ⊓ (pullback.snd t t) ⁻¹ᵁ V

theorem Zop_le_W : Zop t V W ≤ W := inf_le_left

theorem Zop_le_snd : Zop t V W ≤ (pullback.snd t t) ⁻¹ᵁ V := inf_le_right

/-- The first projection restricted to the chosen open intersection. -/
def pZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ T := (Zop t V W).ι ≫ pullback.fst t t

theorem pZ_def : pZ t V W = (Zop t V W).ι ≫ pullback.fst t t := rfl

/-- The inclusion of the chosen open intersection into the domain of the difference extension. -/
def aZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ (W : Scheme.{u}) :=
  (pullback t t).homOfLE (Zop_le_W t V W)

theorem aZ_ι : aZ t V W ≫ W.ι = (Zop t V W).ι := Scheme.homOfLE_ι _ _

/-- The second projection restricted to the open where the original section is defined. -/
def cZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ (V : Scheme.{u}) :=
  (pullback.snd t t).resLE V (Zop t V W) (Zop_le_snd t V W)

theorem cZ_ι : cZ t V W ≫ V.ι = (Zop t V W).ι ≫ pullback.snd t t := Scheme.Hom.resLE_comp_ι _ _

theorem aZ_fst : aZ t V W ≫ W.ι ≫ pullback.fst t t = pZ t V W := by
  rw [← Category.assoc, aZ_ι, pZ]

theorem aZ_snd : aZ t V W ≫ W.ι ≫ pullback.snd t t = cZ t V W ≫ V.ι := by
  rw [← Category.assoc, aZ_ι, cZ_ι]

/-- The base structure morphism of the open intersection. -/
abbrev tZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
  aZ t V W ≫ W.ι ≫ pullback.fst t t ≫ t

theorem tZ_eq : tZ t V W = pZ t V W ≫ t := by
  rw [tZ, ← aZ_fst, Category.assoc, Category.assoc]

/-- The difference extension restricted to the open intersection. -/
def dZ : SchemeHomOver (tZ t V W) f := ⟨aZ t V W ≫ d.1, by rw [Category.assoc, d.2]⟩

/-- The original section pulled back by the restricted second projection. -/
def vZ : SchemeHomOver (tZ t V W) f :=
  ⟨cZ t V W ≫ v.1, by
    rw [Category.assoc, v.2, ← Category.assoc, ← aZ_snd, Category.assoc, Category.assoc, ←
      pullback.condition]⟩

/-- The product of the restricted difference extension with the pulled-back original section. -/
def rZ : SchemeHomOver (tZ t V W) f := G.mul (tZ t V W) (dZ t V W d) (vZ t V v W)

theorem rZ_base : (rZ G t V v W d).1 ≫ f = pZ t V W ≫ t := by
  rw [(rZ G t V v W d).2, tZ_eq]

theorem comp_rZ_eq_of_fst
    (hd : ∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc,
              Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1,
            by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)
    {S : Scheme.{u}} (s : S ⟶ ↑(Zop t V W)) (b : S ⟶ ↑V) (hb : s ≫ pZ t V W = b ≫ V.ι) :
    s ≫ (rZ G t V v W d).1 = b ≫ v.1 := by
  have hψ : s ≫ tZ t V W = (s ≫ aZ t V W) ≫ W.ι ≫ pullback.fst t t ≫ t := (Category.assoc _ _
    _).symm
  have hnat := G.mul_natural (tZ t V W) ((s ≫ aZ t V W) ≫ W.ι ≫ pullback.fst t t ≫ t) s hψ
    (dZ t V W d) (vZ t V v W)
  have hb' : (s ≫ aZ t V W) ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι := by
    rw [Category.assoc, aZ_fst, hb]
  have hc' : (s ≫ aZ t V W) ≫ W.ι ≫ pullback.snd t t = (s ≫ cZ t V W) ≫ V.ι := by
    rw [Category.assoc, aZ_snd, Category.assoc]
  have key := hd S (s ≫ aZ t V W) b (s ≫ cZ t V W) hb' hc'
  have e1 : schemeHomOverComp s hψ (dZ t V W d) =
      ⟨(s ≫ aZ t V W) ≫ d.1, by rw [Category.assoc, d.2]⟩ := by
    apply Subtype.ext
    change s ≫ (aZ t V W ≫ d.1) = (s ≫ aZ t V W) ≫ d.1
    rw [Category.assoc]
  have e2 : schemeHomOverComp s hψ (vZ t V v W) =
      ⟨(s ≫ cZ t V W) ≫ v.1, by
        have h__af := (congrArg (fun k => s ≫ k) (vZ t V v W).2)
        simp only [Category.assoc] at h__af ⊢
        exact h__af⟩ := by
    apply Subtype.ext
    change s ≫ (cZ t V W ≫ v.1) = (s ≫ cZ t V W) ≫ v.1
    rw [Category.assoc]
  have h1 : s ≫ (rZ G t V v W d).1 = (schemeHomOverComp s hψ (rZ G t V v W d)).1 :=
    (schemeHomOverComp_coe s hψ _).symm
  rw [h1, rZ, hnat, e1, e2, key]

end Setup

section FieldBase

open Topology

scoped instance isDomain_sections_spec (k : Type u) [Field k] :
    IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isDomain k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isIntegrallyClosed_sections_spec (k : Type u) [Field k] :
    IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
  IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm

theorem isReduced_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

theorem exists_mem_specializes_of_dense (k : Type u) [Field k] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t] (V : T.Opens) (hV : Dense (V : Set T)) (x : T) :
    ∃ ξ : T, ξ ∈ V ∧ ξ ⤳ x := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have hZ : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hZc : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  obtain ⟨hZo, -⟩ := AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk (X := T)
    (fun p => (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk t p).1) x
  let ξ := hZ.genericPoint
  have hξ : IsGenericPoint ξ (irreducibleComponent x) := hZ.isGenericPoint_genericPoint hZc
  obtain ⟨y, hyZ, hyV⟩ := hV.inter_open_nonempty _ hZo ⟨x, mem_irreducibleComponent⟩
  refine ⟨ξ, ?_, hξ.specializes mem_irreducibleComponent⟩
  exact (hξ.specializes hyZ).mem_open V.2 hyV

end FieldBase

section Main

variable (k : Type u) [Field k]
  {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
  (t : T ⟶ Spec (CommRingCat.of k))
  (V : T.Opens)
  (W : (pullback t t).Opens)

scoped instance pZ_smooth [Smooth t] : Smooth (pZ t V W) := by
  rw [pZ_def]; infer_instance

theorem pZ_surjective [Smooth t]
    (hV : Dense (V : Set T))
    (hW : ∀ x : T, (pullback.diagonal t).base x ∈ W) :
    Function.Surjective (pZ t V W).base := by
  intro x
  obtain ⟨ξ, hξV, hξt, hξx⟩ : ∃ ξ : T, ξ ∈ V ∧ t.base ξ = t.base x ∧ ξ ⤳ x := by
    obtain ⟨ξ, hξV, hξx⟩ := exists_mem_specializes_of_dense k t V hV x
    exact ⟨ξ, hξV, Subsingleton.elim _ _, hξx⟩
  set s₀ := t.base x with hs₀
  let ιs := t.fiberι s₀
  let πs := t.fiberToSpecResidueField s₀
  let jx : Spec (T.residueField x) ⟶ Spec ((Spec (CommRingCat.of k)).residueField s₀) :=
    Spec.map (t.residueFieldMap x)
  have : Flat jx := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (t.residueFieldMap x).hom.Flat
    unfold RingHom.Flat
    let := (t.residueFieldMap x).hom.toAlgebra
    infer_instance
  have hnat : T.fromSpecResidueField x ≫ t = jx ≫ (Spec (CommRingCat.of k)).fromSpecResidueField s₀
    :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField t x).symm
  let l : Spec (T.residueField x) ⟶ t.fiber s₀ := pullback.lift (T.fromSpecResidueField x) jx hnat
  have hl : l ≫ ιs = T.fromSpecResidueField x := pullback.lift_fst _ _ _
  have hl' : l ≫ πs = jx := pullback.lift_snd _ _ _
  let F := pullback πs jx
  let pr : F ⟶ t.fiber s₀ := pullback.fst πs jx
  have hm : (pullback.snd πs jx ≫ T.fromSpecResidueField x) ≫ t = (pr ≫ ιs) ≫ t := by
    rw [Category.assoc, hnat, ← pullback.condition_assoc, Category.assoc]
    exact (congrArg (fun k => pr ≫ k) (pullback.condition (f := t)
      (g := (Spec (CommRingCat.of k)).fromSpecResidueField s₀))).symm
  let m : F ⟶ pullback t t := pullback.lift (pullback.snd πs jx ≫ T.fromSpecResidueField x) (pr ≫
    ιs) hm
  have hm1 : m ≫ pullback.fst t t = pullback.snd πs jx ≫ T.fromSpecResidueField x :=
    pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd t t = pr ≫ ιs := pullback.lift_snd _ _ _
  let σ : Spec (T.residueField x) ⟶ F := pullback.lift l (𝟙 _) (by rw [hl', Category.id_comp])
  have hσm : σ ≫ m = T.fromSpecResidueField x ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        Category.assoc,
        pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hm2, ← Category.assoc, pullback.lift_fst, hl, Category.assoc,
        pullback.diagonal_snd, Category.comp_id]
  have hσpr : σ ≫ pr ≫ ιs = T.fromSpecResidueField x := by
    rw [← Category.assoc, pullback.lift_fst, hl]
  let pt : Spec (T.residueField x) := IsLocalRing.closedPoint (T.residueField x)
  have hpt : (T.fromSpecResidueField x).base pt = x := Scheme.fromSpecResidueField_apply x pt
  let φ₀ : F := σ.base pt
  have hφ₀W : m.base φ₀ ∈ W := by
    have : m.base φ₀ = (pullback.diagonal t).base x := by
      rw [← hpt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσm]
    rw [this]; exact hW x
  have hy₀ : ιs.base (pr.base φ₀) = x := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσpr, hpt]
  obtain ⟨yξ, hyξ⟩ : ξ ∈ Set.range ιs.base := by
    rw [Scheme.Hom.range_fiberι]; exact hξt
  have hspec : yξ ⤳ pr.base φ₀ := by
    rw [← (IsPreimmersion.isEmbedding ιs).isInducing.specializes_iff, hyξ, hy₀]
    exact hξx
  obtain ⟨φ₁, hφ₁, hprφ₁⟩ := Flat.generalizingMap pr hspec
  have hwW : m.base φ₁ ∈ W := (hφ₁.map (Scheme.Hom.continuous m)).mem_open W.2 hφ₀W
  have hwsnd : (pullback.snd t t).base (m.base φ₁) = ξ := by
    rw [← Scheme.Hom.comp_apply, hm2, Scheme.Hom.comp_apply, hprφ₁, hyξ]
  have hwfst : (pullback.fst t t).base (m.base φ₁) = x := by
    rw [← Scheme.Hom.comp_apply, hm1, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hwZ : m.base φ₁ ∈ Zop t V W := by
    rw [Zop, TopologicalSpace.Opens.mem_inf]
    exact ⟨hwW, by rw [Scheme.Hom.mem_preimage, hwsnd]; exact hξV⟩
  refine ⟨⟨m.base φ₁, hwZ⟩, ?_⟩
  erw [pZ_def, Scheme.Hom.comp_apply]
  exact hwfst

theorem isReduced_kernelPair [Smooth t] :
    IsReduced (pullback (pZ t V W) (pZ t V W)) := by
  have : Smooth (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t) := inferInstance
  exact isReduced_of_smooth k (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t)

theorem dense_kernelPair_fstV [Smooth t]
    (hV : Dense (V : Set T)) :
    Dense (((pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W) ⁻¹ᵁ V : (pullback (pZ t V W) (pZ t V
      W)).Opens) :
      Set ↥(pullback (pZ t V W) (pZ t V W))) := by
  have hopen : IsOpenMap (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W).base :=
    Scheme.Hom.isOpenMap (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W)
  exact hV.preimage hopen

end Main

theorem main
    (k : Type u) [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV : Dense (V : Set T))
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc,
              Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc,
            Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by
  set p := pZ t V W with hp
  set r := rZ G t V v W d with hr
  have hsurj : Function.Surjective p.base := pZ_surjective k t V W hV hd.1
  have : Surjective p := ⟨hsurj⟩
  let K := pullback p p
  have hcompat : pullback.fst p p ≫ r.1 = pullback.snd p p ≫ r.1 := by
    have : IsReduced K := isReduced_kernelPair k t V W
    let KV : K.Opens := (pullback.fst p p ≫ p) ⁻¹ᵁ V
    have : IsDominant KV.ι := by
      rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
      exact dense_kernelPair_fstV k t V W hV
    have hfg : (pullback.fst p p ≫ r.1) ≫ f = (pullback.snd p p ≫ r.1) ≫ f := by
      rw [Category.assoc, Category.assoc, hr, rZ_base, ← hp, pullback.condition_assoc]
    refine ext_of_isDominant_of_isSeparated f hfg KV.ι ?_
    let b : (KV : Scheme.{u}) ⟶ (V : Scheme.{u}) := (pullback.fst p p ≫ p).resLE V KV le_rfl
    have hb : b ≫ V.ι = KV.ι ≫ pullback.fst p p ≫ p := Scheme.Hom.resLE_comp_ι _ _
    have h1 : (KV.ι ≫ pullback.fst p p) ≫ r.1 = b ≫ v.1 :=
      comp_rZ_eq_of_fst G t V v W d hd.2 _ b (by rw [hb, Category.assoc])
    have h2 : (KV.ι ≫ pullback.snd p p) ≫ r.1 = b ≫ v.1 :=
      comp_rZ_eq_of_fst G t V v W d hd.2 _ b (by rw [hb, Category.assoc, ← pullback.condition])
    rw [← Category.assoc, ← Category.assoc, h1, h2]
  have hmem : Sieve.generate (Presieve.singleton p) ∈ Scheme.fppfTopology.{u} T := by
    have h := (Scheme.Hom.cover.{u, 0} (P := @Flat ⊓ @LocallyOfFinitePresentation) p
      ⟨inferInstance, inferInstance⟩).mem_grothendieckTopology
    dsimp only [Scheme.Hom.cover, Precoverage.ZeroHypercover.singleton,
      PreZeroHypercover.singleton] at h
    rw [Sieve.ofArrows, Presieve.ofArrows_pUnit] at h
    exact h
  have hSA : Presieve.IsSheaf Scheme.fppfTopology.{u} (yoneda.obj A) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hSB : Presieve.IsSheaf Scheme.fppfTopology.{u} (yoneda.obj (Spec (CommRingCat.of k))) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hsheafA : Presieve.IsSheafFor (yoneda.obj A) (Presieve.singleton p) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hSA _ hmem
  have hsheafB : Presieve.IsSheafFor (yoneda.obj (Spec (CommRingCat.of k))) (Presieve.singleton p)
    := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hSB _ hmem
  rw [Presieve.isSheafFor_singleton] at hsheafA hsheafB
  have hcompat' : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ ↑(Zop t V W)), p₁ ≫ p = p₂ ≫ p →
      (yoneda.obj A).map p₁.op r.1 = (yoneda.obj A).map p₂.op r.1 := by
    intro Z p₁ p₂ h12
    change p₁ ≫ r.1 = p₂ ≫ r.1
    rw [← pullback.lift_fst p₁ p₂ h12, Category.assoc, hcompat, ← Category.assoc, pullback.lift_snd]
  obtain ⟨φ₁, hφ₁, huniq⟩ := hsheafA r.1 hcompat'
  change p ≫ φ₁ = r.1 at hφ₁
  have hover : φ₁ ≫ f = t := by
    have hcB : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ ↑(Zop t V W)), p₁ ≫ p = p₂ ≫ p →
        (yoneda.obj (Spec (CommRingCat.of k))).map p₁.op (p ≫ t) =
          (yoneda.obj (Spec (CommRingCat.of k))).map p₂.op (p ≫ t) := by
      intro Z p₁ p₂ h12
      change p₁ ≫ p ≫ t = p₂ ≫ p ≫ t
      rw [← Category.assoc, h12, Category.assoc]
    obtain ⟨ψ, hψ, hψuniq⟩ := hsheafB (p ≫ t) hcB
    have e1 : φ₁ ≫ f = ψ := hψuniq (φ₁ ≫ f) (by
      change p ≫ φ₁ ≫ f = p ≫ t
      rw [← Category.assoc, hφ₁, hr, rZ_base])
    have e2 : t = ψ := hψuniq t rfl
    rw [e1, ← e2]
  refine ⟨⟨φ₁, hover⟩, ?_⟩
  let e : (V : Scheme.{u}) ⟶ pullback t t := pullback.lift V.ι V.ι rfl
  have he : e = V.ι ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have herange : Set.range e.base ⊆ Set.range (Zop t V W).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change e.base y ∈ Zop t V W
    rw [Zop, TopologicalSpace.Opens.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [he, Scheme.Hom.comp_apply]; exact hd.1 _
    · rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact y.2
  let δ : (V : Scheme.{u}) ⟶ ↑(Zop t V W) := IsOpenImmersion.lift (Zop t V W).ι e herange
  have hδ : δ ≫ (Zop t V W).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hδp : δ ≫ p = 𝟙 _ ≫ V.ι := by
    rw [hp, pZ_def, ← Category.assoc, hδ, pullback.lift_fst, Category.id_comp]
  have hrec := comp_rZ_eq_of_fst G t V v W d hd.2 δ (𝟙 _) hδp
  rw [Category.id_comp] at hrec
  have hδp' : δ ≫ p = V.ι := by rw [hδp, Category.id_comp]
  change V.ι ≫ φ₁ = v.1
  calc V.ι ≫ φ₁ = (δ ≫ p) ≫ φ₁ := by rw [hδp']
    _ = δ ≫ r.1 := by rw [Category.assoc, hφ₁]
    _ = v.1 := hrec

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC

attribute [local instance]
  GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isDomain_sections_spec
attribute [local instance]
  GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isIntegrallyClosed_sections_spec
attribute [local instance] GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.pZ_smooth





end

attribute [local instance]
  GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isDomain_sections_spec
attribute [local instance]
  GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isIntegrallyClosed_sections_spec
attribute [local instance] GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.pZ_smooth


end RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense in
open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC in
attribute [local instance] isDomain_sections_spec isIntegrallyClosed_sections_spec pZ_smooth

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense in
open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC in
theorem exists_extension_of_diagonal_difference_extension_of_dense
    (k : Type u) [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV : Dense (V : Set T))
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc,
              Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc,
            Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 :=
  main k G t V hV v W d hd
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation
