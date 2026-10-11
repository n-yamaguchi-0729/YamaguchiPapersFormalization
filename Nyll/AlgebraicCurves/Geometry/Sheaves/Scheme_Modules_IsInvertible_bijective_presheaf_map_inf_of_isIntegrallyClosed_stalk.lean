/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic.Choose
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
import Nyll.SchemeTheory.Modules.FrameFromTrivialization

/-!
# Scheme Modules Is Invertible bijective presheaf map inf of is Integrally Closed stalk
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (IsLocallyNoetherian Scheme Scheme.Modules Scheme.Modules.map_smul
  Scheme.Modules.IsInvertible Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Γ Modules Opens Modules.map_smul restrict
  Modules.IsInvertible bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (presheaf isSheaf restrict map_smul IsInvertible
  IsFrameOn exists_isFrameOn_of_pullback_iso_unit)

namespace HartogsLB

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {X : Scheme.{u}}

lemma map_map {M : X.Modules} {U V V' : X.Opens} (i : V ⟶ U) (j : V' ⟶ V) (s : Γ(M, U)) :
    M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map (j ≫ i).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

lemma map_congr {M : X.Modules} {U V : X.Opens} (i j : V ⟶ U) (s : Γ(M, U)) :
    M.presheaf.map i.op s = M.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

lemma rmap_map {U V V' : X.Opens} (i : V ⟶ U) (j : V' ⟶ V) (g : Γ(X, U)) :
    X.presheaf.map j.op (X.presheaf.map i.op g) = X.presheaf.map (j ≫ i).op g := by
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  rfl

lemma rmap_congr {U V : X.Opens} (i j : V ⟶ U) (g : Γ(X, U)) :
    X.presheaf.map i.op g = X.presheaf.map j.op g := by
  rw [Subsingleton.elim i j]

/-- The underlying sheaf of abelian groups of a sheaf of modules. -/
noncomputable def shf (M : X.Modules) : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

lemma map_smul_frame {M : X.Modules} {O W W' : X.Opens} (hWO : W ≤ O) (hW'W : W' ≤ W) (e : Γ(M, O))
    (g : Γ(X, W)) :
    M.presheaf.map (homOfLE hW'W).op (g • M.presheaf.map (homOfLE hWO).op e) =
      X.presheaf.map (homOfLE hW'W).op g • M.presheaf.map (homOfLE (hW'W.trans hWO)).op e := by
  rw [Scheme.Modules.map_smul, map_map]
  rfl

section Main

variable [IsLocallyNoetherian X] (V U : X.Opens)
  (hV : ∀ x : X, x ∈ V → IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
  (hU : ∀ x : X, x ∈ V → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
  {L : X.Modules}

include hV hU in
lemma bijective_fun (W : X.Opens) (hWV : W ≤ V) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) :=
  Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk W U (fun x hx => hV x (hWV hx))
    (fun x hx hdim => hU x (hWV hx) hdim)
include hV hU in
lemma injective_of_frames (O : X → X.Opens) (e : ∀ x, Γ(L, O x)) (hxO : ∀ x, x ∈ O x)
    (he : ∀ x, IsFrameOn (e x) (O x)) (W : X.Opens) (hWV : W ≤ V) :
    Function.Injective (L.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) := by
  intro s t hst
  rw [← sub_eq_zero] at hst ⊢
  rw [← map_sub] at hst
  set d := s - t with hd
  have hcov : W ≤ ⨆ x : X, W ⊓ O x := fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨hy, hxO y⟩⟩
  apply (shf L).eq_of_locally_eq' (fun x : X => W ⊓ O x) W (fun x => homOfLE inf_le_left) hcov
  intro x
  change L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op d =
    L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op 0
  rw [map_zero]
  obtain ⟨g, hg⟩ := ((he x) (inf_le_right : W ⊓ O x ≤ O x) inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op d)
  change g • L.presheaf.map (homOfLE (inf_le_right : W ⊓ O x ≤ O x)).op (e x) = _ at hg
  have hA : (W ⊓ O x) ⊓ U ≤ W ⊓ U := inf_le_inf_right U inf_le_left
  have h1 : L.presheaf.map (homOfLE (inf_le_left : (W ⊓ O x) ⊓ U ≤ W ⊓ O x)).op
      (L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op d) = 0 := by
    rw [map_map, map_congr _ (homOfLE hA ≫ homOfLE (inf_le_left : W ⊓ U ≤ W)), ← map_map, hst,
      map_zero]
  rw [← hg, map_smul_frame] at h1
  have hB : (W ⊓ O x) ⊓ U ≤ O x := inf_le_left.trans inf_le_right
  have hg0 : X.presheaf.map (homOfLE (inf_le_left : (W ⊓ O x) ⊓ U ≤ W ⊓ O x)).op g = 0 := by
    apply ((he x) hB hB).1
    change _ • _ = (0 : Γ(X, (W ⊓ O x) ⊓ U)) • _
    rw [zero_smul]
    exact h1
  have hg00 : g = 0 := by
    apply (bijective_fun V U hV hU (W ⊓ O x) (inf_le_left.trans hWV)).1
    rw [hg0, map_zero]
  rw [← hg, hg00, zero_smul]
include hV hU in
theorem bijective (hL : IsInvertible L) :
    Function.Bijective (L.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by
  have hfr : ∀ x : X, ∃ (O : X.Opens) (e : Γ(L, O)), x ∈ O ∧ IsFrameOn e O := fun x => by
    obtain ⟨O, hxO, ⟨eO⟩⟩ := hL.exists_trivialization x
    obtain ⟨e, he⟩ := exists_isFrameOn_of_pullback_iso_unit O eO
    exact ⟨O, e, hxO, he⟩
  choose O e hxO he using hfr
  refine ⟨injective_of_frames V U hV hU O e hxO he V le_rfl, ?_⟩
  intro σ
  have hloc : ∀ x : X, ∃ ĝ : Γ(X, V ⊓ O x),
      L.presheaf.map (homOfLE (inf_le_inf_right U inf_le_left : (V ⊓ O x) ⊓ U ≤ V ⊓ U)).op σ =
        X.presheaf.map (homOfLE (inf_le_left : (V ⊓ O x) ⊓ U ≤ V ⊓ O x)).op ĝ •
          L.presheaf.map (homOfLE (inf_le_left.trans inf_le_right : (V ⊓ O x) ⊓ U ≤ O x)).op (e x)
            := by
    intro x
    obtain ⟨g, hg⟩ := ((he x) (inf_le_left.trans inf_le_right : (V ⊓ O x) ⊓ U ≤ O x)
      (inf_le_left.trans inf_le_right : (V ⊓ O x) ⊓ U ≤ O x)).2
      (L.presheaf.map (homOfLE (inf_le_inf_right U inf_le_left : (V ⊓ O x) ⊓ U ≤ V ⊓ U)).op σ)
    obtain ⟨ĝ, hĝ⟩ := (bijective_fun V U hV hU (V ⊓ O x) inf_le_left).2 g
    exact ⟨ĝ, by rw [hĝ]; exact hg.symm⟩
  choose ĝ hĝ using hloc
  let s : ∀ x : X, Γ(L, V ⊓ O x) := fun x =>
    ĝ x • L.presheaf.map (homOfLE (inf_le_right : V ⊓ O x ≤ O x)).op (e x)
  have hsσ : ∀ x, L.presheaf.map (homOfLE (inf_le_left : (V ⊓ O x) ⊓ U ≤ V ⊓ O x)).op (s x) =
      L.presheaf.map (homOfLE (inf_le_inf_right U inf_le_left : (V ⊓ O x) ⊓ U ≤ V ⊓ U)).op σ := by
    intro x
    simp only [s]
    rw [map_smul_frame, hĝ]
  have hcompat : TopCat.Presheaf.IsCompatible L.presheaf (fun x : X => V ⊓ O x) s := by
    intro x y
    apply injective_of_frames V U hV hU O e hxO he ((V ⊓ O x) ⊓ (V ⊓ O y)) (inf_le_left.trans
      inf_le_left)
    change L.presheaf.map _ (L.presheaf.map _ (s x)) = L.presheaf.map _ (L.presheaf.map _ (s y))
    have hx' : ((V ⊓ O x) ⊓ (V ⊓ O y)) ⊓ U ≤ (V ⊓ O x) ⊓ U := inf_le_inf_right U inf_le_left
    have hy' : ((V ⊓ O x) ⊓ (V ⊓ O y)) ⊓ U ≤ (V ⊓ O y) ⊓ U := inf_le_inf_right U inf_le_right
    rw [map_map, map_map,
      map_congr _ (homOfLE hx' ≫ homOfLE (inf_le_left : (V ⊓ O x) ⊓ U ≤ V ⊓ O x)) (s x),
      map_congr _ (homOfLE hy' ≫ homOfLE (inf_le_left : (V ⊓ O y) ⊓ U ≤ V ⊓ O y)) (s y),
      ← map_map, ← map_map, hsσ, hsσ, map_map, map_map]
    exact map_congr _ _ σ
  have hcov : V ≤ ⨆ x : X, V ⊓ O x := fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨hy, hxO y⟩⟩
  obtain ⟨t, ht, -⟩ := (shf L).existsUnique_gluing' (fun x : X => V ⊓ O x) V (fun x => homOfLE
    inf_le_left)
    hcov s hcompat
  refine ⟨t, ?_⟩
  have hcovU : V ⊓ U ≤ ⨆ x : X, (V ⊓ O x) ⊓ U :=
    fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨⟨hy.1, hxO y⟩, hy.2⟩⟩
  apply (shf L).eq_of_locally_eq' (fun x : X => (V ⊓ O x) ⊓ U) (V ⊓ U)
    (fun x => homOfLE (inf_le_inf_right U inf_le_left)) hcovU
  intro x
  let a : (V ⊓ U) ⟶ V := homOfLE inf_le_left
  let b : ((V ⊓ O x) ⊓ U) ⟶ (V ⊓ U) := homOfLE (inf_le_inf_right U inf_le_left)
  let c : (V ⊓ O x) ⟶ V := homOfLE inf_le_left
  let d : ((V ⊓ O x) ⊓ U) ⟶ (V ⊓ O x) := homOfLE inf_le_left
  have htx : L.presheaf.map c.op t = s x := ht x
  exact (map_map (M := L) a b t).trans
    ((map_congr (M := L) (b ≫ a) (d ≫ c) t).trans
      ((map_map (M := L) c d t).symm.trans
        ((congrArg (fun z : Γ(L, V ⊓ O x) => L.presheaf.map d.op z) htx).trans (hsσ x))))

end Main

end AlgebraicGeometry.Scheme.Modules.HartogsLB

end Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.Opposite _root_.TopologicalSpace

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk in
theorem bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V U : X.Opens)
    (hV : ∀ x : X, x ∈ V → IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∈ V → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Function.Bijective (L.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) :=
  AlgebraicGeometry.Scheme.Modules.HartogsLB.bijective V U hV hU hL
end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation

open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  PresheafOfModules.instMonoidalClosed
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
