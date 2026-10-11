/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Topology.Sheaves.LocallySurjective
import AlgebraicCurves.Geometry.Sheaves.ModulesDet
import SchemeTheory.Modules.TensorSections

/-!
# Scheme Modules is Frame On sheafification Adjunction unit iota Multi
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.SheafifiedExteriorFrame

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace Ws31H1
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

section ModuleLevel

open Set Set.powersetCard

/-- The unique subset of Fin n of cardinality n, containing all indices. -/
@[reducible] noncomputable def uniquePowersetCardFin (n : ℕ) : Unique (Set.powersetCard (Fin n) n)
  where
  default := Set.powersetCard.ofCard (n := n) (s := (Finset.univ : Finset (Fin n))) (by simp)
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by
    rw [Fintype.card_fin]; exact Set.powersetCard.card_eq s))

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ}

lemma exists_basis_exteriorPower_top (b : Module.Basis (Fin n) A M) :
    ∃ B : Module.Basis (Set.powersetCard (Fin n) n) A (⋀[A]^n M), ∀ s, B s = exteriorPower.ιMulti
      A n b := by
  let := uniquePowersetCardFin n
  let φ : Fin n ↪o Fin n := ofFinEmbEquiv.symm (default : Set.powersetCard (Fin n) n)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective φ (Finite.injective_iff_bijective.1 φ.injective)
  refine ⟨(b.reindex σ).exteriorPower n, fun s => ?_⟩
  rw [Subsingleton.elim s default, exteriorPower.basis_apply]
  change exteriorPower.ιMulti A n ((b.reindex σ) ∘ σ) = _
  congr 1
  funext i
  simp

lemma exists_eq_smul_ιMulti (b : Module.Basis (Fin n) A M) (x : ⋀[A]^n M) :
    ∃ r : A, x = r • exteriorPower.ιMulti A n b := by
  let := uniquePowersetCardFin n
  obtain ⟨B, hB⟩ := exists_basis_exteriorPower_top b
  refine ⟨B.repr x default, ?_⟩
  conv_lhs => rw [← B.sum_repr x]
  rw [Fintype.sum_unique, hB]

lemma smul_ιMulti_injective (b : Module.Basis (Fin n) A M) :
    Function.Injective fun r : A => r • exteriorPower.ιMulti A n b := by
  let := uniquePowersetCardFin n
  obtain ⟨B, hB⟩ := exists_basis_exteriorPower_top b
  intro r r' h
  have h' := congrArg (fun y => B.repr y default) h
  simp only [← hB default] at h'
  simpa [Module.Basis.repr_self] using h'

end ModuleLevel

variable {X : Scheme.{u}} (n : ℕ)

/-- The presheaf exterior power of a module sheaf. -/
noncomputable abbrev pre (M : X.Modules) : X.PresheafOfModules :=
  (presheafExteriorPower X n).obj M.val

/-- The map from the exterior power of local sections to sections of the determinant sheaf. -/
noncomputable def toSh (M : X.Modules) (W : X.Opens) :
    (⋀[Γ(X, W)]^n Γ(M, W)) → Γ(det n M, W) :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n
    M)).app
    (op W) (show (pre n M).obj (op W) from w)

lemma toSh_add (M : X.Modules) (W : X.Opens) (w w' : ⋀[Γ(X, W)]^n Γ(M, W)) :
    toSh n M W (w + w') = toSh n M W w + toSh n M W w' :=
  map_add (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n
    M)).app
    (op W)).hom _ _

lemma toSh_zero (M : X.Modules) (W : X.Opens) : toSh n M W 0 = 0 :=
  map_zero (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n
    M)).app
    (op W)).hom

lemma toSh_smul (M : X.Modules) (W : X.Opens) (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    toSh n M W (r • w) = r • toSh n M W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom.map_smul r _

/-- Restriction of module sections along an inclusion of opens. -/
noncomputable abbrev res (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op s

lemma res_res (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : Γ(M, W₁)) : res M h₃₂ (res M h₂₁ s) = res M (h₃₂.trans h₂₁) s := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_smul (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : Γ(M, W)) :
    res M h (r • s) = X.presheaf.map (homOfLE h).op r • res M h s :=
  Modules.map_smul M (homOfLE h) r s

/-- Restriction of exterior powers of local sections through the presheaf exterior power. -/
noncomputable abbrev preMap (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W)
    (w : ⋀[Γ(X, W)]^n Γ(M, W)) : ⋀[Γ(X, W')]^n Γ(M, W') :=
  show ⋀[Γ(X, W')]^n Γ(M, W') from (pre n M).map j.op (show (pre n M).obj (op W) from w)

lemma preMap_ιMulti (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W) (m : Fin n → Γ(M, W)) :
    preMap n M j (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun k => (M.presheaf.map j.op : Γ(M, W) ⟶ _) (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti n M.val j.op m

lemma preMap_smul (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W)
    (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    preMap n M j (r • w) = X.presheaf.map j.op r • preMap n M j w :=
  (pre n M).map_smul j.op r (show (pre n M).obj (op W) from w)

lemma preMap_zero (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W) :
    preMap n M j (0 : ⋀[Γ(X, W)]^n Γ(M, W)) = 0 :=
  map_zero ((pre n M).map j.op).hom

lemma res_toSh (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    res (det n M) h (toSh n M W w) = toSh n M W' (preMap n M (homOfLE h) w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (pre n M))).naturality (homOfLE h).op
  have hx := congrArg (fun φ => φ.hom (show (pre n M).obj (op W) from w)) hnat
  exact hx.symm

lemma toSh_locally_injective (M : X.Modules) {W : X.Opens} (w w' : ⋀[Γ(X, W)]^n Γ(M, W))
    (h : toSh n M W w = toSh n M W w') (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ preMap n M (homOfLE i) w = preMap n M (homOfLE i) w' := by
  have hli : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf) := inferInstance
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf) (X := op W)
    (show (pre n M).presheaf.obj (op W) from w) (show (pre n M).presheaf.obj (op W) from w') h
  obtain ⟨V, f, hf, hxV⟩ := hmem x hx
  refine ⟨V, f.le, hxV, ?_⟩
  rw [show homOfLE f.le = f from Subsingleton.elim _ _]
  exact hf

lemma toSh_locally_surjective (M : X.Modules) {W : X.Opens} (c : Γ(det n M, W)) (x : X) (hx : x ∈
  W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ w : ⋀[Γ(X, V)]^n Γ(M, V), toSh n M V w = res (det n M)
      i c := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf))
  obtain ⟨V, i, ⟨w, hw⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  exact ⟨V, i, hxV, show ⋀[Γ(X, V)]^n Γ(M, V) from w, hw⟩

section Wedge

variable {n} {M : X.Modules} {U : X.Opens} (e : Fin n → Γ(M, U))

/-- The chosen local frame restricted to a smaller open set. -/
noncomputable abbrev eRes {W : X.Opens} (hW : W ≤ U) : Fin n → Γ(M, W) := fun i => res M hW (e i)

/-- The determinant section obtained by wedging the restricted local frame. -/
noncomputable def wedge {W : X.Opens} (hW : W ≤ U) : Γ(det n M, W) :=
  toSh n M W (exteriorPower.ιMulti _ n (eRes e hW))

lemma res_toSh_ιMulti {W : X.Opens} (hW : W ≤ U) :
    res (det n M) hW (toSh n M U (exteriorPower.ιMulti _ n e)) = wedge e hW := by
  rw [wedge, res_toSh, preMap_ιMulti]

lemma res_wedge {W W' : X.Opens} (hW : W ≤ U) (h : W' ≤ W) :
    res (det n M) h (wedge e hW) = wedge e (h.trans hW) := by
  rw [wedge, wedge, res_toSh, preMap_ιMulti]
  congr 2
  funext i
  exact res_res M hW h (e i)

variable (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
  ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))

include he in
lemma exists_basis_eq {W : X.Opens} (hW : W ≤ U) :
    ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), (b : Fin n → Γ(M, W)) = eRes e hW := by
  obtain ⟨b, hb⟩ := he W hW
  exact ⟨b, funext hb⟩

include he in
lemma smul_wedge_injective {W : X.Opens} (hW : W ≤ U) :
    Function.Injective fun g : Γ(X, W) => g • wedge e hW := by
  intro g g' hgg'
  rw [← sub_eq_zero]
  have h0 : (g - g') • wedge e hW = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr hgg'
  have h1 : toSh n M W ((g - g') • exteriorPower.ιMulti _ n (eRes e hW)) = toSh n M W 0 := by
    rw [toSh_smul, toSh_zero]; exact h0
  have key : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ X.presheaf.map (homOfLE i).op (g - g')
    = 0 := by
    intro x hx
    obtain ⟨V, i, hxV, hV⟩ := toSh_locally_injective n M _ _ h1 x hx
    refine ⟨V, i, hxV, ?_⟩
    rw [preMap_zero, preMap_smul, preMap_ιMulti] at hV
    obtain ⟨b, hb⟩ := exists_basis_eq e he (i.trans hW)
    have hfam : (fun k => (M.presheaf.map (homOfLE i).op : Γ(M, W) ⟶ _) (eRes e hW k)) = (b : Fin
      n → Γ(M, V)) := by
      rw [hb]; funext k; exact res_res M hW i (e k)
    rw [hfam] at hV
    exact smul_ιMulti_injective b (hV.trans (zero_smul _ _).symm)
  choose V hV using key
  refine X.sheaf.eq_of_locally_eq' (fun p : {x // x ∈ W} => V p.1 p.2) W
    (fun p => homOfLE (hV p.1 p.2).1) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, (hV x hx).2.1⟩) (g
      - g') 0
    (fun p => ?_)
  rw [map_zero]
  exact (hV p.1 p.2).2.2

include he in
lemma smul_wedge_surjective {W : X.Opens} (hW : W ≤ U) :
    Function.Surjective fun g : Γ(X, W) => g • wedge e hW := by
  intro c
  have key : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ r : Γ(X, V),
      res (det n M) i c = r • wedge e (i.trans hW) := by
    intro x hx
    obtain ⟨V, i, hxV, w, hw⟩ := toSh_locally_surjective n M c x hx
    obtain ⟨b, hb⟩ := exists_basis_eq e he (i.trans hW)
    obtain ⟨r, hr⟩ := exists_eq_smul_ιMulti b w
    refine ⟨V, i, hxV, r, ?_⟩
    rw [← hw, hr, toSh_smul, hb]
    rfl
  choose V i hxV r hr using key
  let ι := {x // x ∈ W}
  let Vf : ι → X.Opens := fun p => V p.1 p.2
  have hcover : W ≤ iSup Vf := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 Vf (fun p => r p.1 p.2) := by
    intro p q
    rw [Subsingleton.elim (Opens.infLELeft (Vf p) (Vf q)) (homOfLE inf_le_left),
      Subsingleton.elim (Opens.infLERight (Vf p) (Vf q)) (homOfLE inf_le_right)]
    have hpq_p : Vf p ⊓ Vf q ≤ Vf p := inf_le_left
    have hpq_q : Vf p ⊓ Vf q ≤ Vf q := inf_le_right
    have hp : (X.presheaf.map (homOfLE hpq_p).op (r p.1 p.2) : Γ(X, Vf p ⊓ Vf q)) •
        wedge e (hpq_p.trans ((i p.1 p.2).trans hW)) = res (det n M) (hpq_p.trans (i p.1 p.2)) c
          := by
      rw [← res_wedge e ((i p.1 p.2).trans hW) hpq_p, ← res_smul, ← hr p.1 p.2, res_res]
    have hq : (X.presheaf.map (homOfLE hpq_q).op (r q.1 q.2) : Γ(X, Vf p ⊓ Vf q)) •
        wedge e (hpq_q.trans ((i q.1 q.2).trans hW)) = res (det n M) (hpq_q.trans (i q.1 q.2)) c
          := by
      rw [← res_wedge e ((i q.1 q.2).trans hW) hpq_q, ← res_smul, ← hr q.1 q.2, res_res]
    apply smul_wedge_injective e he (hpq_p.trans ((i p.1 p.2).trans hW))
    exact hp.trans hq.symm
  obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' Vf W (fun p => homOfLE (i p.1 p.2)) hcover
    (fun p => r p.1 p.2) hcompat
  refine ⟨show Γ(X, W) from g, ?_⟩
  let D : TopCat.Sheaf Ab X.toTopCat := ⟨(det n M).presheaf, (det n M).isSheaf⟩
  refine D.eq_of_locally_eq' Vf W (fun p => homOfLE (i p.1 p.2)) hcover _ c (fun p => ?_)
  change res (det n M) (i p.1 p.2) ((show Γ(X, W) from g) • wedge e hW) = res (det n M) (i p.1
    p.2) c
  rw [res_smul, res_wedge, hr p.1 p.2]
  congr 1
  exact hg p

include he in
theorem isFrameOn_toSh_ιMulti :
    IsFrameOn (M := det n M) (toSh n M U (exteriorPower.ιMulti _ n e)) U := by
  intro W hWU _
  have hres : (det n M).presheaf.map (homOfLE hWU).op (toSh n M U (exteriorPower.ιMulti _ n e)) =
      wedge e hWU := res_toSh_ιMulti e hWU
  simp only [hres]
  exact ⟨smul_wedge_injective e he hWU, smul_wedge_surjective e he hWU⟩

end Wedge

end AlgebraicGeometry.Scheme.Modules.Ws31H1

theorem _root_.AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    {X : Scheme.{u}} {n : ℕ} {M : X.Modules} {U : X.Opens} (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Scheme.Modules.IsFrameOn (M := Scheme.Modules.det n M)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X n).obj M.val)).app (op U)
        (show ((Scheme.Modules.presheafExteriorPower X n).obj M.val).obj (op U) from
          exteriorPower.ιMulti (M := Γ(M, U)) Γ(X, U) n e))
      U :=
  AlgebraicGeometry.Scheme.Modules.Ws31H1.isFrameOn_toSh_ιMulti e he
end AlgebraicCurves.Geometry.Sheaves.Proofs.SheafifiedExteriorFrame
end ProofImplementation
