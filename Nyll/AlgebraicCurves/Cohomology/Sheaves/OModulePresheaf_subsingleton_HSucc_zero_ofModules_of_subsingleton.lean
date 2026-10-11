/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_eq_sub_of_cocycle_of_isAffineOpen

/-! Independence of degree-one cohomology from the ordered affine cover. -/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace CoverIndepH1
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

section Rs
variable (M : X.Modules)

/-- Restriction of a module section along an inclusion of open sets. -/
def rs {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) : Γ(M, V) := M.presheaf.map (homOfLE h).op x

theorem rs_def {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) : rs M h x = M.presheaf.map (homOfLE h).op
  x := rfl

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(M, U)) : rs M h' (rs M h x) = rs M
  (h'.trans h) x := by
  simp only [rs, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem rs_irrel {U V : X.Opens} (h h' : V ≤ U) (x : Γ(M, U)) : rs M h x = rs M h' x := rfl

theorem rs_refl {U : X.Opens} (x : Γ(M, U)) : rs M (le_refl U) x = x := by
  rw [rs_def, Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), M.presheaf.map_id]
  rfl

theorem rs_sub {U V : X.Opens} (h : V ≤ U) (x y : Γ(M, U)) : rs M h (x - y) = rs M h x - rs M h y
  := map_sub _ _ _
theorem rs_add {U V : X.Opens} (h : V ≤ U) (x y : Γ(M, U)) : rs M h (x + y) = rs M h x + rs M h y
  := map_add _ _ _
theorem rs_zero {U V : X.Opens} (h : V ≤ U) : rs M h (0 : Γ(M, U)) = 0 := map_zero _
theorem rs_neg {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) : rs M h (-x) = -rs M h x := map_neg _ _

theorem rs_injective_of_eq {U V : X.Opens} (e : V = U) : Function.Injective (rs M e.le) := by
  subst e
  intro a b hab
  rwa [rs_refl, rs_refl] at hab

/-- The underlying sheaf of abelian groups of the module sheaf. -/
def sh : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem glue {ι : Type u} (Q : ι → X.Opens) {V : X.Opens} (hQ : ∀ i, Q i ≤ V) (hcov : V ≤ ⨆ i, Q i)
    (x : ∀ i, Γ(M, Q i))
    (hx : ∀ i j, rs M (inf_le_left : Q i ⊓ Q j ≤ Q i) (x i) = rs M (inf_le_right : Q i ⊓ Q j ≤ Q j)
      (x j)) :
    ∃ s : Γ(M, V), ∀ i, rs M (hQ i) s = x i := by
  have hcompat : TopCat.Presheaf.IsCompatible (sh M).1 Q x := by
    intro i j
    have h1 : (sh M).1.map (Opens.infLELeft (Q i) (Q j)).op (x i) = rs M (inf_le_left : Q i ⊓ Q j ≤
      Q i) (x i) := by
      rw [rs_def, Subsingleton.elim (Opens.infLELeft (Q i) (Q j)) (homOfLE inf_le_left)]; rfl
    have h2 : (sh M).1.map (Opens.infLERight (Q i) (Q j)).op (x j) = rs M (inf_le_right : Q i ⊓ Q j
      ≤ Q j) (x j) := by
      rw [rs_def, Subsingleton.elim (Opens.infLERight (Q i) (Q j)) (homOfLE inf_le_right)]; rfl
    rw [h1, h2]
    exact hx i j
  obtain ⟨s, hs, -⟩ := (sh M).existsUnique_gluing' Q V (fun i => homOfLE (hQ i)) hcov x hcompat
  exact ⟨s, hs⟩

theorem locality {ι : Type u} (Q : ι → X.Opens) {V : X.Opens} (hQ : ∀ i, Q i ≤ V) (hcov : V ≤ ⨆ i,
  Q i)
    (s t : Γ(M, V)) (h : ∀ i, rs M (hQ i) s = rs M (hQ i) t) : s = t :=
  (sh M).eq_of_locally_eq' Q V (fun i => homOfLE (hQ i)) hcov s t h

end Rs

section Idx
variable (K : X.OrderedAffineCover)

/-- The zero-simplex at a cover index. -/
def idx0 (a : K.ι) : K.Idx 0 := ⟨fun _ => a, fun i j h => absurd (Subsingleton.elim (α := Fin 1) i
  j) (ne_of_lt h)⟩

/-- The one-simplex formed by two increasing cover indices. -/
def idx1 {a b : K.ι} (hab : a < b) : K.Idx 1 :=
  ⟨![a, b], by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · exact hab
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

/-- The two-simplex formed by three increasing cover indices. -/
def idx2 {a b c : K.ι} (hab : a < b) (hbc : b < c) : K.Idx 2 :=
  ⟨![a, b, c], by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · exact hab
    · exact hab.trans hbc
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)
    · exact hbc
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem inter_idx0_le (a : K.ι) : K.inter (idx0 K a) ≤ K.U a := K.inter_le _ 0
theorem le_inter_idx0 (a : K.ι) : K.U a ≤ K.inter (idx0 K a) := le_iInf fun _ => le_rfl

theorem inter_le_pair (s : K.Idx 1) : K.inter s ≤ K.U (s.1 0) ⊓ K.U (s.1 1) :=
  le_inf (K.inter_le s 0) (K.inter_le s 1)

theorem pair_le_inter (s : K.Idx 1) : K.U (s.1 0) ⊓ K.U (s.1 1) ≤ K.inter s :=
  le_iInf fun k => by
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

theorem inter_pair_eq (s : K.Idx 1) : K.inter s = K.U (s.1 0) ⊓ K.U (s.1 1) :=
  le_antisymm (inter_le_pair K s) (pair_le_inter K s)

theorem inter_le_triple (t : K.Idx 2) : K.inter t ≤ K.U (t.1 0) ⊓ K.U (t.1 1) ⊓ K.U (t.1 2) :=
  le_inf (le_inf (K.inter_le t 0) (K.inter_le t 1)) (K.inter_le t 2)

theorem lt01 (s : K.Idx 1) : s.1 0 < s.1 1 := s.2 (show (0 : Fin 2) < 1 by decide)
theorem lt01' (t : K.Idx 2) : t.1 0 < t.1 1 := t.2 (show (0 : Fin 3) < 1 by decide)
theorem lt12' (t : K.Idx 2) : t.1 1 < t.1 2 := t.2 (show (1 : Fin 3) < 2 by decide)

theorem face_idx1_zero {a b : K.ι} (hab : a < b) : K.face (idx1 K hab) 0 = idx0 K b := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem face_idx1_one {a b : K.ι} (hab : a < b) : K.face (idx1 K hab) 1 = idx0 K a := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem eq_idx1 (s : K.Idx 1) : s = idx1 K (lt01 K s) := by
  apply Subtype.ext; funext k; fin_cases k <;> rfl

theorem face1_val (s : K.Idx 1) (j : Fin 2) : (K.face s j).1 0 = s.1 (j.succAbove 0) := rfl
theorem face2_val (t : K.Idx 2) (j : Fin 3) (k : Fin 2) : (K.face t j).1 k = t.1 (j.succAbove k) :=
  rfl

end Idx

section Dif
variable {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R)) (M : X.Modules) (K : X.OrderedAffineCover)

theorem res_eq_rs {O O' : X.Opens} (h : O ≤ O') (x : Γ(M, O')) :
    (OModulePresheaf.ofModules π M).res h (show (OModulePresheaf.ofModules π M).obj O' from x) = rs
      M h x := rfl

theorem d_zero_apply (e : (OModulePresheaf.ofModules π M).cochain K 0) (s : K.Idx 1) :
    (OModulePresheaf.ofModules π M).d K 0 e s
      = rs M (K.inter_le_inter_face s 0) (e (K.face s 0)) - rs M (K.inter_le_inter_face s 1) (e
        (K.face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
  rw [← sub_eq_add_neg]
  rfl

theorem d_one_apply (c : (OModulePresheaf.ofModules π M).cochain K 1) (t : K.Idx 2) :
    (OModulePresheaf.ofModules π M).d K 1 c t
      = rs M (K.inter_le_inter_face t 0) (c (K.face t 0)) - rs M (K.inter_le_inter_face t 1) (c
        (K.face t 1))
        + rs M (K.inter_le_inter_face t 2) (c (K.face t 2)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_smul, ← sub_eq_add_neg]
  rfl

theorem rs_at_eq {i : ℕ} (c : (OModulePresheaf.ofModules π M).cochain K i) {σ τ : K.Idx i} (e : σ =
  τ)
    {O : X.Opens} (hσ : O ≤ K.inter σ) (hτ : O ≤ K.inter τ) :
    rs M hσ (c σ) = rs M hτ (c τ) := by
  subst e; rfl

/-- The component of a one-cochain restricted to a pairwise intersection. -/
def cm (c : (OModulePresheaf.ofModules π M).cochain K 1) {a b : K.ι} (hab : a < b) : Γ(M, K.U a ⊓
  K.U b) :=
  rs M (pair_le_inter K (idx1 K hab)) (c (idx1 K hab))

theorem rs_cm (c : (OModulePresheaf.ofModules π M).cochain K 1) (s : K.Idx 1) :
    rs M (inter_le_pair K s) (cm π M K c (lt01 K s)) = c s := by
  exact (rs_rs M _ _ _).trans
    ((rs_at_eq π M K c (eq_idx1 K s).symm _ le_rfl).trans (rs_refl M _))

theorem cocycle (c : (OModulePresheaf.ofModules π M).cochain K 1) (hc : (OModulePresheaf.ofModules
  π M).d K 1 c = 0)
    {a b e : K.ι} (hab : a < b) (hbe : b < e) :
    rs M (le_inf (inf_le_left.trans inf_le_right) inf_le_right : K.U a ⊓ K.U b ⊓ K.U e ≤ K.U b ⊓
      K.U e) (cm π M K c hbe)
      - rs M (le_inf (inf_le_left.trans inf_le_left) inf_le_right : K.U a ⊓ K.U b ⊓ K.U e ≤ K.U a ⊓
        K.U e)
          (cm π M K c (hab.trans hbe))
      + rs M (inf_le_left : K.U a ⊓ K.U b ⊓ K.U e ≤ K.U a ⊓ K.U b) (cm π M K c hab) = 0 := by
  change (s : K.Idx 1) → Γ(M, K.inter s) at c
  have ht := (d_one_apply π M K c (idx2 K hab hbe)).symm.trans
    (congrFun hc (idx2 K hab hbe))
  change _ = (0 : Γ(M, K.inter (idx2 K hab hbe))) at ht
  have f0 : K.face (idx2 K hab hbe) 0 = idx1 K hbe :=
    by apply Subtype.ext; funext k; fin_cases k <;> rfl
  have f1 : K.face (idx2 K hab hbe) 1 = idx1 K (hab.trans hbe) :=
    by apply Subtype.ext; funext k; fin_cases k <;> rfl
  have f2 : K.face (idx2 K hab hbe) 2 = idx1 K hab :=
    by apply Subtype.ext; funext k; fin_cases k <;> rfl
  have hle : K.U a ⊓ K.U b ⊓ K.U e ≤ K.inter (idx2 K hab hbe) := le_iInf fun k => by
    fin_cases k
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have := congrArg (rs M hle) ht
  rw [rs_zero, rs_add, rs_sub, rs_rs, rs_rs, rs_rs] at this
  have g0 : rs M (hle.trans (K.inter_le_inter_face (idx2 K hab hbe) 0)) (c (K.face (idx2 K hab hbe)
    0))
      = rs M ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : K.U a ⊓ K.U b ⊓ K.U e ≤ K.U b
        ⊓ K.U e).trans
          (pair_le_inter K (idx1 K hbe))) (c (idx1 K hbe)) := rs_at_eq π M K c f0 _ _
  have g1 : rs M (hle.trans (K.inter_le_inter_face (idx2 K hab hbe) 1)) (c (K.face (idx2 K hab hbe)
    1))
      = rs M ((le_inf (inf_le_left.trans inf_le_left) inf_le_right : K.U a ⊓ K.U b ⊓ K.U e ≤ K.U a
        ⊓ K.U e).trans
          (pair_le_inter K (idx1 K (hab.trans hbe)))) (c (idx1 K (hab.trans hbe))) := rs_at_eq π M
            K c f1 _ _
  have g2 : rs M (hle.trans (K.inter_le_inter_face (idx2 K hab hbe) 2)) (c (K.face (idx2 K hab hbe)
    2))
      = rs M ((inf_le_left : K.U a ⊓ K.U b ⊓ K.U e ≤ K.U a ⊓ K.U b).trans
          (pair_le_inter K (idx1 K hab))) (c (idx1 K hab)) := rs_at_eq π M K c f2 _ _
  rw [g0, g1, g2] at this
  exact (congrArg₂ (fun x y : Γ(M, K.U a ⊓ K.U b ⊓ K.U e) => x + y)
    (congrArg₂ (fun x y : Γ(M, K.U a ⊓ K.U b ⊓ K.U e) => x - y)
      (rs_rs M _ _ _) (rs_rs M _ _ _)) (rs_rs M _ _ _)).trans this

end Dif

section Chase

variable {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R)) [IsSeparated π] (M : X.Modules)
  (htriv : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
    Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
  (K K' : X.OrderedAffineCover)

include π in
theorem isAffineOpen_inf {P Q : X.Opens} (hP : IsAffineOpen P) (hQ : IsAffineOpen Q) : IsAffineOpen
  (P ⊓ Q) := by
  have : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) P (by simp) Q (by simp) hP hQ
omit [IsSeparated π] in
theorem cover_by_K' (W : X.Opens) : W ≤ ⨆ k, W ⊓ K'.U k := by
  rw [← inf_iSup_eq, K'.iSup_eq_top, inf_top_eq]
omit [IsSeparated π] in
theorem cover_by_K (W : X.Opens) : W ≤ ⨆ a, K.U a ⊓ W := by
  rw [← iSup_inf_eq, K.iSup_eq_top, top_inf_eq]
include htriv in
theorem step1 (c : (OModulePresheaf.ofModules π M).cochain K' 1) (hc : (OModulePresheaf.ofModules π
  M).d K' 1 c = 0)
    (a : K.ι) :
    ∃ v : ∀ k : K'.ι, Γ(M, K.U a ⊓ K'.U k), ∀ k l : K'.ι, ∀ hkl : k < l,
      rs M (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (K.U a ⊓ K'.U k) ⊓ (K.U a ⊓ K'.U l) ≤ K'.U k ⊓ K'.U l) (cm π M K' c hkl)
        = rs M inf_le_right (v l) - rs M inf_le_left (v k) := by
  classical
  let P : K'.ι → X.Opens := fun k => K.U a ⊓ K'.U k
  let u : ∀ k l : K'.ι, Γ(M, P k ⊓ P l) := fun k l =>
    if hkl : k < l then
      rs M (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (cm π M K' c
        hkl)
    else 0
  have hu : ∀ k l (hkl : k < l), u k l
      = rs M (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (cm π M K'
        c hkl) :=
    fun k l hkl => dite_eq_left hkl
  obtain ⟨v, hv⟩ := Scheme.Modules.exists_eq_sub_of_cocycle_of_isAffineOpen M htriv (K.U a)
    (K.isAffineOpen a) P
    (fun k => inf_le_left) (fun k => isAffineOpen_inf π (K.isAffineOpen a) (K'.isAffineOpen k))
      (cover_by_K' K' _) u
    (fun i j k hij hjk => by
      change rs M _ (u j k) - rs M _ (u i k) + rs M _ (u i j) = 0
      rw [hu j k hjk, hu i k (hij.trans hjk), hu i j hij, rs_rs, rs_rs, rs_rs]
      have h3 : P i ⊓ P j ⊓ P k ≤ K'.U i ⊓ K'.U j ⊓ K'.U k :=
        le_inf (le_inf ((inf_le_left.trans inf_le_left).trans inf_le_right)
          ((inf_le_left.trans inf_le_right).trans inf_le_right)) (inf_le_right.trans inf_le_right)
      have := congrArg (rs M h3) (cocycle π M K' c hc hij hjk)
      rw [rs_zero, rs_add, rs_sub, rs_rs, rs_rs, rs_rs] at this
      exact this)
  exact ⟨v, fun k l hkl => by rw [← hu k l hkl]; exact hv k l hkl⟩

theorem compat_of_lt {ι : Type u} [LinearOrder ι] (Q : ι → X.Opens) (x : ∀ i, Γ(M, Q i))
    (h : ∀ i j, i < j → rs M (inf_le_left : Q i ⊓ Q j ≤ Q i) (x i) = rs M (inf_le_right : Q i ⊓ Q j
      ≤ Q j) (x j)) :
    ∀ i j, rs M (inf_le_left : Q i ⊓ Q j ≤ Q i) (x i) = rs M (inf_le_right : Q i ⊓ Q j ≤ Q j) (x j)
      := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h i j hij
  · rfl
  · have := congrArg (rs M (le_of_eq (inf_comm (Q i) (Q j)))) (h j i hji)
    rw [rs_rs, rs_rs] at this
    exact this.symm
omit [IsSeparated π] in
theorem step2 (c : (OModulePresheaf.ofModules π M).cochain K' 1)
    (v : ∀ (a : K.ι) (k : K'.ι), Γ(M, K.U a ⊓ K'.U k))
    (hv : ∀ (a : K.ι) (k l : K'.ι) (hkl : k < l),
      rs M (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (K.U a ⊓ K'.U k) ⊓ (K.U a ⊓ K'.U l) ≤ K'.U k ⊓ K'.U l) (cm π M K' c hkl)
        = rs M inf_le_right (v a l) - rs M inf_le_left (v a k))
    (a b : K.ι) :
    ∃ δ : Γ(M, K.U a ⊓ K.U b), ∀ k : K'.ι,
      rs M (inf_le_left : (K.U a ⊓ K.U b) ⊓ K'.U k ≤ K.U a ⊓ K.U b) δ
        = rs M (le_inf (inf_le_left.trans inf_le_right) inf_le_right : (K.U a ⊓ K.U b) ⊓ K'.U k ≤
          K.U b ⊓ K'.U k) (v b k)
          - rs M (le_inf (inf_le_left.trans inf_le_left) inf_le_right : (K.U a ⊓ K.U b) ⊓ K'.U k ≤
            K.U a ⊓ K'.U k) (v a k) := by
  let Q : K'.ι → X.Opens := fun k => (K.U a ⊓ K.U b) ⊓ K'.U k
  let x : ∀ k, Γ(M, Q k) := fun k =>
    rs M (le_inf (inf_le_left.trans inf_le_right) inf_le_right : Q k ≤ K.U b ⊓ K'.U k) (v b k)
      - rs M (le_inf (inf_le_left.trans inf_le_left) inf_le_right : Q k ≤ K.U a ⊓ K'.U k) (v a k)
  have hx := compat_of_lt M Q x fun k l hkl => by
    simp only [x, rs_sub, rs_rs]
    have hWa : Q k ⊓ Q l ≤ (K.U a ⊓ K'.U k) ⊓ (K.U a ⊓ K'.U l) :=
      le_inf (le_inf ((inf_le_left.trans inf_le_left).trans inf_le_left) (inf_le_left.trans
        inf_le_right))
        (le_inf ((inf_le_right.trans inf_le_left).trans inf_le_left) (inf_le_right.trans
          inf_le_right))
    have hWb : Q k ⊓ Q l ≤ (K.U b ⊓ K'.U k) ⊓ (K.U b ⊓ K'.U l) :=
      le_inf (le_inf ((inf_le_left.trans inf_le_left).trans inf_le_right) (inf_le_left.trans
        inf_le_right))
        (le_inf ((inf_le_right.trans inf_le_left).trans inf_le_right) (inf_le_right.trans
          inf_le_right))
    have ha := congrArg (rs M hWa) (hv a k l hkl)
    have hb := congrArg (rs M hWb) (hv b k l hkl)
    rw [rs_rs, rs_sub, rs_rs, rs_rs] at ha hb
    have hab : rs M (hWb.trans inf_le_right) (v b l) - rs M (hWb.trans inf_le_left) (v b k)
        = rs M (hWa.trans inf_le_right) (v a l) - rs M (hWa.trans inf_le_left) (v a k) :=
          hb.symm.trans ha
    exact (sub_eq_sub_iff_sub_eq_sub.mp hab).symm
  obtain ⟨δ, hδ⟩ := glue M Q (fun k => inf_le_left) (cover_by_K' K' _) x hx
  exact ⟨δ, hδ⟩

/-- The one-cochain obtained by restricting sections on pairwise intersections. -/
def δK (δ : ∀ a b : K.ι, Γ(M, K.U a ⊓ K.U b)) : (OModulePresheaf.ofModules π M).cochain K 1 := fun
  s =>
  rs M (inter_le_pair K s) (δ (s.1 0) (s.1 1))
omit [IsSeparated π] in
theorem step3 (v : ∀ (a : K.ι) (k : K'.ι), Γ(M, K.U a ⊓ K'.U k)) (δ : ∀ a b : K.ι, Γ(M, K.U a ⊓ K.U
  b))
    (hδ : ∀ (a b : K.ι) (k : K'.ι),
      rs M (inf_le_left : (K.U a ⊓ K.U b) ⊓ K'.U k ≤ K.U a ⊓ K.U b) (δ a b)
        = rs M (le_inf (inf_le_left.trans inf_le_right) inf_le_right : (K.U a ⊓ K.U b) ⊓ K'.U k ≤
          K.U b ⊓ K'.U k) (v b k)
          - rs M (le_inf (inf_le_left.trans inf_le_left) inf_le_right : (K.U a ⊓ K.U b) ⊓ K'.U k ≤
            K.U a ⊓ K'.U k) (v a k)) :
    (OModulePresheaf.ofModules π M).d K 1 (δK π M K δ) = 0 := by
  funext t
  rw [d_one_apply]
  change rs M (K.inter_le_inter_face t 0)
      (rs M (inter_le_pair K (K.face t 0))
        (δ ((K.face t 0).1 0) ((K.face t 0).1 1))) -
    rs M (K.inter_le_inter_face t 1)
      (rs M (inter_le_pair K (K.face t 1))
        (δ ((K.face t 1).1 0) ((K.face t 1).1 1))) +
    rs M (K.inter_le_inter_face t 2)
      (rs M (inter_le_pair K (K.face t 2))
        (δ ((K.face t 2).1 0) ((K.face t 2).1 1))) = (0 : Γ(M, K.inter t))
  rw [rs_rs, rs_rs, rs_rs]
  apply locality M (fun k => K.inter t ⊓ K'.U k) (fun k => inf_le_left) (cover_by_K' K' _)
  intro k
  rw [rs_zero, rs_add, rs_sub, rs_rs, rs_rs, rs_rs]
  have e0 : K.inter t ⊓ K'.U k ≤ (K.U (t.1 1) ⊓ K.U (t.1 2)) ⊓ K'.U k :=
    le_inf (inf_le_left.trans (le_inf (K.inter_le t 1) (K.inter_le t 2))) inf_le_right
  have e1 : K.inter t ⊓ K'.U k ≤ (K.U (t.1 0) ⊓ K.U (t.1 2)) ⊓ K'.U k :=
    le_inf (inf_le_left.trans (le_inf (K.inter_le t 0) (K.inter_le t 2))) inf_le_right
  have e2 : K.inter t ⊓ K'.U k ≤ (K.U (t.1 0) ⊓ K.U (t.1 1)) ⊓ K'.U k :=
    le_inf (inf_le_left.trans (le_inf (K.inter_le t 0) (K.inter_le t 1))) inf_le_right
  have h0 := congrArg (rs M e0) (hδ (t.1 1) (t.1 2) k)
  have h1 := congrArg (rs M e1) (hδ (t.1 0) (t.1 2) k)
  have h2 := congrArg (rs M e2) (hδ (t.1 0) (t.1 1) k)
  rw [rs_rs, rs_sub, rs_rs, rs_rs] at h0 h1 h2
  change rs M _ (δ (t.1 1) (t.1 2)) - rs M _ (δ (t.1 0) (t.1 2)) + rs M _ (δ (t.1 0) (t.1 1)) = (0
    : Γ(M, K.inter t ⊓ K'.U k))
  rw [h0, h1, h2]
  abel
omit [IsSeparated π] in
theorem step4 (h : Subsingleton ((OModulePresheaf.ofModules π M).HSucc K 0))
    (δ : ∀ a b : K.ι, Γ(M, K.U a ⊓ K.U b)) (hd : (OModulePresheaf.ofModules π M).d K 1 (δK π M K δ)
      = 0) :
    ∃ η : ∀ a : K.ι, Γ(M, K.U a), ∀ a b : K.ι, a < b →
      δ a b = rs M inf_le_right (η b) - rs M inf_le_left (η a) := by
  have hz : (Submodule.Quotient.mk ⟨δK π M K δ, LinearMap.mem_ker.mpr hd⟩ :
      (OModulePresheaf.ofModules π M).HSucc K 0) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨ηK, hηK⟩ := hz
  change (s : K.Idx 0) → Γ(M, K.inter s) at ηK
  change (OModulePresheaf.ofModules π M).d K 0 ηK = δK π M K δ at hηK
  refine ⟨fun a => rs M (le_inter_idx0 K a) (ηK (idx0 K a)), fun a b hab => ?_⟩
  change δ a b = rs M inf_le_right (rs M (le_inter_idx0 K b) (ηK (idx0 K b)))
    - rs M inf_le_left (rs M (le_inter_idx0 K a) (ηK (idx0 K a)))
  rw [rs_rs, rs_rs]
  have hs := (d_zero_apply π M K ηK (idx1 K hab)).symm.trans
    (congrFun hηK (idx1 K hab))
  change rs M (K.inter_le_inter_face (idx1 K hab) 0) (ηK (K.face (idx1 K hab) 0)) -
    rs M (K.inter_le_inter_face (idx1 K hab) 1) (ηK (K.face (idx1 K hab) 1)) =
    rs M (inter_le_pair K (idx1 K hab)) (δ a b) at hs
  have := congrArg (rs M (pair_le_inter K (idx1 K hab))) hs
  have hnormal :
      rs M ((pair_le_inter K (idx1 K hab)).trans (K.inter_le_inter_face (idx1 K hab) 0))
        (ηK (K.face (idx1 K hab) 0)) -
      rs M ((pair_le_inter K (idx1 K hab)).trans (K.inter_le_inter_face (idx1 K hab) 1))
        (ηK (K.face (idx1 K hab) 1)) = δ a b :=
    (congrArg₂ (fun x y : Γ(M, K.U a ⊓ K.U b) => x - y)
      (rs_rs M _ _ _) (rs_rs M _ _ _)).symm.trans
      ((rs_sub M _ _ _).symm.trans
        (this.trans ((rs_rs M _ _ _).trans (rs_refl M _))))
  have h0 : rs M ((pair_le_inter K (idx1 K hab)).trans (K.inter_le_inter_face (idx1 K hab) 0))
        (ηK (K.face (idx1 K hab) 0))
      = rs M ((inf_le_right : K.U a ⊓ K.U b ≤ K.U b).trans (le_inter_idx0 K b)) (ηK (idx0 K b)) :=
    rs_at_eq π M K ηK (face_idx1_zero K hab) _ _
  have h1 : rs M ((pair_le_inter K (idx1 K hab)).trans (K.inter_le_inter_face (idx1 K hab) 1))
        (ηK (K.face (idx1 K hab) 1))
      = rs M ((inf_le_left : K.U a ⊓ K.U b ≤ K.U a).trans (le_inter_idx0 K a)) (ηK (idx0 K a)) :=
    rs_at_eq π M K ηK (face_idx1_one K hab) _ _
  rw [h0, h1] at hnormal
  exact hnormal.symm

theorem step5 (v : ∀ (a : K.ι) (k : K'.ι), Γ(M, K.U a ⊓ K'.U k)) (δ : ∀ a b : K.ι, Γ(M, K.U a ⊓ K.U
  b))
    (hδ : ∀ (a b : K.ι) (k : K'.ι),
      rs M (inf_le_left : (K.U a ⊓ K.U b) ⊓ K'.U k ≤ K.U a ⊓ K.U b) (δ a b)
        = rs M (le_inf (inf_le_left.trans inf_le_right) inf_le_right : (K.U a ⊓ K.U b) ⊓ K'.U k ≤
          K.U b ⊓ K'.U k) (v b k)
          - rs M (le_inf (inf_le_left.trans inf_le_left) inf_le_right : (K.U a ⊓ K.U b) ⊓ K'.U k ≤
            K.U a ⊓ K'.U k) (v a k))
    (η : ∀ a : K.ι, Γ(M, K.U a))
    (hη : ∀ a b : K.ι, a < b → δ a b = rs M inf_le_right (η b) - rs M inf_le_left (η a)) (k : K'.ι)
      :
    ∃ e : Γ(M, K'.U k), ∀ a : K.ι,
      rs M (inf_le_right : K.U a ⊓ K'.U k ≤ K'.U k) e = v a k - rs M inf_le_left (η a) := by
  let Q : K.ι → X.Opens := fun a => K.U a ⊓ K'.U k
  let f : ∀ a, Γ(M, Q a) := fun a => v a k - rs M inf_le_left (η a)
  have hf := compat_of_lt M Q f fun a b hab => by
    simp only [f, rs_sub, rs_rs]
    have hW : Q a ⊓ Q b ≤ (K.U a ⊓ K.U b) ⊓ K'.U k :=
      le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
        (inf_le_left.trans inf_le_right)
    have h1 := congrArg (rs M hW) (hδ a b k)
    rw [hη a b hab] at h1
    simp only [rs_sub, rs_rs] at h1
    have h2 := sub_eq_sub_iff_sub_eq_sub.mp h1
    have h3 := congrArg Neg.neg h2
    simp only [neg_sub] at h3
    exact h3.symm
  obtain ⟨e, he⟩ := glue M Q (fun a => inf_le_right) (cover_by_K K _) f hf
  exact ⟨e, he⟩
omit [IsSeparated π] in
theorem step6 (c : (OModulePresheaf.ofModules π M).cochain K' 1)
    (v : ∀ (a : K.ι) (k : K'.ι), Γ(M, K.U a ⊓ K'.U k))
    (hv : ∀ (a : K.ι) (k l : K'.ι) (hkl : k < l),
      rs M (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (K.U a ⊓ K'.U k) ⊓ (K.U a ⊓ K'.U l) ≤ K'.U k ⊓ K'.U l) (cm π M K' c hkl)
        = rs M inf_le_right (v a l) - rs M inf_le_left (v a k))
    (η : ∀ a : K.ι, Γ(M, K.U a)) (e : ∀ k : K'.ι, Γ(M, K'.U k))
    (he : ∀ (k : K'.ι) (a : K.ι),
      rs M (inf_le_right : K.U a ⊓ K'.U k ≤ K'.U k) (e k) = v a k - rs M inf_le_left (η a))
    {k l : K'.ι} (hkl : k < l) :
    rs M inf_le_right (e l) - rs M inf_le_left (e k) = cm π M K' c hkl := by
  apply locality M (fun a => K.U a ⊓ (K'.U k ⊓ K'.U l)) (fun a => inf_le_right) (cover_by_K K _)
  intro a
  rw [rs_sub, rs_rs, rs_rs]
  have hWk : K.U a ⊓ (K'.U k ⊓ K'.U l) ≤ K.U a ⊓ K'.U k := le_inf inf_le_left (inf_le_right.trans
    inf_le_left)
  have hWl : K.U a ⊓ (K'.U k ⊓ K'.U l) ≤ K.U a ⊓ K'.U l := le_inf inf_le_left (inf_le_right.trans
    inf_le_right)
  have hk := congrArg (rs M hWk) (he k a)
  have hl := congrArg (rs M hWl) (he l a)
  rw [rs_rs, rs_sub, rs_rs] at hk hl
  rw [hl, hk]
  have hW : K.U a ⊓ (K'.U k ⊓ K'.U l) ≤ (K.U a ⊓ K'.U k) ⊓ (K.U a ⊓ K'.U l) := le_inf hWk hWl
  have hc := congrArg (rs M hW) (hv a k l hkl)
  rw [rs_rs, rs_sub, rs_rs, rs_rs] at hc
  rw [hc]
  abel
include htriv in
theorem chase (h : Subsingleton ((OModulePresheaf.ofModules π M).HSucc K 0))
    (c : (OModulePresheaf.ofModules π M).cochain K' 1) (hc : (OModulePresheaf.ofModules π M).d K' 1
      c = 0) :
    ∃ eK : (OModulePresheaf.ofModules π M).cochain K' 0, (OModulePresheaf.ofModules π M).d K' 0 eK
      = c := by
  choose v hv using step1 π M htriv K K' c hc
  choose δ hδ using step2 π M K K' c v hv
  obtain ⟨η, hη⟩ := step4 π M K h δ (step3 π M K K' v δ hδ)
  choose e he using step5 M K K' v δ hδ η hη
  let eK : (s : K'.Idx 0) → Γ(M, K'.inter s) :=
    fun s => rs M (K'.inter_le s 0) (e (s.1 0))
  refine ⟨eK, funext fun s => ?_⟩
  refine (d_zero_apply π M K' eK s).trans ?_
  change rs M (K'.inter_le_inter_face s 0)
      (rs M (K'.inter_le (K'.face s 0) 0) (e ((K'.face s 0).1 0))) -
    rs M (K'.inter_le_inter_face s 1)
      (rs M (K'.inter_le (K'.face s 1) 0) (e ((K'.face s 1).1 0))) = c s
  rw [rs_rs, rs_rs, ← rs_cm π M K' c s, ← step6 π M K K' c v hv η e he (lt01 K' s),
    rs_sub, rs_rs, rs_rs]
  rfl
include htriv in
theorem main (h : Subsingleton ((OModulePresheaf.ofModules π M).HSucc K 0)) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc K' 0) := by
  refine subsingleton_of_forall_eq 0 fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, LinearMap.mem_range]
    obtain ⟨eK, heK⟩ := chase π M htriv K K' h x.1 (LinearMap.mem_ker.mp x.2)
    exact ⟨eK, heK⟩

end Chase

end AlgebraicGeometry.OModulePresheaf.CoverIndepH1

theorem _root_.AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π] (M :
      X.Modules)
    (htriv : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (K K' : X.OrderedAffineCover) (h : Subsingleton ((OModulePresheaf.ofModules π M).HSucc K 0)) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc K' 0) :=
  AlgebraicGeometry.OModulePresheaf.CoverIndepH1.main π M htriv K K' h

end
end OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
