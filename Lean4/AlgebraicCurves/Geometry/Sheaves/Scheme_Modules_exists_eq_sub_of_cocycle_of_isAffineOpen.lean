/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_eq_sub_of_cocycle_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.OpenImmersionUnit
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial

/-!
# Solving a cocycle on an affine open

Quasicoherent Cech exactness produces local sections whose differences give the cocycle.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_eq_sub_of_cocycle_of_isAffineOpen
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace RelH1
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h'
  exact h'.symm

theorem comp_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (φ ≫ ψ).app U m = ψ.app U (φ.app U m) := rfl

theorem zero_app_apply {M N : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (0 : M ⟶ N).app U m = 0 :=
  rfl

section OpenImm

variable {X' : Scheme.{u}} (p : X' ⟶ X) [IsOpenImmersion p] (M : X.Modules)

/-- The adjunction unit for pullback along the open immersion. -/
abbrev η : M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M

/-- Pull a section along the open immersion. -/
abbrev pull (V : X.Opens) (m : Γ(M, V)) : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ V) := (η p
  M).app V m

omit [IsOpenImmersion p] in
theorem pull_add (V : X.Opens) (m m' : Γ(M, V)) : pull p M V (m + m') = pull p M V m + pull p M V
  m' := map_add _ _ _
omit [IsOpenImmersion p] in
theorem pull_sub (V : X.Opens) (m m' : Γ(M, V)) : pull p M V (m - m') = pull p M V m - pull p M V
  m' := map_sub _ _ _
omit [IsOpenImmersion p] in
theorem pull_zero (V : X.Opens) : pull p M V 0 = 0 := map_zero _

omit [IsOpenImmersion p] in
theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(M, V)) :
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone h)).op
      (pull p M V m)
      = pull p M U (M.presheaf.map (homOfLE h).op m) := by
  rw [pull, pull, ← app_naturality (η p M) (homOfLE h) m]
  rfl

theorem pull_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (pull p M V) :=
  Scheme.Modules.bijective_unit_app_of_le_opensRange p M V hV

end OpenImm

section PFam

variable {ι : Type u} [LinearOrder ι] (P : ι → X.Opens)

/-- The intersection of two opens in the family. -/
abbrev P2 (i j : ι) : X.Opens := P i ⊓ P j
/-- The intersection of three opens in the family. -/
abbrev P3 (i j k : ι) : X.Opens := P i ⊓ P j ⊓ P k

omit [LinearOrder ι] in
theorem P3_le_left (i j k : ι) : P3 P i j k ≤ P i := inf_le_left.trans inf_le_left
omit [LinearOrder ι] in
theorem P3_le_mid (i j k : ι) : P3 P i j k ≤ P j := inf_le_left.trans inf_le_right
omit [LinearOrder ι] in
theorem P3_le_right (i j k : ι) : P3 P i j k ≤ P k := inf_le_right

end PFam

section Transport

variable (N : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) {ι : Type u} [Fintype ι] [LinearOrder
  ι] (P : ι → X.Opens)
  (hPU : ∀ i, P i ≤ U) (haff : ∀ i, IsAffineOpen (P i)) (hcov : U ≤ ⨆ i, P i)

/-- The ordered affine cover obtained by restricting the family to the affine open. -/
def cover : (U : Scheme.{u}).OrderedAffineCover where
  ι := ι
  U i := U.ι ⁻¹ᵁ P i
  isAffineOpen i := by
    have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ P i) = P i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr
        (hPU i)]
    have := haff i
    rw [← himg] at this
    exact (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).mp this
  iSup_eq_top := by
    apply top_unique
    intro y _
    have hy : U.ι.base y ∈ U := y.2
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hy)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem cover_U (i : ι) : (cover U P hPU haff hcov).U i = U.ι ⁻¹ᵁ P i := rfl

/-- The module presheaf of the restricted scheme module. -/
abbrev F : OModulePresheaf (U : Scheme.{u}).toSpecΓ :=
  OModulePresheaf.ofModules (U : Scheme.{u}).toSpecΓ ((Scheme.Modules.pullback U.ι).obj N)

omit hU hPU haff hcov in
theorem isQuasicoherent_F
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj N ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
        :
    (F N U).IsQuasicoherent :=
  OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _
    (Scheme.Modules.IsInvertible.pullback U.ι (L := N) ⟨htriv⟩).exists_trivialization

variable (u : ∀ i j, Γ(N, P2 P i j))

theorem inter_le_pre (σ : (cover U P hPU haff hcov).Idx 1) :
    (cover U P hPU haff hcov).inter σ ≤ U.ι ⁻¹ᵁ P2 P (σ.1 0) (σ.1 1) := fun _y hy =>
  ⟨(cover U P hPU haff hcov).inter_le σ 0 hy, (cover U P hPU haff hcov).inter_le σ 1 hy⟩

/-- The Cech cochain induced by the given cocycle. -/
def u' : (F N U).cochain (cover U P hPU haff hcov) 1 := fun σ =>
  ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE (inter_le_pre U P hPU haff hcov σ)).op
    (pull U.ι N (P2 P (σ.1 0) (σ.1 1)) (u (σ.1 0) (σ.1 1)))

theorem F_res_apply {O O' : (U : Scheme.{u}).Opens} (h : O ≤ O') (x : (F N U).obj O') :
    (F N U).res h x = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE h).op x :=
  OModulePresheaf.ofModules_res_apply _ _ h x


theorem res_u'_eq (τ : (cover U P hPU haff hcov).Idx 2) (j : Fin 3) (a b : ι)
    (e0 : (((cover U P hPU haff hcov).face τ j).1 0) = a) (e1 : (((cover U P hPU haff hcov).face τ
      j).1 1) = b)
    (h3 : (cover U P hPU haff hcov).inter τ ≤ U.ι ⁻¹ᵁ P3 P (τ.1 0) (τ.1 1) (τ.1 2))
    (hab3 : P3 P (τ.1 0) (τ.1 1) (τ.1 2) ≤ P2 P a b) :
    (F N U).res ((cover U P hPU haff hcov).inter_le_inter_face τ j) (u' N U P hPU haff hcov u
      ((cover U P hPU haff hcov).face τ j))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE h3).op
          (pull U.ι N (P3 P (τ.1 0) (τ.1 1) (τ.1 2)) (N.presheaf.map (homOfLE hab3).op (u a b))) :=
            by
  subst e0; subst e1
  rw [F_res_apply, u', ← map_pull]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  congr 1

theorem face_val (τ : (cover U P hPU haff hcov).Idx 2) (j : Fin 3) (k : Fin 2) :
    ((cover U P hPU haff hcov).face τ j).1 k = τ.1 (j.succAbove k) := rfl

theorem d_u' (hcoc : ∀ i j k : ι, i < j → j < k →
      N.presheaf.map (homOfLE (le_inf (P3_le_mid P i j k) (P3_le_right P i j k))).op (u j k)
        - N.presheaf.map (homOfLE (le_inf (P3_le_left P i j k) (P3_le_right P i j k))).op (u i k)
        + N.presheaf.map (homOfLE (le_inf (P3_le_left P i j k) (P3_le_mid P i j k))).op (u i j) =
          0) :
    (F N U).d (cover U P hPU haff hcov) 1 (u' N U P hPU haff hcov u) =
      (fun τ => (0 : Γ((Scheme.Modules.pullback U.ι).obj N,
        (cover U P hPU haff hcov).inter τ))) := by
  funext τ
  let : AddCommGroup ((F N U).obj ((cover U P hPU haff hcov).inter τ)) :=
    (F N U).addCommGroup _
  have h3 : (cover U P hPU haff hcov).inter τ ≤ U.ι ⁻¹ᵁ P3 P (τ.1 0) (τ.1 1) (τ.1 2) := fun y hy =>
    ⟨⟨(cover U P hPU haff hcov).inter_le τ 0 hy, (cover U P hPU haff hcov).inter_le τ 1 hy⟩, (cover
      U P hPU haff hcov).inter_le τ 2 hy⟩
  refine (OModulePresheaf.d_apply (F N U) (cover U P hPU haff hcov) 1
    (u' N U P hPU haff hcov u) τ).trans ?_
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_smul, ← sub_eq_add_neg]
  rw [res_u'_eq N U P hPU haff hcov u τ 0 (τ.1 1) (τ.1 2) rfl rfl h3
      (le_inf (P3_le_mid P _ _ _) (P3_le_right P _ _ _)),
    res_u'_eq N U P hPU haff hcov u τ 1 (τ.1 0) (τ.1 2) rfl rfl h3
      (le_inf (P3_le_left P _ _ _) (P3_le_right P _ _ _)),
    res_u'_eq N U P hPU haff hcov u τ 2 (τ.1 0) (τ.1 1) rfl rfl h3
      (le_inf (P3_le_left P _ _ _) (P3_le_mid P _ _ _))]
  have key2 := congrArg (pull U.ι N (P3 P (τ.1 0) (τ.1 1) (τ.1 2)))
    (hcoc (τ.1 0) (τ.1 1) (τ.1 2)
      (τ.2 (show (0 : Fin 3) < 1 by decide)) (τ.2 (show (1 : Fin 3) < 2 by decide)))
  rw [pull_add, pull_sub, pull_zero] at key2
  have key3 := congrArg (((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE h3).op) key2
  rw [map_add, map_sub, map_zero] at key3
  exact key3

/-- The degree-zero cover index associated to one open. -/
def idx0 (i : ι) : (cover U P hPU haff hcov).Idx 0 :=
  ⟨fun _ => i, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩

theorem pre_le_inter_idx0 (i : ι) : U.ι ⁻¹ᵁ P i ≤ (cover U P hPU haff hcov).inter (idx0 U P hPU
  haff hcov i) :=
  le_iInf fun _ => le_rfl

/-- The degree-one cover index associated to an ordered pair. -/
def idx1 {a b : ι} (hab : a < b) : (cover U P hPU haff hcov).Idx 1 :=
  ⟨![a, b], by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · change a < b
      exact hab
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem face_idx1_zero {a b : ι} (hab : a < b) :
    (cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 0 = idx0 U P hPU haff hcov b := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem face_idx1_one {a b : ι} (hab : a < b) :
    (cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 1 = idx0 U P hPU haff hcov a := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem inter_idx1 {a b : ι} (hab : a < b) :
    (cover U P hPU haff hcov).inter (idx1 U P hPU haff hcov hab) = U.ι ⁻¹ᵁ P2 P a b := by
  refine le_antisymm (inter_le_pre U P hPU haff hcov _) (le_iInf fun k => ?_)
  fin_cases k
  · exact fun y hy => hy.1
  · exact fun y hy => hy.2

theorem res_at_eq (c : (F N U).cochain (cover U P hPU haff hcov) 0) {σ τ : (cover U P hPU haff
  hcov).Idx 0} (e : σ = τ)
    {O : (U : Scheme.{u}).Opens} (hσ : O ≤ (cover U P hPU haff hcov).inter σ) (hτ : O ≤ (cover U P
      hPU haff hcov).inter τ) :
    (F N U).res hσ (c σ) = (F N U).res hτ (c τ) := by
  subst e; rfl

theorem map_injective_of_eq (N : (U : Scheme.{u}).Modules) {W W' : (U : Scheme.{u}).Opens} (h : W =
  W') (hle : W ≤ W') :
    Function.Injective (N.presheaf.map (homOfLE hle).op) := by
  subst h
  intro a b hab
  have : (homOfLE hle) = 𝟙 W := rfl
  rw [this, op_id, N.presheaf.map_id] at hab
  exact hab

theorem exists_v (v' : (F N U).cochain (cover U P hPU haff hcov) 0)
    (hv' : (F N U).d (cover U P hPU haff hcov) 0 v' = u' N U P hPU haff hcov u) :
    ∃ v : ∀ i, Γ(N, P i), ∀ a b : ι, a < b →
      u a b = N.presheaf.map (homOfLE inf_le_right).op (v b) - N.presheaf.map (homOfLE
        inf_le_left).op (v a) := by
  have hDr : ∀ i, P i ≤ U.ι.opensRange := fun i => by
    rw [Scheme.Opens.opensRange_ι]; exact hPU i
  let w : ∀ i, Γ((Scheme.Modules.pullback U.ι).obj N, U.ι ⁻¹ᵁ P i) := fun i =>
    (F N U).res (pre_le_inter_idx0 U P hPU haff hcov i) (v' (idx0 U P hPU haff hcov i))
  choose v hv using fun i => (pull_bijective U.ι N (P i) (hDr i)).2 (w i)
  refine ⟨v, fun a b hab => ?_⟩
  let : AddCommGroup ((F N U).obj
      ((cover U P hPU haff hcov).inter (idx1 U P hPU haff hcov hab))) :=
    (F N U).addCommGroup _
  have hcomp := (OModulePresheaf.d_apply (F N U) (cover U P hPU haff hcov) 0 v'
    (idx1 U P hPU haff hcov hab)).symm.trans
      (congrFun hv' (idx1 U P hPU haff hcov hab))
  rw [Fin.sum_univ_two] at hcomp
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul] at hcomp
  have hle2 : (cover U P hPU haff hcov).inter (idx1 U P hPU haff hcov hab) ≤ U.ι ⁻¹ᵁ P2 P a b :=
    (inter_idx1 U P hPU haff hcov hab).le
  have hb' : (F N U).res ((cover U P hPU haff hcov).inter_le_inter_face (idx1 U P hPU haff hcov
    hab) 0)
        (v' ((cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 0))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (N.presheaf.map (homOfLE inf_le_right).op (v b))) := by
    rw [res_at_eq N U P hPU haff hcov v' (face_idx1_zero U P hPU haff hcov hab) _
      (hle2.trans (((Opens.map U.ι.base).monotone inf_le_right).trans (pre_le_inter_idx0 U P hPU
        haff hcov b))),
      ← (F N U).res_res ((hle2.trans ((Opens.map U.ι.base).monotone inf_le_right)))
        (pre_le_inter_idx0 U P hPU haff hcov b)]
    change (F N U).res _ (w b) = _
    rw [← hv b]
    erw [F_res_apply, ← map_pull]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    congr 1
  have ha' : (F N U).res ((cover U P hPU haff hcov).inter_le_inter_face (idx1 U P hPU haff hcov
    hab) 1)
        (v' ((cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 1))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (N.presheaf.map (homOfLE inf_le_left).op (v a))) := by
    rw [res_at_eq N U P hPU haff hcov v' (face_idx1_one U P hPU haff hcov hab) _
      (hle2.trans (((Opens.map U.ι.base).monotone inf_le_left).trans (pre_le_inter_idx0 U P hPU
        haff hcov a))),
      ← (F N U).res_res ((hle2.trans ((Opens.map U.ι.base).monotone inf_le_left)))
        (pre_le_inter_idx0 U P hPU haff hcov a)]
    change (F N U).res _ (w a) = _
    rw [← hv a]
    erw [F_res_apply, ← map_pull]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    congr 1
  rw [hb', ha'] at hcomp
  have hu' : u' N U P hPU haff hcov u (idx1 U P hPU haff hcov hab)
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (u a b)) := rfl
  erw [hu', ← sub_eq_add_neg] at hcomp
  have hcomp' : ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
        (pull U.ι N (P2 P a b)
          (N.presheaf.map (homOfLE inf_le_right).op (v b) - N.presheaf.map (homOfLE inf_le_left).op
            (v a)))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (u a b)) := by
    rw [pull_sub, map_sub]
    exact hcomp
  have hinj1 := map_injective_of_eq U ((Scheme.Modules.pullback U.ι).obj N) (inter_idx1 U P hPU
    haff hcov hab) hle2
  have hinj2 := (pull_bijective U.ι N (P2 P a b) ((inf_le_left).trans (hDr a))).1
  exact (hinj2 (hinj1 hcomp')).symm

end Transport

theorem main
    {X : Scheme.{u}} (N : X.Modules)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj N ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) {ι : Type u} [Finite ι] [LinearOrder ι] (P : ι → X.Opens)
    (hPU : ∀ i, P i ≤ U) (haff : ∀ i, IsAffineOpen (P i)) (hcov : U ≤ ⨆ i, P i)
    (u : ∀ i j : ι, Γ(N, P i ⊓ P j))
    (hcoc : ∀ i j k : ι, i < j → j < k →
      N.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          P i ⊓ P j ⊓ P k ≤ P j ⊓ P k)).op (u j k)
        - N.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          P i ⊓ P j ⊓ P k ≤ P i ⊓ P k)).op (u i k)
        + N.presheaf.map (homOfLE (inf_le_left : P i ⊓ P j ⊓ P k ≤ P i ⊓ P j)).op (u i j) = 0) :
    ∃ v : ∀ i : ι, Γ(N, P i), ∀ i j : ι, i < j →
      u i j = N.presheaf.map (homOfLE (inf_le_right : P i ⊓ P j ≤ P j)).op (v j)
        - N.presheaf.map (homOfLE (inf_le_left : P i ⊓ P j ≤ P i)).op (v i) := by
  let : Fintype ι := Fintype.ofFinite ι
  have : IsAffine (U : Scheme.{u}) := hU
  let π : (U : Scheme.{u}) ⟶ Spec (.of Γ((U : Scheme.{u}), ⊤)) :=
    (U : Scheme.{u}).toSpecΓ
  have : IsIso π := IsAffine.affine
  have : IsSeparated π := IsSeparated.isSeparated_of_mono π
  let : ∀ W : (U : Scheme.{u}).Opens, AddCommGroup ((F N U).obj W) :=
    (F N U).addCommGroup
  let : ∀ W : (U : Scheme.{u}).Opens, Module Γ((U : Scheme.{u}), ⊤) ((F N U).obj W) :=
    (F N U).module
  have hF := isQuasicoherent_F N U htriv
  have hd := d_u' N U P hPU haff hcov u hcoc
  obtain ⟨v', hv'⟩ := OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent
    (R := Γ((U : Scheme.{u}), ⊤)) (V := (U : Scheme.{u}))
    (π := π) (F N U) hF
    (cover U P hPU haff hcov) 0 (show _ from hd)
  exact exists_v N U P hPU haff hcov u v' hv'

end AlgebraicGeometry.Scheme.Modules.RelH1

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_eq_sub_of_cocycle_of_isAffineOpen
    {X : Scheme.{u}} (N : X.Modules)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj N ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) {ι : Type u} [Finite ι] [LinearOrder ι] (P : ι → X.Opens)
    (hPU : ∀ i, P i ≤ U) (haff : ∀ i, IsAffineOpen (P i)) (hcov : U ≤ ⨆ i, P i)
    (u : ∀ i j : ι, Γ(N, P i ⊓ P j))
    (hcoc : ∀ i j k : ι, i < j → j < k →
      N.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          P i ⊓ P j ⊓ P k ≤ P j ⊓ P k)).op (u j k)
        - N.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          P i ⊓ P j ⊓ P k ≤ P i ⊓ P k)).op (u i k)
        + N.presheaf.map (homOfLE (inf_le_left : P i ⊓ P j ⊓ P k ≤ P i ⊓ P j)).op (u i j) = 0) :
    ∃ v : ∀ i : ι, Γ(N, P i), ∀ i j : ι, i < j →
      u i j = N.presheaf.map (homOfLE (inf_le_right : P i ⊓ P j ≤ P j)).op (v j)
        - N.presheaf.map (homOfLE (inf_le_left : P i ⊓ P j ≤ P i)).op (v i) :=
  AlgebraicGeometry.Scheme.Modules.RelH1.main N htriv U hU P hPU haff hcov u hcoc

end
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_eq_sub_of_cocycle_of_isAffineOpen
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
