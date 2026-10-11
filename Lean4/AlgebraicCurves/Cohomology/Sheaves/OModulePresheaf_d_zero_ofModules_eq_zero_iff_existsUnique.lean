/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules

/-!
# OModule Presheaf d zero of Modules eq zero iff exists Unique
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.GlobalSectionsDescent

universe u

section cechH0
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace CechH0Sol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

theorem map_map {U U' U'' : V.Opens} (f : U' ⟶ U) (g : U'' ⟶ U') (k : U'' ⟶ U) (x : Γ(M, U)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem map_id' {U : V.Opens} (k : U ⟶ U) (x : Γ(M, U)) : M.presheaf.map k.op x = x := by
  have : k = 𝟙 U := Subsingleton.elim _ _
  subst this
  simp

/-- The zero-simplex associated to a member of the ordered cover. -/
def idx0 (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b h => absurd h
    (by rw [Subsingleton.elim (α := Fin 1) a b]; exact lt_irrefl _)⟩

theorem exists_eq_idx0 (s : K.Idx 0) : ∃ i, s = idx0 K i :=
  ⟨s.1 0, Subtype.ext (funext fun j => by rw [Subsingleton.elim (α := Fin 1) j 0]; rfl)⟩

theorem le_inter_idx0 (i : K.ι) : K.U i ≤ K.inter (idx0 K i) := le_iInf fun _ => le_rfl

theorem inter_idx0_le (i : K.ι) : K.inter (idx0 K i) ≤ K.U i := K.inter_le _ 0

/-- The ordered one-simplex determined by two strictly increasing cover indices. -/
def idx1 {i j : K.ι} (h : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.2 fun k => by
    fin_cases k
    simpa using h⟩

theorem face_idx1_zero {i j : K.ι} (h : i < j) : K.face (idx1 K h) 0 = idx0 K j :=
  Subtype.ext (funext fun k => by
    rw [Subsingleton.elim (α := Fin 1) k 0, K.face_val]
    rfl)

theorem face_idx1_one {i j : K.ι} (h : i < j) : K.face (idx1 K h) 1 = idx0 K i :=
  Subtype.ext (funext fun k => by
    rw [Subsingleton.elim (α := Fin 1) k 0, K.face_val]
    rfl)

theorem inf_le_inter_idx1 {i j : K.ι} (h : i < j) : K.U i ⊓ K.U j ≤ K.inter (idx1 K h) :=
  le_iInf fun k => by
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right

theorem map_congr_idx (c : (OModulePresheaf.ofModules π M).cochain K 0) {s s' : K.Idx 0} (h : s =
  s')
    {W : V.Opens} (f : W ⟶ K.inter s) (f' : W ⟶ K.inter s') :
    M.presheaf.map f.op (show Γ(M, K.inter s) from c s) = M.presheaf.map f'.op (show Γ(M, K.inter
      s') from c s') := by
  subst h
  rw [Subsingleton.elim f f']

theorem d_zero_apply (c : (OModulePresheaf.ofModules π M).cochain K 0) (t : K.Idx 1) :
    (OModulePresheaf.ofModules π M).d K 0 c t =
      M.presheaf.map (homOfLE (K.inter_le_inter_face t 0)).op (show Γ(M, K.inter (K.face t 0))
        from c (K.face t 0)) -
      M.presheaf.map (homOfLE (K.inter_le_inter_face t 1)).op (show Γ(M, K.inter (K.face t 1))
        from c (K.face t 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg]
  rfl

/-- The underlying sheaf of abelian groups of the sheaf of modules. -/
noncomputable abbrev abSheaf : TopCat.Sheaf Ab V.carrier := ⟨M.presheaf, M.isSheaf⟩

/-- The local section family obtained from a Čech zero-cochain. -/
noncomputable def sfam (c : (OModulePresheaf.ofModules π M).cochain K 0) (i : K.ι) : Γ(M, K.U i) :=
  M.presheaf.map (homOfLE (le_inter_idx0 K i)).op (show Γ(M, K.inter (idx0 K i)) from c (idx0 K i))

theorem sfam_def (c : (OModulePresheaf.ofModules π M).cochain K 0) (i : K.ι) : sfam π M K c i =
    M.presheaf.map (homOfLE (le_inter_idx0 K i)).op (show Γ(M, K.inter (idx0 K i)) from c (idx0 K
      i)) := rfl

theorem glue (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hcompat : TopCat.Presheaf.IsCompatible M.presheaf K.U (sfam π M K c)) :
    ∃! x : Γ(M, ⊤), ∀ i, M.presheaf.map (homOfLE (le_top : K.U i ≤ ⊤)).op x = sfam π M K c i :=
  TopCat.Sheaf.existsUnique_gluing' (abSheaf M) K.U ⊤ (fun _ => homOfLE le_top) K.iSup_eq_top.ge _
    hcompat

theorem main (c : (OModulePresheaf.ofModules π M).cochain K 0) :
    (OModulePresheaf.ofModules π M).d K 0 c = 0 ↔
      ∃! x : Γ(M, ⊤), ∀ s : K.Idx 0, c s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x
        := by
  classical
  constructor
  · intro hd
    let sf : ∀ i, Γ(M, K.U i) := sfam π M K c
    have sf_def : ∀ i, sf i =
      M.presheaf.map (homOfLE (le_inter_idx0 K i)).op (show Γ(M, K.inter (idx0 K i)) from c (idx0
        K i)) :=
      fun _ => rfl
    have hlt : ∀ {i j : K.ι} (h : i < j),
        M.presheaf.map (homOfLE (inf_le_left : K.U i ⊓ K.U j ≤ K.U i)).op (sf i) =
          M.presheaf.map (homOfLE (inf_le_right : K.U i ⊓ K.U j ≤ K.U j)).op (sf j) := by
      intro i j h
      have h0 := congrFun hd (idx1 K h)
      rw [d_zero_apply] at h0
      change _ - _ = (0 : Γ(M, K.inter (idx1 K h))) at h0
      rw [sub_eq_zero] at h0
      have h1 := congrArg (M.presheaf.map (homOfLE (inf_le_inter_idx1 K h)).op) h0
      have eL : M.presheaf.map (homOfLE (inf_le_left : K.U i ⊓ K.U j ≤ K.U i)).op (sf i) =
          M.presheaf.map (homOfLE (inf_le_inter_idx1 K h)).op
            (M.presheaf.map (homOfLE (K.inter_le_inter_face (idx1 K h) 1)).op
              (show Γ(M, K.inter (K.face (idx1 K h) 1)) from c (K.face (idx1 K h) 1))) := by
        rw [sf_def, map_map M _ _ (homOfLE (inf_le_left.trans (le_inter_idx0 K i))),
          map_congr_idx π M K c (face_idx1_one K h).symm (homOfLE (inf_le_left.trans
            (le_inter_idx0 K i)))
            (homOfLE ((inf_le_inter_idx1 K h).trans (K.inter_le_inter_face (idx1 K h) 1))),
          ← map_map M (homOfLE (K.inter_le_inter_face (idx1 K h) 1)) (homOfLE (inf_le_inter_idx1 K
            h))
            (homOfLE ((inf_le_inter_idx1 K h).trans (K.inter_le_inter_face (idx1 K h) 1)))]
      have eR : M.presheaf.map (homOfLE (inf_le_right : K.U i ⊓ K.U j ≤ K.U j)).op (sf j) =
          M.presheaf.map (homOfLE (inf_le_inter_idx1 K h)).op
            (M.presheaf.map (homOfLE (K.inter_le_inter_face (idx1 K h) 0)).op
              (show Γ(M, K.inter (K.face (idx1 K h) 0)) from c (K.face (idx1 K h) 0))) := by
        rw [sf_def, map_map M _ _ (homOfLE (inf_le_right.trans (le_inter_idx0 K j))),
          map_congr_idx π M K c (face_idx1_zero K h).symm (homOfLE (inf_le_right.trans
            (le_inter_idx0 K j)))
            (homOfLE ((inf_le_inter_idx1 K h).trans (K.inter_le_inter_face (idx1 K h) 0))),
          ← map_map M (homOfLE (K.inter_le_inter_face (idx1 K h) 0)) (homOfLE (inf_le_inter_idx1 K
            h))
            (homOfLE ((inf_le_inter_idx1 K h).trans (K.inter_le_inter_face (idx1 K h) 0)))]
      rw [eL, eR]
      exact h1.symm
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf K.U (sfam π M K c) := by
      intro i j
      change M.presheaf.map (Opens.infLELeft (K.U i) (K.U j)).op (sf i) =
        M.presheaf.map (Opens.infLERight (K.U i) (K.U j)).op (sf j)
      rcases lt_trichotomy i j with h | rfl | h
      · exact hlt h
      · rw [sf_def, map_map M _ _ (homOfLE (inf_le_left.trans (le_inter_idx0 K i))),
          map_map M _ _ (homOfLE (inf_le_left.trans (le_inter_idx0 K i)))]
      · have h' := congrArg (M.presheaf.map (homOfLE (le_of_eq (inf_comm (K.U i) (K.U j)))).op)
          (hlt h)
        simp only at h'
        rw [map_map M _ _ (Opens.infLERight (K.U i) (K.U j)),
          map_map M _ _ (Opens.infLELeft (K.U i) (K.U j))] at h'
        exact h'.symm
    obtain ⟨x, hx, huniq⟩ := glue π M K c hcompat
    refine ⟨x, fun s => ?_, fun y hy => huniq y fun i => ?_⟩
    · obtain ⟨i, rfl⟩ := exists_eq_idx0 K s
      have h2 := congrArg (M.presheaf.map (homOfLE (inter_idx0_le K i)).op) (hx i)
      rw [sfam_def, map_map M _ _ (homOfLE ((inter_idx0_le K i).trans le_top)),
        map_map M _ _ (homOfLE le_rfl), map_id'] at h2
      exact h2.symm
    · rw [sfam_def, hy (idx0 K i), map_map M _ _ (homOfLE le_top)]
  · rintro ⟨x, hx, -⟩
    funext t
    rw [d_zero_apply, hx, hx, map_map M _ _ (homOfLE le_top), map_map M _ _ (homOfLE le_top),
      sub_self]
    rfl

end CechH0Sol

theorem _root_.AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (K : V.OrderedAffineCover) (c : (OModulePresheaf.ofModules π M).cochain K 0) :
    (OModulePresheaf.ofModules π M).d K 0 c = 0 ↔
      ∃! x : Γ(M, ⊤), ∀ s : K.Idx 0, c s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x :=
  CechH0Sol.main π M K c

end cechH0
end AlgebraicCurves.Cohomology.Sheaves.Proofs.GlobalSectionsDescent
end ProofImplementation
