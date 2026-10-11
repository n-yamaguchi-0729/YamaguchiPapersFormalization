/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FieldFiniteCover
import Nyll.EtaleCohomology.Classical.NatInjectiveResolution
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Finite étale local primitives for field cohomology

A closed global section of an exact complex of abelian sheaves over a field
becomes an actual boundary after a connected finite étale cover. Applying
this to an injective resolution supplies finite-cover local primitives
in every positive degree. These are the actual resolutions computing
classical sheaf cohomology, not an assumed field/Galois comparison.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Exactness of abelian sheaves over a field supplies a finite étale
local primitive for every closed global section. -/
theorem exists_finiteEtale_primitive_of_exact_of_field
    (K : Type u) [Field K]
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.Exact)
    (t : S.X₂.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))))
    (ht : S.g.hom.app _ t = 0) :
    ∃ (V : (Spec (.of K)).Etale)
      (f : V ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFinite V.hom ∧ ConnectedSpace V.left ∧ Function.Surjective V.hom ∧
        ∃ s : S.X₁.obj.obj (op V), S.f.hom.app (op V) s = S.X₂.obj.map f.op t := by
  let Γ : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
    sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))
  let e : Γ.obj (kernel S.g) ≅ AddCommGrpCat.of (Γ.map S.g).hom.ker :=
    IsLimit.conePointUniqueUpToIso
      (isLimitOfHasKernelOfPreservesLimit Γ S.g)
      (AddCommGrpCat.kernelIsLimit (Γ.map S.g))
  let z : Γ.obj (kernel S.g) := e.inv ⟨t, ht⟩
  have hz : (Γ.map (kernel.ι S.g)) z = t := by
    have he : e.inv ≫ Γ.map (kernel.ι S.g) =
        AddCommGrpCat.ofHom (Γ.map S.g).hom.ker.subtype :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (isLimitOfHasKernelOfPreservesLimit Γ S.g)
        (AddCommGrpCat.kernelIsLimit (Γ.map S.g)) WalkingParallelPair.zero
    exact ConcreteCategory.congr_hom he ⟨t, ht⟩
  let q : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  have : Epi q := S.exact_iff_epi_kernel_lift.mp hS
  obtain ⟨V, f, hf, hc, hs, s, h⟩ :=
    exists_finiteEtale_lift_sheaf_epi_section_of_field K q z
  refine ⟨V, f, hf, hc, hs, s, ?_⟩
  have hq : q ≫ kernel.ι S.g = S.f := kernel.lift_ι _ _ _
  have hq' := ConcreteCategory.congr_hom
    (congrArg (fun α => α.hom.app (op V)) hq) s
  change (kernel.ι S.g).hom.app (op V) (q.hom.app (op V) s) =
    S.f.hom.app (op V) s at hq'
  rw [← hq', h]
  have hn := ConcreteCategory.congr_hom ((kernel.ι S.g).hom.naturality f.op) z
  change (kernel.ι S.g).hom.app (op V) ((kernel S.g).obj.map f.op z) =
    S.X₂.obj.map f.op ((Γ.map (kernel.ι S.g)) z) at hn
  rw [hn, hz]

/-- Every positive-degree closed section of an actual injective resolution
over a field acquires an actual primitive on a connected finite étale cover. -/
theorem exists_finiteEtale_resolution_primitive_of_field
    (K : Type u) [Field K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (n : ℕ)
    (t : (I.cocomplex.X (n + 1)).obj.obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))))
    (ht : (I.cocomplex.d (n + 1) (n + 2)).hom.app _ t = 0) :
    ∃ (V : (Spec (.of K)).Etale)
      (f : V ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFinite V.hom ∧ ConnectedSpace V.left ∧ Function.Surjective V.hom ∧
        ∃ s : (I.cocomplex.X n).obj.obj (op V),
          (I.cocomplex.d n (n + 1)).hom.app (op V) s =
            (I.cocomplex.X (n + 1)).obj.map f.op t :=
  exists_finiteEtale_primitive_of_exact_of_field K
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2)))
    (I.exact_succ n) t ht

end EtaleCohomology
