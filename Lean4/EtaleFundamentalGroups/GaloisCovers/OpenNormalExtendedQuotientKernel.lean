/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.ExtendedQuotientKernel
import ProCGroups.FiniteStepSolvableQuotients.ProsolvableCriterion

/-!
# Finite-abelian kernel tests on open-normal local models

Finite discrete abelian kernel tests are invariant under isomorphisms of the
source and target groups.  Consequently, actual finite-etale extensions on a
family of geometric local models provide the kernel condition over every open
normal subgroup.
-/

noncomputable section

namespace ProCGroups.ProC

universe u

/-- The condition that all finite discrete abelian maps kill a kernel can be
transported across a commutative square whose horizontal maps are topological
group isomorphisms. -/
theorem finiteDiscreteAbelianMapsKillKernel_of_continuousMulEquiv
    {G Q G' Q' : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [TopologicalSpace G'] [Group G'] [IsTopologicalGroup G']
    [TopologicalSpace Q'] [Group Q'] [IsTopologicalGroup Q']
    (f : G →ₜ* Q) (f' : G' →ₜ* Q')
    (eG : G' ≃ₜ* G) (eQ : Q' ≃ₜ* Q)
    (hcomm : ∀ x, eQ (f' x) = f (eG x))
    (hkill : FiniteDiscreteAbelianMapsKillKernel f') :
    FiniteDiscreteAbelianMapsKillKernel f := by
  intro A _hAfinite _hAtopology _hAcomm _hAdiscrete phi x hx
  let phi' : G' →ₜ* A :=
    phi.comp (ContinuousMonoidHom.toContinuousMonoidHom eG)
  have hx' : eG.symm x ∈ f'.ker := by
    apply MonoidHom.mem_ker.mpr
    apply eQ.injective
    change eQ (f' (eG.symm x)) = eQ 1
    calc
      eQ (f' (eG.symm x)) = f (eG (eG.symm x)) := hcomm _
      _ = f x := congrArg f (eG.apply_symm_apply x)
      _ = 1 := MonoidHom.mem_ker.mp hx
      _ = eQ 1 := (map_one eQ).symm
  have hphi' : eG.symm x ∈ phi'.ker := hkill A phi' hx'
  apply MonoidHom.mem_ker.mpr
  change phi x = 1
  have hphiEq := MonoidHom.mem_ker.mp hphi'
  change phi (eG (eG.symm x)) = 1 at hphiEq
  simpa only [eG.apply_symm_apply] using hphiEq

end ProCGroups.ProC

namespace AlgebraicGeometry.FiniteEtale

universe u

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open ProCGroups.FiniteStepSolvableQuotients

variable {X Y : Scheme.{u}}
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- Suppose every open-normal restriction of a fundamental-group map is
realized by a geometric local model, compatibly with topological group
isomorphisms.  If every abelian Galois quotient cover on each source model has
an actual finite-etale extension on its target model, then all open-normal
finite discrete abelian maps kill the corresponding restricted kernel. -/
theorem fundamentalGroupHom_openNormalFiniteDiscreteAbelianMapsKillKernel_of_local_extensions
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (X' Y' : OpenNormalSubgroup (π₁ᵉᵗ(xi ≫ f)) → Scheme.{u})
    [∀ H, ConnectedSpace (X' H)] [∀ H, ConnectedSpace (Y' H)]
    (g : ∀ H, X' H ⟶ Y' H)
    (xi' : ∀ H, Spec (.of Omega) ⟶ X' H)
    (eSource : ∀ H,
      π₁ᵉᵗ(xi' H) ≃ₜ*
        ProCGroups.OpenNormalSubgroup.comap
          (fundamentalGroupHom f xi).toMonoidHom
          (fundamentalGroupHom f xi).continuous_toFun H)
    (eTarget : ∀ H, π₁ᵉᵗ(xi' H ≫ g H) ≃ₜ* H)
    (hcomm : ∀ H a,
      eTarget H (fundamentalGroupHom (g H) (xi' H) a) =
        ProCGroups.ContinuousMonoidHom.restrictPreimage
          (fundamentalGroupHom f xi) (H : Subgroup π₁ᵉᵗ(xi ≫ f))
          (eSource H a))
    (extend : ∀ H (W : FiniteEtale (X' H)) (_hW : IsGalois W),
      IsMulCommutative (Aut W) →
        Σ Z : FiniteEtale (Y' H), (pullback (g H)).obj Z ≅ W) :
    OpenNormalFiniteDiscreteAbelianMapsKillKernel
      (fundamentalGroupHom f xi) := by
  intro H
  let fH := ProCGroups.ContinuousMonoidHom.restrictPreimage
    (fundamentalGroupHom f xi) (H : Subgroup π₁ᵉᵗ(xi ≫ f))
  let gH := fundamentalGroupHom (g H) (xi' H)
  have hkill : ProCGroups.ProC.FiniteDiscreteAbelianMapsKillKernel gH :=
    fundamentalGroupHom_finiteDiscreteAbelianMapsKillKernel_of_galoisCover_extensions
      (g H) (xi' H) (extend H)
  exact ProCGroups.ProC.finiteDiscreteAbelianMapsKillKernel_of_continuousMulEquiv
    fH gH (eSource H) (eTarget H) (hcomm H) hkill

end AlgebraicGeometry.FiniteEtale

end
