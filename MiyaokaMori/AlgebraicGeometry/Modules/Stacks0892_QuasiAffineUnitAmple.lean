import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus

/-! # The structure sheaf of a quasi-affine scheme is ample

**Stacks 01P9 (`properties-lemma-quasi-affine-O-ample`, direction "⇒"): the structure sheaf of a
quasi-affine scheme is ample.**

References: Stacks 01P9; `AlgebraicGeometry.Scheme.IsQuasiAffine` (quasi-compact and
`X → Spec Γ(X, O)` an immersion, hence an open immersion). Used at the end of the proof of Stacks 0892
(via 0891: "`f` quasi-affine ⟺ `O_X` is `f`-relatively ample").

Proof:
1. The first conjunct of `IsAmple`, `CompactSpace X`: `IsQuasiAffine extends CompactSpace`.
2. The second conjunct: for `x ∈ X`, `Scheme.IsQuasiAffine.isBasis_basicOpen` says that
   `{X.basicOpen r | r ∈ Γ(X, ⊤), X.basicOpen r affine}` is a basis of the topology, so there is
   `r ∈ Γ(X, ⊤)` with `X.basicOpen r` affine and `x ∈ X.basicOpen r`
   (`Opens.IsBasis.exists_subset_of_mem_open` for the open `⊤`).
3. Take `m := 0 + 1` and `s := r^{⊗1} = tensorPowSection r 1 ∈ Γ(O_X^{⊗1}, ⊤)`.
   `nonvanishingLocus_tensorPowSection_succ` gives `X_{r^{⊗1}} = (O_X)_r`
   (no need for `unitTensorPowIso` and `nonvanishingLocus_iso`).
4. **The nonvanishing locus of a section of the structure sheaf is a basic open**
   (`nonvanishingLocus_unit_eq_basicOpen`): `(O_X)_r = X.basicOpen r`. Pointwise:
   `y ∈ X.basicOpen r ⟺ r_y` is a unit (`Scheme.mem_basicOpen_top`); `y ∈ (O_X)_r ⟺ r_y ∉ 𝔪_y • ⊤`.
   `1` is a frame of `O_X = O_X^{⊗0}` on `⊤` (`isFrame_tensorPow_zero_one`), and the coordinate of `r`
   in the frame `1` is `r` (`IsFrame.coord_unique`: `r • 1 = r`), so `r_y ∈ 𝔪_y • ⊤ ⟺ r_y ∈ 𝔪_y`
   (`IsFrame.germ_mem_maximalIdeal_smul_iff_coord`) `⟺ r_y` is not a unit
   (`IsLocalRing.notMem_maximalIdeal`).
5. Hence `x ∈ X_s = X.basicOpen r` and `X_s` is affine.

Edge case: `X` empty — `CompactSpace` holds and `∀ x` is vacuous.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The nonvanishing locus of a section `r ∈ Γ(X, ⊤)` of the structure sheaf, viewed as a global
section of the line bundle `O_X`, is the basic open `X.basicOpen r` (for `L = O_X` the `X_s` of
Stacks 01CY is `D(s)`). A `private` copy of
`AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_unit_eq_basicOpen`, kept to avoid a heavy import. -/
private theorem nonvanishingLocus_unit_eq_basicOpen (X : AlgebraicGeometry.Scheme.{u}) (r : Γ(X, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) r =
      X.basicOpen r := by
  -- `1` is a frame of `O_X = O_X^{⊗0}` on `⊤` (`tensorPow L 0 = O_X` by definition)
  have hf : IsFrame (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⊤ (1 : Γ(X, ⊤)) :=
    isFrame_tensorPow_zero_one (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⊤
  -- the coordinate of `r` in the frame `1` is `r`: `r • 1 = r`
  have hcoord : hf.coord le_rfl
      (AlgebraicGeometry.Scheme.Modules.res (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        le_top r) = r := by
    apply hf.coord_unique
    have h1 : AlgebraicGeometry.Scheme.Modules.res (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        le_rfl (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤)) :=
      res_self (SheafOfModules.unit X.ringCatSheaf : X.Modules) (1 : Γ(X, ⊤))
    have h2 : AlgebraicGeometry.Scheme.Modules.res (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        le_top r = r :=
      res_self (SheafOfModules.unit X.ringCatSheaf : X.Modules) r
    rw [h1, h2]
    change r * (1 : Γ(X, ⊤)) = r
    exact mul_one r
  apply TopologicalSpace.Opens.ext
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe]
  refine (mem_nonvanishingLocus (SheafOfModules.unit X.ringCatSheaf : X.Modules) r y).trans ?_
  refine Iff.trans ?_ (X.mem_basicOpen_top r y).symm
  have key := hf.germ_mem_maximalIdeal_smul_iff_coord (y := y) trivial r
  rw [hcoord] at key
  exact (not_congr key).trans IsLocalRing.notMem_maximalIdeal

end AlgebraicGeometry.Scheme.Modules

/-- **The structure sheaf of a quasi-affine scheme is ample** (Stacks 01P9, "⇒"). -/
theorem AlgebraicGeometry.IsAmple.unit_of_isQuasiAffine (X : AlgebraicGeometry.Scheme.{u})
    [X.IsQuasiAffine] :
    AlgebraicGeometry.IsAmple (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  have hloc := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection_succ
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) r 0
  rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_unit_eq_basicOpen] at hloc
  refine ⟨0 + 1, Nat.succ_pos 0,
    AlgebraicGeometry.Scheme.Modules.tensorPowSection (M := SheafOfModules.unit X.ringCatSheaf) r (0 + 1),
    ?_, ?_⟩
  · rw [hloc]; exact hxr
  · rw [hloc]; exact hr

end
