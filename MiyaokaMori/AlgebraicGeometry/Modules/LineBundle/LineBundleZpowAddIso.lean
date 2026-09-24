import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.LineBundleDualEvalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # Additive isomorphisms of integer powers of a line bundle

The additive isomorphism data `L^{p+q} ≅ L^p ⊗ L^q` for integer powers of a line bundle (for equal signs a
rearrangement by associators and unitors, for opposite signs pairwise cancellation through the contraction
`L ⊗ L^∨ ≅ O_X`), together with `L^1 ≅ L` and `L^{-1} ≅ L^∨`.

References: Stacks 01CT/01CU.

The two inverse laws of the contraction `L ⊗ L^∨ ≅ O_X` (`LineBundle.contraction_hom_inv_id` /
`contraction_inv_hom_id`) are proved as follows: `contractionInv = coevHom L ≫ β` and
`contractionHom = β ≫ dualEv L`; the braidings cancel, and `coevHom L ≫ dualEv L = 𝟙` is the rank-one
computation `ev(ε^∨ ⊗ ε) = coord_ε(ε) = 1` on frame opens (section "The contraction is an isomorphism"
below); `hom_inv_id` then follows from `isIso_internalHomEval_dual` (Stacks 01CT/0B8K).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The monoidal left-recursive tensor power: `M^{⊗0} = 𝟙_`, `M^{⊗(n+1)} = M ⊗ M^{⊗n}` (the same recursion
   direction as `moduleTensorPower`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.mpow {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => M ⊗ AlgebraicGeometry.Scheme.Modules.mpow M n

/- The tensor power `moduleTensorPower` (iterated `Modules.tensor`) and the monoidal version are identified
   levelwise through `tensorIsoTensorObj`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) : (n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.moduleTensorPower M n ≅ AlgebraicGeometry.Scheme.Modules.mpow M n)
  | 0 => CategoryTheory.Iso.refl _
  | n + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M (AlgebraicGeometry.Scheme.Modules.moduleTensorPower M n) ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso M
        (AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow M n)

/- Addition of equal signs: `M^{⊗(m+n)} ≅ M^{⊗m} ⊗ M^{⊗n}`, by recursion on `m` (left unitor, associator). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.mpowAdd {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) : (m n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.mpow M (m + n) ≅
      AlgebraicGeometry.Scheme.Modules.mpow M m ⊗ AlgebraicGeometry.Scheme.Modules.mpow M n)
  | 0, n =>
    CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mpow M) (Nat.zero_add n)) ≪≫
      (λ_ (AlgebraicGeometry.Scheme.Modules.mpow M n)).symm
  | m + 1, n =>
    CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mpow M) (Nat.succ_add m n)) ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso M (AlgebraicGeometry.Scheme.Modules.mpowAdd M m n) ≪≫
      (α_ M (AlgebraicGeometry.Scheme.Modules.mpow M m) (AlgebraicGeometry.Scheme.Modules.mpow M n)).symm

/- Integer powers (monoidal version): powers of `M` for nonnegative exponents, powers of `D` for negative ones
   (`D` will be `M^∨`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.mzpow {X : AlgebraicGeometry.Scheme.{u}}
    (M D : X.Modules) : ℤ → X.Modules
  | (n : ℕ) => AlgebraicGeometry.Scheme.Modules.mpow M n
  | Int.negSucc n => AlgebraicGeometry.Scheme.Modules.mpow D (n + 1)

/- Cancelling one factor on each side: `(M ⊗ P) ⊗ (D ⊗ Q) ≅ (M ⊗ D) ⊗ (P ⊗ Q) ≅ 𝟙 ⊗ (P ⊗ Q) ≅ P ⊗ Q`
   (associators, braiding and the contraction `c : M ⊗ D ≅ 𝟙`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.cancelPair {X : AlgebraicGeometry.Scheme.{u}}
    {M D : X.Modules} (c : M ⊗ D ≅ 𝟙_ X.Modules) (P Q : X.Modules) :
    (M ⊗ P) ⊗ (D ⊗ Q) ≅ P ⊗ Q :=
  α_ M P (D ⊗ Q) ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso M
      ((α_ P D Q).symm ≪≫ CategoryTheory.MonoidalCategory.whiskerRightIso (β_ P D) Q ≪≫ α_ D P Q) ≪≫
    (α_ M D (P ⊗ Q)).symm ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso c (P ⊗ Q) ≪≫ λ_ (P ⊗ Q)

/- Addition of opposite signs: `M^{⊗m} ⊗ D^{⊗n} ≅` the integer power `(m − n)`, decreasing both exponents
   simultaneously and cancelling pairwise. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.mpowCancel {X : AlgebraicGeometry.Scheme.{u}}
    {M D : X.Modules} (c : M ⊗ D ≅ 𝟙_ X.Modules) : (m n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.mpow M m ⊗ AlgebraicGeometry.Scheme.Modules.mpow D n ≅
      AlgebraicGeometry.Scheme.Modules.mzpow M D ((m : ℤ) - (n : ℤ)))
  | 0, 0 =>
    λ_ (𝟙_ X.Modules) ≪≫
      CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) by simp))
  | 0, n + 1 =>
    λ_ (AlgebraicGeometry.Scheme.Modules.mpow D (n + 1)) ≪≫
      CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show Int.negSucc n = ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) by rw [Int.negSucc_eq]; push_cast; ring))
  | m + 1, 0 =>
    ρ_ (AlgebraicGeometry.Scheme.Modules.mpow M (m + 1)) ≪≫
      CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show ((m + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) by simp))
  | m + 1, n + 1 =>
    AlgebraicGeometry.Scheme.Modules.cancelPair c
        (AlgebraicGeometry.Scheme.Modules.mpow M m) (AlgebraicGeometry.Scheme.Modules.mpow D n) ≪≫
      AlgebraicGeometry.Scheme.Modules.mpowCancel c m n ≪≫
      CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show (m : ℤ) - (n : ℤ) = ((m + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) by push_cast; ring))

/- The additive isomorphism of integer powers (monoidal version): four cases according to the signs of `p`, `q`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.mzpowAdd {X : AlgebraicGeometry.Scheme.{u}}
    {M D : X.Modules} (c : M ⊗ D ≅ 𝟙_ X.Modules) : (p q : ℤ) →
    (AlgebraicGeometry.Scheme.Modules.mzpow M D (p + q) ≅
      AlgebraicGeometry.Scheme.Modules.mzpow M D p ⊗ AlgebraicGeometry.Scheme.Modules.mzpow M D q)
  | (m : ℕ), (n : ℕ) =>
    CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) by push_cast; ring)) ≪≫
      AlgebraicGeometry.Scheme.Modules.mpowAdd M m n
  | (m : ℕ), Int.negSucc n =>
    CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show (m : ℤ) + Int.negSucc n = (m : ℤ) - ((n + 1 : ℕ) : ℤ) by
          rw [Int.negSucc_eq]; push_cast; ring)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.mpowCancel c m (n + 1)).symm
  | Int.negSucc m, (n : ℕ) =>
    CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show Int.negSucc m + (n : ℤ) = (n : ℤ) - ((m + 1 : ℕ) : ℤ) by
          rw [Int.negSucc_eq]; push_cast; ring)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.mpowCancel c n (m + 1)).symm ≪≫
      β_ (AlgebraicGeometry.Scheme.Modules.mpow M n) (AlgebraicGeometry.Scheme.Modules.mpow D (m + 1))
  | Int.negSucc m, Int.negSucc n =>
    CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mzpow M D)
        (show Int.negSucc m + Int.negSucc n = Int.negSucc (m + 1 + n) by
          rw [Int.negSucc_eq, Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring)) ≪≫
      CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.mpow D)
        (show m + 1 + n + 1 = (m + 1) + (n + 1) by omega)) ≪≫
      AlgebraicGeometry.Scheme.Modules.mpowAdd D (m + 1) (n + 1)

/-- The forward direction of the contraction: braiding followed by evaluation. -/

noncomputable def LineBundle.contractionHom {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    L.toModules ⊗ AlgebraicGeometry.Scheme.Modules.dual L.toModules ⟶ 𝟙_ X.toScheme.Modules :=
  (β_ L.toModules (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).hom ≫
    AlgebraicGeometry.Scheme.Modules.internalHomEval L.toModules (SheafOfModules.unit X.toScheme.ringCatSheaf)

/-- The inverse direction of the contraction: the morphism `O_X → L^∨ ⊗ L` corresponding to the
coevaluation section, followed by the braiding. -/

noncomputable def LineBundle.contractionInv {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    𝟙_ X.toScheme.Modules ⟶ L.toModules ⊗ AlgebraicGeometry.Scheme.Modules.dual L.toModules :=
  haveI : L.toModules.IsLocallyFree := L.locallyFree
  AlgebraicGeometry.Scheme.Modules.homOfTopSection _
      (AlgebraicGeometry.Scheme.Modules.coevSection L.toModules) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules).hom ≫
    (β_ (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules).hom

/-! ### The contraction is an isomorphism

`contractionHom = β ≫ ev` and `contractionInv = coev ≫ β` where `coev = DualZigzag.coevHom L`
(`1 ↦ coevSection L`) and `ev = dualEv L`. The two braidings cancel (`SymmetricCategory.symmetry`), so
`inv_hom_id` is the rank-one statement `coev ≫ ev = 𝟙_{O_X}` ("`dim L = 1`"), which is checked on
sections over frame opens `W ⊆ U_i` of the trivializing cover `locallyFreeData L`: there
`coev|_W = Σ_j e_j^∨ ⊗ e_j` for *any* finite frame datum of `L|_W` (`Frame.coevOfData_eq`), in particular
for the one-element frame `(ε, ε^∨)` given by `IsFrame` (Stacks 01CY/0B8K), and
`ev(ε^∨ ⊗ ε) = ε^∨(ε) = coord_ε(ε) = 1` (`IsFrame.coord_frame`). `hom_inv_id` follows because `ev` is an
isomorphism for a line bundle (`isIso_internalHomEval_dual`, Stacks 01CT/0B8K). -/

section ContractionIso

open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Frame
  AlgebraicGeometry.Scheme.Modules.DualZigzag

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A section `ε ∈ Γ(M, W)` as a section of `M.over W` (`V ↦ ε|_V`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.Frame.secOfSection (M : X.Modules) (W : X.Opens)
    (ε : Γ(M, W)) : (M.over W).sections :=
  _root_.PresheafOfModules.sectionsMk (fun V => M.presheaf.map V.unop.hom.op ε)
    (fun ⦃V V'⦄ i => by
      have h : M.val.presheaf.map V.unop.hom.op ≫ M.val.presheaf.map i.unop.left.op =
          M.val.presheaf.map V'.unop.hom.op := by
        rw [← M.val.presheaf.map_comp]; rfl
      exact congrArg (fun φ => φ.hom ε) h)

/-- The coordinate functional `ε^∨ : x ↦ coord_ε(x)` of a frame `ε` of `M` on `W`, as a compatible family
of local functionals (`Frame.LH M W = LocalDualSections X M W`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.IsFrame.coordLH {M : X.Modules} {W : X.Opens}
    {ε : Γ(M, W)} (hf : IsFrame M W ε) : LH M W :=
  ⟨fun V => (hf.coordEquiv (leOfHom V.hom)).toLinearMap, fun _ V' i x =>
    hf.coord_map (leOfHom i.left) (leOfHom V'.hom) x⟩

/-- `(ε, ε^∨)` is a (one-element) frame datum of `M|_W`: `m = coord_ε(m) • ε|_V`. -/
theorem AlgebraicGeometry.Scheme.Modules.IsFrame.isFrameData_coordLH {M : X.Modules} {W : X.Opens}
    {ε : Γ(M, W)} (hf : IsFrame M W ε) :
    IsFrameData M W (fun _ : PUnit.{u+1} => secOfSection M W ε) (fun _ => hf.coordLH) := by
  refine ⟨fun V m => ?_⟩
  rw [Fintype.sum_unique]
  exact (hf.coord_smul_frame (leOfHom V.hom) m).symm

/-- On `W ⊆ U_i` (with `U_i` carrying a finite frame), `coev|_W = Σ_j φ_j ⊗ e_j` for **any** finite frame
datum `(e, φ)` of `V|_W` (`Frame.coevOfData_eq`: the local coevaluation is frame-independent). -/
theorem AlgebraicGeometry.Scheme.Modules.DualZigzag.coevHom_app_one_eq_sum_of_isFrameData (V : X.Modules)
    [V.IsLocallyFree] (i : (locallyFreeData V).I) [hfin : Finite ((locallyFreeData V).generators i).I]
    (W : X.Opens) (hW : W ≤ (locallyFreeData V).X i) {I : Type u} [Fintype I]
    (e : I → (V.over W).sections) (φ : I → LH V W) (hfr : IsFrameData V W e φ) :
    (coevHom V).app W (unitOne W) =
      ∑ j, tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j)) := by
  let _ := Fintype.ofFinite ((locallyFreeData V).generators i).I
  have := (locallyFreeData_isLocallyFreeData V).isIso i
  rw [coevHom_app_one, coevSection_res V i W hW]
  unfold AlgebraicGeometry.Scheme.Modules.coevLocal
  rw [dif_pos hfin, coevOfData_res]
  have hEq := coevOfData_eq V W
    (fun j => resSec V (homOfLE hW) (((locallyFreeData V).generators i).s j))
    (fun j => AlgebraicGeometry.Scheme.Modules.localDualRestrict V (homOfLE hW) (dualBasisLocalHom V i j))
    (isFrameData_res V (homOfLE hW) _ _ (frameData V ((locallyFreeData V).generators i))) e φ hfr
  rw [hEq]
  unfold coevOfData
  exact (app_sum _ _ _ _).trans (Finset.sum_congr rfl fun j _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/-- **`coev ≫ ev = 𝟙` for a line bundle** (`dim L = 1`). Checked on sections over frame opens
`W ⊆ U_i`: `coev|_W = ε^∨ ⊗ ε` and `ev(ε^∨ ⊗ ε) = coord_ε(ε) = 1`. -/
theorem AlgebraicGeometry.Scheme.Modules.DualZigzag.coevHom_comp_dualEv (L : X.Modules) [L.IsLineBundle] :
    coevHom L ≫ dualEv L = 𝟙 (𝟙_ X.Modules) := by
  have hcov : ∀ p : X, ∃ (i : (locallyFreeData L).I) (W : X.Opens) (_ : W ≤ (locallyFreeData L).X i)
      (_ : p ∈ W) (e : Γ(L, W)), IsFrame L W e := fun p => by
    have hp : p ∈ (⨆ i, (locallyFreeData L).X i : X.Opens) := by
      rw [locallyFreeData_iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    obtain ⟨W, hWU, hpW, e, hf⟩ := exists_frame_le L hi
    exact ⟨i, W, hWU, hpW, e, hf⟩
  choose idx Wp hWp hpW ε hε using hcov
  refine hom_ext_of_cover_app Wp ?_ _ _ fun p W hW x => ?_
  · exact eq_top_iff.mpr fun q _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hpW q⟩
  · by_cases hfin : Finite ((locallyFreeData L).generators (idx p)).I
    · have hf : IsFrame L W (L.res hW (ε p)) := (hε p).restrict hW
      have hc := coevHom_app_one_eq_sum_of_isFrameData L (idx p) W (hW.trans (hWp p)) _ _
        hf.isFrameData_coordLH
      rw [Fintype.sum_unique] at hc
      have hval : (coevHom L ≫ dualEv L).app W (unitOne W) = unitOne W :=
        (congrArg ((dualEv L).app W) hc).trans
          ((dualEv_app_tensorSections_dualUnit L W _ _).trans (hf.coord_frame (leOfHom (topZ W).hom)))
      have h1 : (show Γ(X, W) from x) • unitOne W = x := mul_one (show Γ(X, W) from x)
      calc (coevHom L ≫ dualEv L).app W x
          = (coevHom L ≫ dualEv L).app W ((show Γ(X, W) from x) • unitOne W) := congrArg _ h1.symm
        _ = (show Γ(X, W) from x) • (coevHom L ≫ dualEv L).app W (unitOne W) :=
            AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ (show Γ(X, W) from x) (unitOne W)
        _ = (show Γ(X, W) from x) • unitOne W := by rw [hval]
        _ = x := h1
        _ = AlgebraicGeometry.Scheme.Modules.Hom.app (𝟙 (𝟙_ X.Modules)) W x := rfl
    · have hbot := locallyFreeData_X_eq_bot_of_not_finite L (idx p) hfin
      have hW' : W = ⊥ := le_bot_iff.mp (hbot ▸ (hW.trans (hWp p)))
      subst hW'
      have := subsingleton_sections_bot (𝟙_ X.Modules)
      exact Subsingleton.elim _ _

end ContractionIso

/-- `contractionInv = coev ≫ β` (reassociation only; `coevHom` is the first two factors). -/
theorem LineBundle.contractionInv_eq {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    L.contractionInv =
      AlgebraicGeometry.Scheme.Modules.DualZigzag.coevHom L.toModules ≫
        (β_ (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules).hom := by
  unfold LineBundle.contractionInv AlgebraicGeometry.Scheme.Modules.DualZigzag.coevHom
  exact (CategoryTheory.Category.assoc _ _ _).symm

/-- `contractionHom = β ≫ ev` with `ev` in the `dual` spelling (`dualEv`; definitional). -/
theorem LineBundle.contractionHom_eq {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    L.contractionHom =
      (β_ L.toModules (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).hom ≫
        AlgebraicGeometry.Scheme.Modules.dualEv L.toModules :=
  rfl

/-- `contractionInv ≫ contractionHom = 𝟙`: the braidings cancel and `coev ≫ ev = 𝟙` (`dim L = 1`,
`coevHom_comp_dualEv`). Stacks 01CT/0B8M. -/
theorem LineBundle.contraction_inv_hom_id {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    L.contractionInv ≫ L.contractionHom = 𝟙 _ := by
  rw [LineBundle.contractionInv_eq, LineBundle.contractionHom_eq, CategoryTheory.Category.assoc,
    ← CategoryTheory.Category.assoc (β_ _ _).hom, CategoryTheory.SymmetricCategory.symmetry,
    CategoryTheory.Category.id_comp]
  exact AlgebraicGeometry.Scheme.Modules.DualZigzag.coevHom_comp_dualEv L.toModules

/-- `contractionHom ≫ contractionInv = 𝟙`: `contractionHom` is an isomorphism (`ev` is, for a line
bundle: `isIso_internalHomEval_dual`, Stacks 01CT/0B8K), so `contraction_inv_hom_id` identifies
`contractionInv` with its inverse. -/
theorem LineBundle.contraction_hom_inv_id {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    L.contractionHom ≫ L.contractionInv = 𝟙 _ := by
  -- `apply` (not `exact`): the `dual`/`internalHom` spelling check is done once (cf. `ModulesDualEv`)
  have hev : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.dualEv L.toModules) := by
    apply AlgebraicGeometry.Scheme.Modules.isIso_internalHomEval_dual
  have : CategoryTheory.IsIso L.contractionHom := by
    rw [LineBundle.contractionHom_eq]; infer_instance
  rw [CategoryTheory.IsIso.eq_inv_of_inv_hom_id L.contraction_inv_hom_id]
  exact CategoryTheory.IsIso.hom_inv_id _

/- The contraction `L ⊗ L^∨ ≅ O_X` of a line bundle: forward = braiding followed by evaluation
   (`internalHomEval`, `L^∨ = 𝓗om(L, O_X)`); inverse = the morphism `O_X → L^∨ ⊗ L` corresponding to the
   coevaluation section `coev ∈ Γ(X, L^∨ ⊗ L)`, followed by the braiding. -/

noncomputable def LineBundle.contraction {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    L.toModules ⊗ AlgebraicGeometry.Scheme.Modules.dual L.toModules ≅ 𝟙_ X.toScheme.Modules where
  hom := L.contractionHom
  inv := L.contractionInv
  hom_inv_id := L.contraction_hom_inv_id
  inv_hom_id := L.contraction_inv_hom_id

/- The underlying module of `L.zpow p` (`moduleTensorPower` / `moduleNegativePower`) is identified with the
   monoidal integer power. -/

noncomputable def LineBundle.zpowIsoMzpow {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    (p : ℤ) → ((L.zpow p).toModules ≅
      AlgebraicGeometry.Scheme.Modules.mzpow L.toModules (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p)
  | (n : ℕ) => AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow L.toModules n
  | Int.negSucc n =>
    AlgebraicGeometry.Scheme.Modules.tensorPowerIsoMpow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (n + 1)

/- The isomorphism data `L^{p+q} ≅ L^p ⊗ L^q` (`⊗` being `Modules.tensor`): pass to the monoidal integer
   powers, use `mzpowAdd`, and transport both ends back through `zpowIsoMzpow` and `tensorIsoTensorObj`. -/

noncomputable def LineBundle.zpowAddIso {k : Type u} [Field k] {X : Variety k} (L : LineBundle X)
    (p q : ℤ) : (L.zpow (p + q)).toModules ≅
      AlgebraicGeometry.Scheme.Modules.tensor (L.zpow p).toModules (L.zpow q).toModules :=
  L.zpowIsoMzpow (p + q) ≪≫
    AlgebraicGeometry.Scheme.Modules.mzpowAdd L.contraction p q ≪≫
    (CategoryTheory.MonoidalCategory.tensorIso (L.zpowIsoMzpow p) (L.zpowIsoMzpow q)).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (L.zpow p).toModules (L.zpow q).toModules).symm

theorem LineBundle.zpow_add {k : Type u} [Field k] {X : Variety k} (L : LineBundle X)
    (p q : ℤ) : Nonempty ((L.zpow (p + q)).toModules ≅
      AlgebraicGeometry.Scheme.Modules.tensor (L.zpow p).toModules (L.zpow q).toModules) :=
  ⟨L.zpowAddIso p q⟩

/- `L^1 ≅ L`, `L^{-1} ≅ L^∨`: the first power is `M ⊗ O_X`; use the right unitor. -/

noncomputable def LineBundle.zpowOneIso {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    (L.zpow 1).toModules ≅ L.toModules :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L.toModules (SheafOfModules.unit X.toScheme.ringCatSheaf) ≪≫
    ρ_ L.toModules

noncomputable def LineBundle.zpowNegOneIso {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    (L.zpow (-1)).toModules ≅ AlgebraicGeometry.Scheme.Modules.dual L.toModules :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      (SheafOfModules.unit X.toScheme.ringCatSheaf) ≪≫
    ρ_ (AlgebraicGeometry.Scheme.Modules.dual L.toModules)

end
