import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # Auxiliary facts for the sections of the thickening

Variable-level facts used to assemble `jetNeighborhood_globalSections_decomp`.

1. `pullbackSectionToPushforward g M` (Γ(T, g^*M) → Γ(X, M ⊗ g_*O_T), the projection formula on global
   sections) is a two-sided inverse of `pushforwardSectionToPullback g M`, is additive, and is
   *semilinear along `g^♯`*: `Φ₀ (g^♯ r • P) = r • Φ₀ P` for `r ∈ Γ(X, O_X)`. The last point is the
   `k`-linearity bookkeeping of `jetNeighborhood_globalSections_decomp`:
   `ρ_⁻¹` is a morphism of `O_T`-modules, so its `⊤`-section map is `Γ(T, O_T)`-linear; the
   `Γ(X, O_X)`-module structure on `Γ(X, g_* N) = Γ(T, N)` is restriction of scalars along `g^♯ = g.appTop`
   (definitional: `SheafOfModules.pushforward` is `restrictScalars` of `pushforward₀`), and `θ⁻¹`
   (projection formula) is a morphism of `O_X`-modules.
2. Global sections of `M ⊗ ⨁_q N_q` decompose along `M ◁ π_q` / `M ◁ ι_q`: `M ◁ -` is additive
   (`Modules.tensorLeft_additive`), so `M ◁ (Σ_q π_q ≫ ι_q) = Σ_q M ◁ (π_q ≫ ι_q)` and
   `biproduct.total` gives `x = Σ_q (M ◁ ι_q)(M ◁ π_q) x` on `⊤`; the orthogonality relations
   `(M ◁ π_{q'})(M ◁ ι_q) = δ_{q q'}` come from `biproduct.ι_π_self` / `biproduct.ι_π_ne` and
   `M ◁ 0 = 0`.

References: Stacks 01E8 (projection formula), 01LQ (`p_*O_{Spec_X A} = A`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T X : AlgebraicGeometry.Scheme.{u}}

/-- `Φ₀ ∘ Ψ₀ = id` (`θ⁻¹ ≫ θ = 𝟙`, `ρ⁻¹ ≫ ρ = 𝟙` on `⊤`-sections). -/
theorem pullbackSectionToPushforward_pushforwardSectionToPullback (g : T ⟶ X) (M : X.Modules)
    [M.IsLineBundle]
    (s : ((M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M
      (AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback g M s) = s := by
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_eq,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq]
  exact (congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_hom_inv (ρ_ _) _)).trans
    (AlgebraicGeometry.Scheme.Modules.app_top_hom_inv
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)) s)

/-- `Φ₀` is additive. -/
theorem pullbackSectionToPushforward_add (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (P Q : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M (P + Q) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P +
        AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M Q := by
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq, map_add]
  exact map_add _ _ _

/-- The scalar action on `⊤`-sections of a pushforward is restriction along `g.appTop` (definitional). -/
theorem pushforward_smul_top (g : T ⟶ X) (N : T.Modules) (r : X.ringCatSheaf.obj.obj (Opposite.op ⊤))
    (y : (((AlgebraicGeometry.Scheme.Modules.pushforward g).obj N).val.obj (Opposite.op ⊤) : Type u)) :
    r • y = (show (N.val.obj (Opposite.op ⊤) : Type u) from
      (show T.ringCatSheaf.obj.obj (Opposite.op ⊤) from g.appTop.hom r) •
        (show (N.val.obj (Opposite.op ⊤) : Type u) from y)) := rfl

/-- **Semilinearity of `Φ₀` along `g^♯`**: `Φ₀ (g^♯ r • P) = r • Φ₀ P`. -/
theorem pullbackSectionToPushforward_smul (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (r : X.ringCatSheaf.obj.obj (Opposite.op ⊤))
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M
        ((show T.ringCatSheaf.obj.obj (Opposite.op ⊤) from g.appTop.hom r) • P) =
      r • AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P := by
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq]
  have h1 := LinearMap.map_smul ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv.val.app
    (Opposite.op ⊤)).hom (show T.ringCatSheaf.obj.obj (Opposite.op ⊤) from g.appTop.hom r) P
  rw [h1]
  exact LinearMap.map_smul ((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
    (SheafOfModules.unit T.ringCatSheaf)).inv.val.app (Opposite.op ⊤)).hom r _

/-- `(M ◁ e.inv)(M ◁ e.hom) x = x` on `⊤`-sections. -/
theorem app_top_whiskerLeft_hom_inv (M : X.Modules) {A B : X.Modules} (e : A ≅ B)
    (x : ((M ⊗ A).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ e.inv).val.app (Opposite.op ⊤)).hom (((M ◁ e.hom).val.app (Opposite.op ⊤)).hom x) = x :=
  AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_inv_hom M e.symm x

/-- `M ◁ 0 = 0` on `⊤`-sections. -/
theorem app_top_whiskerLeft_zero (M : X.Modules) {A B : X.Modules}
    (x : ((M ⊗ A).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ (0 : A ⟶ B)).val.app (Opposite.op ⊤)).hom x = 0 := by
  rw [AlgebraicGeometry.Scheme.Modules.whiskerLeft_zero']
  rfl

/-- `(M ◁ π_q)(M ◁ ι_q) c = c`. -/
theorem app_top_whiskerLeft_biproduct_ι_π_self (M : X.Modules) {ι : Type} [Fintype ι]
    (N : ι → X.Modules) (q : ι) (c : ((M ⊗ N q).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ CategoryTheory.Limits.biproduct.π N q).val.app (Opposite.op ⊤)).hom
      (((M ◁ CategoryTheory.Limits.biproduct.ι N q).val.app (Opposite.op ⊤)).hom c) = c := by
  rw [← AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp,
    CategoryTheory.Limits.biproduct.ι_π_self, AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_id]

/-- `(M ◁ π_{q'})(M ◁ ι_q) c = 0` for `q ≠ q'`. -/
theorem app_top_whiskerLeft_biproduct_ι_π_ne (M : X.Modules) {ι : Type} [Fintype ι]
    (N : ι → X.Modules) {q q' : ι} (h : q ≠ q') (c : ((M ⊗ N q).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ CategoryTheory.Limits.biproduct.π N q').val.app (Opposite.op ⊤)).hom
      (((M ◁ CategoryTheory.Limits.biproduct.ι N q).val.app (Opposite.op ⊤)).hom c) = 0 := by
  rw [← AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp,
    CategoryTheory.Limits.biproduct.ι_π_ne _ h, AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_zero]

/-- **Sections of `M ⊗ ⨁ N` decompose along `M ◁ π_q`**: `x = Σ_q (M ◁ ι_q)((M ◁ π_q) x)`. -/
theorem app_top_whiskerLeft_biproduct_eq_sum (M : X.Modules) {ι : Type} [Fintype ι]
    (N : ι → X.Modules) (x : ((M ⊗ CategoryTheory.Limits.biproduct N).val.obj (Opposite.op ⊤) : Type u)) :
    x = ∑ q : ι, ((M ◁ CategoryTheory.Limits.biproduct.ι N q).val.app (Opposite.op ⊤)).hom
      (((M ◁ CategoryTheory.Limits.biproduct.π N q).val.app (Opposite.op ⊤)).hom x) := by
  have hadd := AlgebraicGeometry.Scheme.Modules.tensorLeft_additive M
  have htot : ∑ q : ι, M ◁ (CategoryTheory.Limits.biproduct.π N q ≫ CategoryTheory.Limits.biproduct.ι N q) =
      M ◁ (𝟙 (CategoryTheory.Limits.biproduct N)) := by
    have h := congrArg (CategoryTheory.MonoidalCategory.tensorLeft M).map
      (CategoryTheory.Limits.biproduct.total (f := N))
    rw [Functor.map_sum] at h
    exact h
  have h := congrArg (fun f : M ⊗ CategoryTheory.Limits.biproduct N ⟶ M ⊗ CategoryTheory.Limits.biproduct N =>
    (f.val.app (Opposite.op ⊤)).hom x) htot
  rw [AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_id] at h
  refine h.symm.trans ?_
  have e : ∀ f : ι → (M ⊗ CategoryTheory.Limits.biproduct N ⟶ M ⊗ CategoryTheory.Limits.biproduct N),
      ((∑ q, f q).val.app (Opposite.op ⊤)).hom x = ∑ q, ((f q).val.app (Opposite.op ⊤)).hom x := by
    intro f
    let e : (M ⊗ CategoryTheory.Limits.biproduct N ⟶ M ⊗ CategoryTheory.Limits.biproduct N) →+
        ((M ⊗ CategoryTheory.Limits.biproduct N).val.obj (Opposite.op ⊤) : Type u) :=
      { toFun := fun f => (f.val.app (Opposite.op ⊤)).hom x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact map_sum e f Finset.univ
  rw [e]
  exact Finset.sum_congr rfl fun q _ =>
    AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M _ _ x

/-! ## Global sections of `p^*M` for `p : T → X` with `p_*O_T ≅ ⨁ N_q`

Abstract data: `p : T ⟶ X`, a line bundle `M` on `X`, a finite family `N : ι → X.Modules` with an
isomorphism `σ : ⨁ N ≅ p_*O_T`, and isomorphisms `g q : M ⊗ N q ≅ W q`. Then
`Γ(T, p^*M) ≃ ∏_q Γ(X, W q)`: `P ↦ (g_q ∘ (M ◁ π_q) ∘ (M ◁ σ⁻¹) ∘ Φ₀) P`, with inverse
`c ↦ Ψ₀ ((M ◁ σ) (Σ_q (M ◁ ι_q) (g_q⁻¹ c_q)))`. The forward map is additive and semilinear along
`p^♯`, hence `k`-linear for `globalSectionsModuleOver`. -/

section Decomposition

variable (p : T ⟶ X) (M : X.Modules) [M.IsLineBundle] {ι : Type} [Fintype ι]
  (N : ι → X.Modules)
  (σ : CategoryTheory.Limits.biproduct N ≅
    (AlgebraicGeometry.Scheme.Modules.pushforward p).obj (SheafOfModules.unit T.ringCatSheaf))
  (W : ι → X.Modules) (g : ∀ q, M ⊗ N q ≅ W q)

/-- The `q`-th coefficient `Γ(T, p^*M) → Γ(X, W q)`. -/
def affineSectionsCoeff
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) (q : ι) :
    ((W q).val.obj (Opposite.op ⊤) : Type u) :=
  ((g q).hom.val.app (Opposite.op ⊤)).hom
    (((M ◁ CategoryTheory.Limits.biproduct.π N q).val.app (Opposite.op ⊤)).hom
      (((M ◁ σ.inv).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward p M P)))

/-- Assembling a section of `p^*M` from its coefficients. -/
def affineSectionsAssemble (c : ∀ q, ((W q).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback p M
    (((M ◁ σ.hom).val.app (Opposite.op ⊤)).hom
      (∑ q, ((M ◁ CategoryTheory.Limits.biproduct.ι N q).val.app (Opposite.op ⊤)).hom
        (((g q).inv.val.app (Opposite.op ⊤)).hom (c q))))

theorem affineSectionsAssemble_coeff
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    affineSectionsAssemble p M N σ W g (affineSectionsCoeff p M N σ W g P) = P := by
  unfold affineSectionsAssemble affineSectionsCoeff
  have h2 := Finset.sum_congr (s₁ := Finset.univ) rfl fun q _ =>
    congrArg ((M ◁ CategoryTheory.Limits.biproduct.ι N q).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.app_top_hom_inv (g q)
        (((M ◁ CategoryTheory.Limits.biproduct.π N q).val.app (Opposite.op ⊤)).hom
          (((M ◁ σ.inv).val.app (Opposite.op ⊤)).hom
            (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward p M P))))
  rw [h2, ← AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_biproduct_eq_sum,
    AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_inv_hom,
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward]

theorem affineSectionsCoeff_assemble (c : ∀ q, ((W q).val.obj (Opposite.op ⊤) : Type u)) :
    affineSectionsCoeff p M N σ W g (affineSectionsAssemble p M N σ W g c) = c := by
  funext q'
  unfold affineSectionsAssemble affineSectionsCoeff
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_pushforwardSectionToPullback,
    AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_hom_inv,
    AlgebraicGeometry.Scheme.Modules.app_top_sum,
    Finset.sum_eq_single q' (fun q _ hq => by
      rw [AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_biproduct_ι_π_ne M N hq]) (fun h => absurd (Finset.mem_univ q') h),
    AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_biproduct_ι_π_self,
    AlgebraicGeometry.Scheme.Modules.app_top_inv_hom]

theorem affineSectionsCoeff_add
    (P Q : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    affineSectionsCoeff p M N σ W g (P + Q) =
      affineSectionsCoeff p M N σ W g P + affineSectionsCoeff p M N σ W g Q := by
  funext q
  unfold affineSectionsCoeff
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_add, map_add, map_add, map_add]
  rfl

/-- Semilinearity along `p^♯`. -/
theorem affineSectionsCoeff_smul (r : X.ringCatSheaf.obj.obj (Opposite.op ⊤))
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) (q : ι) :
    affineSectionsCoeff p M N σ W g
        ((show T.ringCatSheaf.obj.obj (Opposite.op ⊤) from p.appTop.hom r) • P) q =
      r • affineSectionsCoeff p M N σ W g P q := by
  unfold affineSectionsCoeff
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_smul, LinearMap.map_smul,
    LinearMap.map_smul, LinearMap.map_smul]

/-- **`Γ(T, p^*M) ≃ₗ[k] ∏_q Γ(X, W q)`** for `T → X → Spec k`, with `k`-module structures
`globalSectionsModuleOver`. -/
def affineSectionsLinearEquiv {k : Type u} [Field k]
    (s : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) :
    letI := AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver (p ≫ s)
      ((AlgebraicGeometry.Scheme.Modules.pullback p).obj M)
    letI := fun q : ι => AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver s (W q)
    ((((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u) ≃ₗ[k]
      ∀ q, ((W q).val.obj (Opposite.op ⊤) : Type u)) :=
  letI := AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver (p ≫ s)
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj M)
  letI := fun q : ι => AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver s (W q)
  { toFun := affineSectionsCoeff p M N σ W g
    invFun := affineSectionsAssemble p M N σ W g
    map_add' := affineSectionsCoeff_add p M N σ W g
    map_smul' := fun a P => by
      funext q
      exact affineSectionsCoeff_smul p M N σ W g
        (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom a) P q
    left_inv := affineSectionsAssemble_coeff p M N σ W g
    right_inv := affineSectionsCoeff_assemble p M N σ W g }

end Decomposition

end AlgebraicGeometry.Scheme.Modules

end
