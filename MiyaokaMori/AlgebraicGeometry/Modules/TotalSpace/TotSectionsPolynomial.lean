import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.CoproductSectionsLocallyFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalZero
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowNegIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMonomial
import MiyaokaMori.AlgebraicGeometry.Modules.TotLineMonomialMul
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineMonomialZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineMonomialZeroUnit
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Frames

/-! # Sections on the total space of a line bundle as polynomials in `ξ`

Global sections of `p_L^*M` on `Tot(L)` are `⊕_{q≥0} H^0(C̃, M⊗L^{-q})`, the `q`-th component being `c·ξ^q`; this
defines the ξ-coefficients and the ξ-degree, with: multiplication is convolution (degrees add), pullback along the
zero section is the `q = 0` component, and on an affine open with a frame the functions form the polynomial ring
`O(V)[t]` (`ξ = tε`). (In the paper: `C̃_(k)(L) = Spec ⊕_{q≤k} L^{-q}`, locally `O(V)[t]/(t^{k+1})`, and the
ξ-expansion of the coefficients.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

/- The `k`-module structure on global sections: when `T` is a `k`-scheme via `s : T → Spec k`, `Γ(T, M)` has scalars
   restricted along `k ≅ Γ(Spec k, ⊤) → Γ(T, ⊤)` (the global sections map of `s`). Used only as `letI`, not registered
   as a global instance. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver {k : Type u} [Field k]
    {T : AlgebraicGeometry.Scheme.{u}} (s : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (M : T.Modules) :
    Module k (M.val.obj (Opposite.op ⊤) : Type u) :=
  Module.compHom _ (show k →+* T.ringCatSheaf.obj.obj (Opposite.op ⊤) from
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom)

/- **`Γ(Tot(L), p^*M) ≅ ⊕_{q≥0} H^0(C̃, M ⊗ L^{-q})` (`k`-linear)**: `totLine_globalSections_decomp` is proved in the
   downstream companion module `TotSectionsPolynomialGlobalDecomp` (this file is close to the compile-time limit). -/

/- The `q`-th ξ-coefficient: `totalSpace.coefficient` (inverse of the projection formula + inverse of
   `p_*O_Tot ≅ ⊕ Sym^m L^∨` + `q`-th graded projection), transported by `coefficientModuleIso` to the coefficient
   line bundle `(M.zpow 1) ⊗ L^{-q}`. -/

noncomputable def xiCoefficient {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj
      (Opposite.op ⊤)) : Type u) :=
  ((L.coefficientModuleIso M q).hom.val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.totalSpace.coefficient L.toModules M.toModules q P)

/- The monomial `c·ξ^q ∈ Γ(Tot(L), p^*M)` (`c ∈ H^0(M ⊗ L^{-q})`): `totalSpace.monomial` through the same isomorphism. -/

noncomputable def xiMonomial {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ)
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.totalSpace.monomial L.toModules M.toModules q
    (((L.coefficientModuleIso M q).inv.val.app (Opposite.op ⊤)).hom c)

/-- **`xiMonomial` as a global-sections map** (definitional): `xiMonomial L M q c = Φ_q.app ⊤ c` with
`Φ_q := coefficientModuleIso⁻¹ ≫ τ ≫ ((M ◁ (Θ_q ≫ ι_q ≫ σ)) ≫ θ ≫ p_*(ρ_))`. Stated once so that the (expensive)
unfolding of `xiMonomial`/`monomial`/`pushforwardSectionToPullback` is done once per file. -/
theorem xiMonomial_eq_app {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ)
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    xiMonomial L M q c =
      (((L.coefficientModuleIso M q).inv ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).hom ≫
        ((M.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom)).val.app (Opposite.op ⊤)).hom c := rfl

/-! ## Composition rules at the level of sections (`rfl` lemmas)

The section maps over `⊤` of morphisms of `X.Modules`: composition is function composition and the identity is the
identity (by definition); the two composites of an isomorphism are identities. -/

theorem AlgebraicGeometry.Scheme.Modules.app_top_comp {X : AlgebraicGeometry.Scheme.{u}} {A B D : X.Modules}
    (f : A ⟶ B) (g : B ⟶ D) (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    ((f ≫ g).val.app (Opposite.op ⊤)).hom x =
      (g.val.app (Opposite.op ⊤)).hom ((f.val.app (Opposite.op ⊤)).hom x) := rfl

theorem AlgebraicGeometry.Scheme.Modules.app_top_id {X : AlgebraicGeometry.Scheme.{u}} {A : X.Modules}
    (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    ((𝟙 A : A ⟶ A).val.app (Opposite.op ⊤)).hom x = x := rfl

theorem AlgebraicGeometry.Scheme.Modules.app_top_inv_hom {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules}
    (e : A ≅ B) (x : (B.val.obj (Opposite.op ⊤) : Type u)) :
    (e.hom.val.app (Opposite.op ⊤)).hom ((e.inv.val.app (Opposite.op ⊤)).hom x) = x := by
  rw [← AlgebraicGeometry.Scheme.Modules.app_top_comp, e.inv_hom_id]
  rfl

theorem AlgebraicGeometry.Scheme.Modules.app_top_hom_inv {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules}
    (e : A ≅ B) (x : (A.val.obj (Opposite.op ⊤) : Type u)) :
    (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom x) = x := by
  rw [← AlgebraicGeometry.Scheme.Modules.app_top_comp, e.hom_inv_id]
  rfl

theorem AlgebraicGeometry.Scheme.Modules.app_top_zero {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) : (f.val.app (Opposite.op ⊤)).hom (0 : (A.val.obj (Opposite.op ⊤) : Type u)) = 0 :=
  map_zero _

theorem AlgebraicGeometry.Scheme.Modules.app_top_sum {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) {ι : Type*} (s : Finset ι) (x : ι → (A.val.obj (Opposite.op ⊤) : Type u)) :
    (f.val.app (Opposite.op ⊤)).hom (∑ i ∈ s, x i) = ∑ i ∈ s, (f.val.app (Opposite.op ⊤)).hom (x i) :=
  map_sum _ _ _

/- Left whiskering on `⊤`-sections: composition, identity, cancellation of isomorphisms; proved once abstractly, the
   concrete sites only use `(e)rw` (the concrete types involve `X.ringCatSheaf`, and `TopCat.Sheaf` is a `def`, so
   `rw`/`simp` with `whiskerLeft_comp` directly fails because of the instance-transparency mismatch). -/

theorem AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) {A B D : X.Modules} (f : A ⟶ B) (g : B ⟶ D)
    (x : ((M ⊗ A).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ (f ≫ g)).val.app (Opposite.op ⊤)).hom x =
      ((M ◁ g).val.app (Opposite.op ⊤)).hom (((M ◁ f).val.app (Opposite.op ⊤)).hom x) := by
  rw [CategoryTheory.MonoidalCategory.whiskerLeft_comp]
  rfl

theorem AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_id {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) {A : X.Modules} (x : ((M ⊗ A).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ (𝟙 A)).val.app (Opposite.op ⊤)).hom x = x := by
  rw [CategoryTheory.MonoidalCategory.whiskerLeft_id]
  rfl

theorem AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_inv_hom {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) {A B : X.Modules} (e : A ≅ B) (x : ((M ⊗ B).val.obj (Opposite.op ⊤) : Type u)) :
    ((M ◁ e.hom).val.app (Opposite.op ⊤)).hom (((M ◁ e.inv).val.app (Opposite.op ⊤)).hom x) = x := by
  rw [← AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp, e.inv_hom_id,
    AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_id]

/- Unfoldings of the two section maps of `TotLineCoefficientMap` (the `show … from` in the definition body leaves a
   `have` binding that blocks `rw`; here as `rfl` equations) and their mutual inverse laws
   (`θIso.inv ≫ θIso.hom = 𝟙`, `ρ.inv ≫ ρ.hom = 𝟙`). -/

theorem AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_eq {T X : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) (M : X.Modules)
    (s : ((M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback g M s =
      ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).hom.val.app (Opposite.op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf)).val.app
          (Opposite.op ⊤)).hom s) := rfl

theorem AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq {T X : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P =
      ((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).inv.val.app
          (Opposite.op ⊤)).hom
        (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv.val.app (Opposite.op ⊤)).hom P) := rfl

theorem AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward
    {T X : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback g M
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M P) = P := by
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_eq,
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq]
  exact (congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_inv_hom
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)) _)).trans
    (AlgebraicGeometry.Scheme.Modules.app_top_inv_hom (ρ_ _) P)

/-! ## Graded components of global sections of `N ⊗ (⊕_m S_m)`

For a graded quasi-coherent algebra `S` and a module `N`, the `q`-th component of a section `t` of `Γ(X, N ⊗ ⊕_m S_m)`
is `(N ◁ π_q) t ∈ Γ(X, N ⊗ S_q)`. The two results below (finite support, `t = Σ_q (N ◁ ι_q)(N ◁ π_q) t`) are the
concrete form of "Γ commutes with direct sums" (`X` quasi-compact); the ξ-coefficient decomposition
(`xiCoefficient_finite_support`, `eq_sum_xiMonomial`) follows from them by cancelling isomorphisms. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.tensorComponent {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (N : X.Modules) (q : ℕ)
    (t : ((N ⊗ S.total.carrier).val.obj (Opposite.op ⊤) : Type u)) :
    ((N ⊗ S.part q).val.obj (Opposite.op ⊤) : Type u) :=
  ((N ◁ S.totalProj q).val.app (Opposite.op ⊤)).hom t

/-- **Γ commutes with direct sums (`X` quasi-compact)**: a section `t` of `Γ(X, N ⊗ ⊕_m S_m)` has a finite set `Fs`
outside of which all graded components vanish, and `t = Σ_{q∈Fs} (N ◁ ι_q)((N ◁ π_q) t)`.

Reference: Stacks 01AI (sections of a direct sum of sheaves on a quasi-compact space = direct sum of the sections).

Proof: `N ⊗ -` preserves colimits (`tensorLeft_preservesColimitsOfSize`), so `N ⊗ ∐ S.part` with the `N ◁ ι_m` is a
coproduct cocone; `N ◁ ι_m ≫ N ◁ π_q = N ◁ (ι_m ≫ π_q)`, and `ι_m ≫ π_q` is `0` for `m ≠ q` (`Sigma.ι_desc` +
`dif_neg`, then `whiskerLeft_zeroMorphism`) and `𝟙` for `m = q` (`totalIncl_totalProj`). Then
`Modules.exists_finset_sum_eq_of_isColimit` (`CoproductSectionsLocallyFinite`: the sheafification unit is locally
surjective + elements of a coproduct in `ModuleCat` are finite sums + a finite subcover by quasi-compactness +
separatedness of sheaves) gives the claim. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.exists_finset_tensorComponent {X : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace X] (S : X.GradedQCAlgebra) (N : X.Modules)
    (t : ((N ⊗ S.total.carrier).val.obj (Opposite.op ⊤) : Type u)) :
    ∃ Fs : Finset ℕ, (∀ q, q ∉ Fs → S.tensorComponent N q t = 0) ∧
      ∑ q ∈ Fs, ((N ◁ S.totalIncl q).val.app (Opposite.op ⊤)).hom (S.tensorComponent N q t) = t := by
  have : PreservesColimitsOfSize.{0, 0} (CategoryTheory.MonoidalCategory.tensorLeft N) :=
    preservesColimitsOfSize_shrink _
  have hc : IsColimit ((CategoryTheory.MonoidalCategory.tensorLeft N).mapCocone
      (colimit.cocone (Discrete.functor S.part))) :=
    isColimitOfPreserves (CategoryTheory.MonoidalCategory.tensorLeft N)
      (colimit.isColimit (Discrete.functor S.part))
  have hp0 : ∀ m q : ℕ, m ≠ q →
      ((CategoryTheory.MonoidalCategory.tensorLeft N).mapCocone
        (colimit.cocone (Discrete.functor S.part))).ι.app ⟨m⟩ ≫ (N ◁ S.totalProj q) = 0 := by
    intro m q hmq
    have h0 : Sigma.ι S.part m ≫ S.totalProj q = 0 :=
      (Sigma.ι_desc (fun m => if h : m = q then CategoryTheory.eqToHom (congrArg S.part h) else 0) m).trans
        (dif_neg hmq)
    show (N ◁ Sigma.ι S.part m) ≫ (N ◁ S.totalProj q) = 0
    exact (CategoryTheory.MonoidalCategory.whiskerLeft_comp N _ _).symm.trans
      ((congrArg (fun g => N ◁ g) h0).trans (AlgebraicGeometry.Scheme.Modules.whiskerLeft_zeroMorphism N))
  have hp1 : ∀ m : ℕ,
      ((CategoryTheory.MonoidalCategory.tensorLeft N).mapCocone
        (colimit.cocone (Discrete.functor S.part))).ι.app ⟨m⟩ ≫ (N ◁ S.totalProj m) = 𝟙 _ := by
    intro m
    show (N ◁ Sigma.ι S.part m) ≫ (N ◁ S.totalProj m) = 𝟙 _
    exact (CategoryTheory.MonoidalCategory.whiskerLeft_comp N _ _).symm.trans
      ((congrArg (fun g => N ◁ g) (S.totalIncl_totalProj m)).trans
        (CategoryTheory.MonoidalCategory.whiskerLeft_id N _))
  obtain ⟨Fs, h1, h2⟩ := AlgebraicGeometry.Scheme.Modules.exists_finset_sum_eq_of_isColimit hc
    (fun q => N ◁ S.totalProj q) hp0 hp1 t
  exact ⟨Fs, h1, h2⟩

/-- **Γ commutes with direct sums, finiteness**: for `X` quasi-compact, a section of `Γ(X, N ⊗ ⊕_m S_m)` has only
finitely many nonzero graded components.

Reference: Stacks 01AI. Proof: the finite set `Fs` of `exists_finset_tensorComponent` contains the support. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.tensorComponent_finite {X : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace X] (S : X.GradedQCAlgebra) (N : X.Modules)
    (t : ((N ⊗ S.total.carrier).val.obj (Opposite.op ⊤) : Type u)) :
    {q : ℕ | S.tensorComponent N q t ≠ 0}.Finite := by
  obtain ⟨Fs, h1, -⟩ := S.exists_finset_tensorComponent N t
  exact Fs.finite_toSet.subset fun q hq => by_contra fun hn => hq (h1 q hn)

/-- **Γ commutes with direct sums, reconstruction**: for `X` quasi-compact, `t = Σ_q (N ◁ ι_q)((N ◁ π_q) t)`, the sum
over the nonzero components.

Reference: the other half of Stacks 01AI. Proof: `exists_finset_tensorComponent` gives the sum over `Fs ⊇ support`
equal to `t`; the terms in `Fs \ support` are `0` (`map_zero`); `Finset.sum_subset`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.sum_tensorComponent {X : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace X] (S : X.GradedQCAlgebra) (N : X.Modules)
    (t : ((N ⊗ S.total.carrier).val.obj (Opposite.op ⊤) : Type u)) :
    ∑ q ∈ (S.tensorComponent_finite N t).toFinset,
      ((N ◁ S.totalIncl q).val.app (Opposite.op ⊤)).hom (S.tensorComponent N q t) = t := by
  obtain ⟨Fs, h1, h2⟩ := S.exists_finset_tensorComponent N t
  refine (Finset.sum_subset (fun q hq => ?_) (fun q _ hq => ?_)).trans h2
  · by_contra hn
    exact ((S.tensorComponent_finite N t).mem_toFinset.mp hq) (h1 q hn)
  · have h0 : S.tensorComponent N q t = 0 := by
      by_contra hne
      exact hq ((S.tensorComponent_finite N t).mem_toFinset.mpr hne)
    rw [h0]
    exact map_zero _

/-- **`Sym^q(L^∨) → (L^∨)^{⊗q} → Sym^q(L^∨)` is the identity on a line bundle**
(`symPartToTensorPower ≫ tensorPowerToSymPart = 𝟙`; `Sym^q` and `⊗^q` coincide on a line bundle, and the paper
writes `L^{-q}` for both).

Proof: by definition `symPartToTensorPower L q = symPartToMonoidalPow (L^∨) q ≫ powIso.hom` and
`tensorPowerToSymPart L q = powIso.inv ≫ [cast] symPowπ (L^∨) q` (quasi-coherent branch for `L^∨`), and
`symPartToMonoidalPow (L^∨) q = [cast] inv (symPowπ (L^∨) q)` (`symPowπ` is an isomorphism for a line bundle,
`SymPowLineBundle`). After cancelling `powIso.hom ≫ powIso.inv` what remains is `[cast] inv symPowπ ≫ [cast] symPowπ = 𝟙`;
`generalize` then `subst` the equation `symGradedAlgebra (L^∨) = symGradedAlgebraOfQC (L^∨) hq` (`dif_pos`), so both
casts become identities, and this is `IsIso.inv_hom_id`.
(The other composite `tensorPowerToSymPart ≫ symPartToMonoidalPow = powIso.inv` is in `JetWeightComponentEqCoefficient`,
by the same method.) -/
theorem AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower_tensorPowerToSymPart
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q ≫
      AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L q = 𝟙 _ := by
  exact AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower_comp_tensorPowerToSymPart L q

/- The intermediate section of the coefficient decomposition: `P ∈ Γ(Tot, p^*M)` is sent by the inverse projection
   formula to `Γ(C̃, M ⊗ p_*O_Tot)`, then by the inverse of `p_*O_Tot ≅ ⊕ S_m` to `Γ(C̃, M ⊗ ⊕_m S_m)`; the
   ξ-coefficients are its graded components (up to a change of spelling). -/

noncomputable def xiBaseSection {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    ((M.toModules ⊗ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total.carrier).val.obj (Opposite.op ⊤) : Type u) :=
  ((M.toModules ◁ (AlgebraicGeometry.Scheme.relativeSpec.structureIso
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv).val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules P)

theorem xiCoefficient_eq_tensorComponent {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiCoefficient L M P q =
      ((L.coefficientModuleIso M q).hom.val.app (Opposite.op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
            (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv.val.app
              (Opposite.op ⊤)).hom
          (((M.toModules ◁ AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L.toModules q).val.app
              (Opposite.op ⊤)).hom
            ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).tensorComponent M.toModules q
                (xiBaseSection L M P)))) := by
  unfold xiCoefficient xiBaseSection AlgebraicGeometry.Scheme.GradedQCAlgebra.tensorComponent
    AlgebraicGeometry.Scheme.totalSpace.coefficient AlgebraicGeometry.Scheme.totalSpace.coefficientHom
  show (((L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj q ≫ AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L.toModules q))).val.app (Opposite.op ⊤)).hom ((AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules P)))) = _
  exact congrArg (fun y => (((L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv).val.app (Opposite.op ⊤)).hom (y)))
    ((AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules _ _ _).trans (AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules _ _ _))

theorem xiCoefficient_support_subset {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    {q : ℕ | xiCoefficient L M P q ≠ 0} ⊆
      {q : ℕ | (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).tensorComponent M.toModules q
          (xiBaseSection L M P) ≠ 0} := by
  intro q hq h0
  apply hq
  rw [xiCoefficient_eq_tensorComponent, h0]
  exact (congrArg _ (congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_zero _))).trans
    ((congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_zero _)).trans
      (AlgebraicGeometry.Scheme.Modules.app_top_zero _))

/-- **Every section has only finitely many nonzero ξ-coefficients** (`P = Σ_q c_q ξ^q` is a finite sum).

Proof: by `xiCoefficient_eq_tensorComponent`, the ξ-coefficient is the `q`-th graded component of the section
`xiBaseSection` of `Γ(C̃, M ⊗ ⊕_m S_m)` followed by three module morphisms; the index set of nonzero coefficients is
contained in the support of the graded components (`xiCoefficient_support_subset`), which is finite
(`tensorComponent_finite`, `C̃` quasi-compact: `Variety.compactSpace`). -/
theorem xiCoefficient_finite_support {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    {q : ℕ | xiCoefficient L M P q ≠ 0}.Finite := by
  have : CompactSpace C.toScheme := Variety.compactSpace C.toVariety
  exact ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).tensorComponent_finite M.toModules
      (xiBaseSection L M P)).subset (xiCoefficient_support_subset L M P)

theorem xiMonomial_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ) : xiMonomial L M q 0 = 0 := by
  unfold xiMonomial AlgebraicGeometry.Scheme.totalSpace.monomial
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_eq]
  exact (congrArg _ (congrArg _ (congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_zero _)))).trans
    ((congrArg _ (congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_zero _))).trans
      ((congrArg _ (AlgebraicGeometry.Scheme.Modules.app_top_zero _)).trans
        (AlgebraicGeometry.Scheme.Modules.app_top_zero _)))

theorem xiMonomial_xiCoefficient_eq {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiMonomial L M q (xiCoefficient L M P q) =
      (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q)).val.app (Opposite.op ⊤)).hom (((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).tensorComponent M.toModules q (xiBaseSection L M P)))))) := by
  unfold xiMonomial xiCoefficient
  rw [AlgebraicGeometry.Scheme.Modules.app_top_hom_inv]
  unfold AlgebraicGeometry.Scheme.totalSpace.monomial AlgebraicGeometry.Scheme.totalSpace.coefficient
    AlgebraicGeometry.Scheme.totalSpace.monomialHom AlgebraicGeometry.Scheme.totalSpace.coefficientHom
    xiBaseSection AlgebraicGeometry.Scheme.GradedQCAlgebra.tensorComponent
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_eq]
  show (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total))).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj q ≫ AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L.toModules q))).val.app (Opposite.op ⊤)).hom ((AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules P))))))) = _
  refine congrArg (fun y => (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.app (Opposite.op ⊤)).hom (y))) ?_
  refine (congrArg (fun y => (((M.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total))).val.app (Opposite.op ⊤)).hom (y))
    (AlgebraicGeometry.Scheme.Modules.app_top_inv_hom (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)) _)).trans ?_
  refine ((AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules _ _ _).trans (AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules _ _ _)).trans ?_
  refine congrArg (fun z => (((M.toModules ◁ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q)).val.app (Opposite.op ⊤)).hom (z))) ?_
  refine (congrArg (fun y => (((M.toModules ◁ AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q)).val.app (Opposite.op ⊤)).hom (y))
    ((AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules _ _ _).trans (AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules _ _ _))).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_comp M.toModules (AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L.toModules q) (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q) _).symm.trans ?_
  rw [AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower_tensorPowerToSymPart]
  exact AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_id M.toModules _

/-- **`P = Σ_q c_q ξ^q`** (`c_q` the `q`-th ξ-coefficient, the sum over the nonzero coefficients).

Proof: monomial ∘ coefficient = `pushforwardSectionToPullback ∘ (M ◁ σ) ∘ (M ◁ ι_q) ∘ (q-th component)`
(`xiMonomial_xiCoefficient_eq`: `τ.inv ≫ τ.hom`, `Θ'_q ≫ Θ_q` and the two directions of `coefficientModuleIso` cancel).
Enlarge the sum to the support of the graded components (the extra terms have coefficient `0`, `xiMonomial_zero`),
move the sum inside by linearity, use `sum_tensorComponent` to get `xiBaseSection`, and cancel
`σ⁻¹ ≫ σ = 𝟙`, `θ⁻¹ ≫ θ = 𝟙`, `ρ⁻¹ ≫ ρ = 𝟙` to return to `P`. -/
theorem eq_sum_xiMonomial {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    P = ∑ q ∈ (xiCoefficient_finite_support L M P).toFinset, xiMonomial L M q (xiCoefficient L M P q) := by
  have : CompactSpace C.toScheme := Variety.compactSpace C.toVariety
  rw [Finset.sum_subset (s₂ := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).tensorComponent_finite M.toModules (xiBaseSection L M P)).toFinset)
    (Set.Finite.toFinset_subset_toFinset.mpr (xiCoefficient_support_subset L M P))]
  · rw [Finset.sum_congr rfl (fun q _ => xiMonomial_xiCoefficient_eq L M P q)]
    refine Eq.symm ?_
    refine ((AlgebraicGeometry.Scheme.Modules.app_top_sum (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom _ _).symm.trans
      (congrArg (fun y => (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom).val.app (Opposite.op ⊤)).hom (y))
        ((AlgebraicGeometry.Scheme.Modules.app_top_sum (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) _ _).symm.trans
          (congrArg (fun y => (((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.app (Opposite.op ⊤)).hom (y))
            (AlgebraicGeometry.Scheme.Modules.app_top_sum (M.toModules ◁ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) _ _).symm)))).trans ?_
    refine (congrArg (fun y => (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.app (Opposite.op ⊤)).hom ((((M.toModules ◁ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)).val.app (Opposite.op ⊤)).hom (y))))
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.sum_tensorComponent (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) M.toModules (xiBaseSection L M P))).trans ?_
    unfold xiBaseSection
    refine (congrArg (fun y => (((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom).val.app (Opposite.op ⊤)).hom ((((AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf))).val.app (Opposite.op ⊤)).hom (y)))
      (AlgebraicGeometry.Scheme.Modules.app_top_whiskerLeft_inv_hom M.toModules (AlgebraicGeometry.Scheme.relativeSpec.structureIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) _)).trans ?_
    exact AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward _ _ _
  · intro q _ hq
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hq
    rw [hq, xiMonomial_zero]

theorem xiCoefficient_xiMonomial {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q q' : ℕ)
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    xiCoefficient L M (xiMonomial L M q c) q' =
      if h : q = q' then h ▸ c else 0 := by
  split_ifs with h
  · subst q'
    simp only [xiCoefficient, xiMonomial,
      AlgebraicGeometry.Scheme.totalSpace.coefficient_monomial_eq]
    rw [← ModuleCat.comp_apply]
    change (((L.coefficientModuleIso M q).inv ≫
      (L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom c = c
    have hh := congrArg (fun f => (f.val.app (Opposite.op ⊤)).hom c)
      (L.coefficientModuleIso M q).inv_hom_id
    rw [hh]
    exact ModuleCat.id_apply _ _
  · unfold xiCoefficient xiMonomial
    rw [AlgebraicGeometry.Scheme.totalSpace.coefficient_monomial_eq_zero_of_ne L.toModules
      M.toModules (Ne.symm h)]
    exact map_zero _

/- The ξ-degree: the largest index of a nonzero coefficient (finite support by `xiCoefficient_finite_support`; `⊥` for
   `P = 0`). -/

noncomputable def xiDegree {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) : WithBot ℕ :=
  (xiCoefficient_finite_support L M P).toFinset.max

theorem xiDegree_lt_iff {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (r : ℕ) :
    xiDegree L M P ≤ (r : WithBot ℕ) ↔ ∀ q > r, xiCoefficient L M P q = 0 := by
  rw [xiDegree, Finset.max_le_iff]
  constructor
  · intro h q hqr
    by_contra hq
    have hmem : q ∈ (xiCoefficient_finite_support L M P).toFinset :=
      (xiCoefficient_finite_support L M P).mem_toFinset.mpr hq
    have hle : (q : WithBot ℕ) ≤ (r : WithBot ℕ) := h q hmem
    exact (not_le_of_gt hqr) (WithBot.coe_le_coe.mp hle)
  · intro h q hq
    have hne : xiCoefficient L M P q ≠ 0 :=
      (xiCoefficient_finite_support L M P).mem_toFinset.mp hq
    have hle : q ≤ r := by
      by_contra hn
      exact hne (h q (Nat.lt_of_not_ge hn))
    exact WithBot.coe_le_coe.mpr hle

/- Multiplication of sections on `Tot(L)`: `P ⊗ P'` is a section of `p^*M ⊗ p^*M'`, sent to a section of `p^*(M ⊗ M')`
   through `p^*M ⊗ p^*M' ≅ p^*(M ⊗ M')` (pullback commutes with tensor products) and
   `(M.tensor M').toModules = M ⊗ M'`. -/

noncomputable def xiSectionMul {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (M.tensor M').toModules).val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.tensor_toModules M M').symm)).app ⊤ (sectionTensor P P')

/-- **`xiSectionMul` as a global-sections map** (definitional): `xiSectionMul x y = (δ⁻¹ ≫ p^*τ⁻¹).app ⊤ (x ⊗ y)`
(`eqToHom rfl = 𝟙`, `τ'.hom (sectionTensor x y) = tensorSections x y`). -/
theorem xiSectionMul_eq_app_tensorSections {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (x : ((((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules).val.obj (Opposite.op ⊤)) : Type u))
    (y : ((((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules).val.obj (Opposite.op ⊤)) : Type u)) :
    xiSectionMul L M M' x y =
      (((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules).inv).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules) ⊤ x y) := rfl

/- The tensor product of coefficients: `c ∈ H^0(M ⊗ L^{-a})`, `c' ∈ H^0(M' ⊗ L^{-b})`, `a + b = q`; the section obtained
   from `c ⊗ c'` through the canonical isomorphism `(M ⊗ L^{-a}) ⊗ (M' ⊗ L^{-b}) ≅ (M ⊗ M') ⊗ L^{-q}`. -/

/- The multiplication of coefficient line bundles `(M ⊗ L^{-a}) ⊗ (M' ⊗ L^{-b}) → (M ⊗ M') ⊗ L^{-q}` (`a + b = q`): both
   sides are rewritten through `coefficientModuleIso` as `M ⊗ T_a`, `M' ⊗ T_b` (`T = (L^∨)^{⊗·}`), the middle-four
   interchange `tensorμ` of the symmetric monoidal category gives `(M ⊗ M') ⊗ (T_a ⊗ T_b)`, and `T_a ⊗ T_b → T_{a+b}`
   is the concatenation isomorphism `monoidalPowCat` of `monoidalPow`. -/

noncomputable def tensorCoefficientsHom {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q) :
    AlgebraicGeometry.Scheme.Modules.tensor ((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules
        ((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules ⟶
      (((M.tensor M').zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules :=
  let D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  let pw := AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower D
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom
      ((L.coefficientModuleIso M a).inv ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom)
      ((L.coefficientModuleIso M' b).inv ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom) ≫
    CategoryTheory.MonoidalCategory.tensorμ M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D a)
      M'.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D b) ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules).inv
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (pw a).inv (pw b).inv ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat D a b).hom ≫ (pw (a + b)).hom ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D) hab)) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.tensor M').toModules
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D q)).inv ≫
    (L.coefficientModuleIso (M.tensor M') q).hom

noncomputable def tensorCoefficients {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q)
    (c : ((((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (c' : ((((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    (((((M.tensor M').zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj
      (Opposite.op ⊤)) : Type u) :=
  ((tensorCoefficientsHom L M M' hab).val.app (Opposite.op ⊤)).hom (sectionTensor c c')

/-- `sectionTensor 0 t = 0`: `moduleTensorSection_zero_left` in the section spelling used here
(`(M.val.obj (op ⊤) : Type u)` rather than `Γ(M, ⊤)`; definitionally the same, but `rw` does not identify them). -/
theorem sectionTensor_zero_left {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (t : (M'.val.obj (Opposite.op ⊤) : Type u)) :
    sectionTensor (M := M) (0 : (M.val.obj (Opposite.op ⊤) : Type u)) t = 0 :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_left (M := M) (N := M') (U := ⊤) t

/-- `sectionTensor s 0 = 0`: `moduleTensorSection_zero_right` in the section spelling used here. -/
theorem sectionTensor_zero_right {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionTensor (M' := M') s (0 : (M'.val.obj (Opposite.op ⊤) : Type u)) = 0 :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_right (M := M) (N := M') (U := ⊤) s

/-- The tensor product of coefficients preserves zero in the first variable: `sectionTensor 0 c' = 0`, then `map_zero`
of a module morphism. -/
theorem tensorCoefficients_zero_left {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q)
    (c' : ((((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    tensorCoefficients L M M' hab 0 c' = 0 := by
  unfold tensorCoefficients
  rw [sectionTensor_zero_left]
  exact map_zero _

/-- The tensor product of coefficients preserves zero in the second variable: `sectionTensor c 0 = 0`
(`moduleTensorSection_zero_right`), then `map_zero` of a module morphism. -/
theorem tensorCoefficients_zero_right {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q)
    (c : ((((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    tensorCoefficients L M M' hab c 0 = 0 := by
  unfold tensorCoefficients
  rw [sectionTensor_zero_right]
  exact map_zero _

/-- Coefficients above the degree vanish: if `xiDegree P < n` then `xiCoefficient P n = 0` (contrapositive of
`Finset.le_max`). -/
theorem xiCoefficient_eq_zero_of_xiDegree_lt {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) {n : ℕ}
    (hn : xiDegree L M P < (n : WithBot ℕ)) : xiCoefficient L M P n = 0 := by
  by_contra h
  have hmem : n ∈ (xiCoefficient_finite_support L M P).toFinset :=
    (xiCoefficient_finite_support L M P).mem_toFinset.mpr h
  exact absurd (Finset.le_max hmem) (not_le_of_gt hn)

/- Additivity of the ξ-coefficient in `P`: the four section maps (inverse right unitor, inverse projection formula
   isomorphism, `coefficientHom`, `coefficientModuleIso`) are additive one by one. Named `xiCoefficient_map_add`: the
   downstream `SubstitutedPolynomialDegreeBridge_XiDegreeAdd` declares the same statement as `xiCoefficient_add` (it
   imports this module, so this module cannot refer to it). -/

theorem xiCoefficient_map_add {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiCoefficient L M (P + P') q = xiCoefficient L M P q + xiCoefficient L M P' q := by
  unfold xiCoefficient AlgebraicGeometry.Scheme.totalSpace.coefficient
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq (P := P + P'),
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq (P := P),
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_eq (P := P')]
  exact (congrArg _ (congrArg _ ((congrArg _ (map_add _ P P')).trans (map_add _ _ _)))).trans
    ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _))

theorem xiCoefficient_sum {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (q : ℕ) {ι : Type*} (s : Finset ι)
    (P : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiCoefficient L M (∑ i ∈ s, P i) q = ∑ i ∈ s, xiCoefficient L M (P i) q :=
  map_sum (AddMonoidHom.mk' (fun P => xiCoefficient L M P q) (fun P P' => xiCoefficient_map_add L M P P' q)) P s

/-- `sectionTensor` is additive in the first variable (`moduleTensorSection_add_left` in the section spelling used here). -/
theorem sectionTensor_add_left {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (s s' : (M.val.obj (Opposite.op ⊤) : Type u)) (t : (M'.val.obj (Opposite.op ⊤) : Type u)) :
    sectionTensor (M := M) (M' := M') (s + s') t = sectionTensor s t + sectionTensor s' t :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorSection_add_left (M := M) (N := M') (U := ⊤) s s' t

/-- `sectionTensor` is additive in the second variable (`moduleTensorSection_add_right`). -/
theorem sectionTensor_add_right {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (t t' : (M'.val.obj (Opposite.op ⊤) : Type u)) :
    sectionTensor (M := M) (M' := M') s (t + t') = sectionTensor s t + sectionTensor s t' :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorSection_add_right (M := M) (N := M') (U := ⊤) s t t'

/-- `xiSectionMul` is additive in the first variable: additivity of `sectionTensor` + additivity of the section maps
of module morphisms. -/
theorem xiSectionMul_add_left {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P Q : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiSectionMul L M M' (P + Q) P' = xiSectionMul L M M' P P' + xiSectionMul L M M' Q P' := by
  unfold xiSectionMul
  rw [sectionTensor_add_left]
  exact map_add _ _ _

/-- `xiSectionMul` is additive in the second variable. -/
theorem xiSectionMul_add_right {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' Q' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiSectionMul L M M' P (P' + Q') = xiSectionMul L M M' P P' + xiSectionMul L M M' P Q' := by
  unfold xiSectionMul
  rw [sectionTensor_add_right]
  exact map_add _ _ _

/-- `xiSectionMul` of a finite sum in the first variable. -/
theorem xiSectionMul_sum_left {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {ι : Type*} (s : Finset ι)
    (P : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiSectionMul L M M' (∑ i ∈ s, P i) P' = ∑ i ∈ s, xiSectionMul L M M' (P i) P' :=
  map_sum (AddMonoidHom.mk' (fun P => xiSectionMul L M M' P P')
    (fun P Q => xiSectionMul_add_left L M M' P Q P')) P s

/-- `xiSectionMul` of a finite sum in the second variable. -/
theorem xiSectionMul_sum_right {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {ι : Type*} (s : Finset ι)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiSectionMul L M M' P (∑ i ∈ s, P' i) = ∑ i ∈ s, xiSectionMul L M M' P (P' i) :=
  map_sum (AddMonoidHom.mk' (fun P' => xiSectionMul L M M' P P')
    (fun P' Q' => xiSectionMul_add_right L M M' P P' Q')) P' s

set_option maxRecDepth 8000 in
/-- **Product of monomials**: `(c·ξ^a)·(c'·ξ^b) = (c ⊗ c')·ξ^{a+b}`, where `c ⊗ c'` is the section of
`(M ⊗ M') ⊗ L^{-(a+b)}` given by `tensorCoefficients`. This is the only non-formal content of the convolution formula
`xiCoefficient_mul`. (`Sym(L^∨)` is a graded algebra: `ξ^a·ξ^b = ξ^{a+b}`.)

Proof (notation: `p : Tot(L) → C̃`, `S := Sym(L^∨)`, `σ := relativeSpec.structureHom S.total`,
`θ_N := projectionFormulaHom p N O_Tot`, `τ_{A,B} := tensorIsoTensorObj A B`, `u_a := Θ_a ≫ ι_a ≫ σ : T_a ⟶ p_*O_Tot`,
`Φ_a := cmi_a⁻¹ ≫ τ_{M,T_a} ≫ (M ◁ u_a) ≫ θ_M ≫ p_*(ρ_) : A_a ⟶ p_*p^*M`, `A_a := (M^1 ⊗ L^{-a})`; by definition
`xiMonomial L M a c = Φ_a.app ⊤ c`):
1. Both sides are the image of `sectionTensor c c'` under a module morphism `tensor A_a A'_b ⟶ p_*p^*(tensor M M')` on
   `C̃`, evaluated at `⊤`: the left side `xiSectionMul (Φ_a c) (Φ'_b c') = pTI⁻¹(Φ_a c ⊗ Φ'_b c')`, and a pure tensor
   `x ⊗ y` on `Tot` (`x`, `y` global sections) is `μ((Φ_a ⊗ₘ Φ'_b)(c ⊗ c'))` through the lax monoidal structure `μ`
   of the pushforward (`pushforwardLaxMonoidal_μ_tensorSections`, `tensorHom_tensorSections`), so the left side is
   `[τ ≫ (Φ_a ⊗ₘ Φ'_b) ≫ μ ≫ p_*(pTI⁻¹)].app ⊤ (sectionTensor c c')`; the right side is
   `[tensorCoefficientsHom ≫ Φ''_{a+b}].app ⊤ (sectionTensor c c')`.
2. The equation of morphisms `τ ≫ (Φ_a ⊗ₘ Φ'_b) ≫ μ ≫ p_*(pTI⁻¹) = tensorCoefficientsHom ≫ Φ''_{a+b}`: after cancelling
   the common prefix `τ ≫ (cmi_a⁻¹ ≫ τ) ⊗ₘ (cmi'_b⁻¹ ≫ τ)` (`tensorHom_comp_tensorHom`), naturality of `θ` in `M` moves
   `τ_{M,M'}⁻¹` to the end where it cancels, leaving the equation on the monoidal `M ⊗ M'`
   `((M ◁ u_a) ≫ θ_M ≫ p_*ρ) ⊗ₘ ((M' ◁ u_b) ≫ θ_{M'} ≫ p_*ρ) ≫ μ ≫ p_*(δ⁻¹) = tensorμ ≫ (𝟙 ⊗ₘ W) ≫ ((M ⊗ M') ◁ u''_{a+b}) ≫ θ_{M⊗M'} ≫ p_*ρ`
   (`W := (pw_a⁻¹ ⊗ pw_b⁻¹) ≫ monoidalPowCat ≫ pw_{a+b}`).
3. Multiplicativity: `(u_a ⊗ₘ u_b) ≫ pushforwardUnitMul p = W ≫ u''_{a+b}`: `σ` is an algebra map
   (`mul_comp_eq_of_isAlgebraMap_mul`, the multiplicative component of `relativeSpecHomEquiv … 𝟙`),
   `(ι_a ⊗ ι_b) ≫ totalMul = S.mul a b ≫ ι_{a+b}` (`tensor_ι_comp_totalMul`),
   `(π_a ⊗ π_b) ≫ symPowMul = monoidalPowCat.hom ≫ π_{a+b}` (`symPowπ_tensor_symPowMul`; `Θ_a = pw_a⁻¹ ≫ π_a`,
   quasi-coherent branch).
4. Compatibility of the projection formula with multiplication (after step 3, the equation of step 2 reduces to this
   one purely monoidal-adjoint compatibility): for `u : T ⟶ p_*O`, `v : T' ⟶ p_*O`,
   `((M ◁ u) ≫ θ ≫ p_*ρ) ⊗ₘ ((M' ◁ v) ≫ θ ≫ p_*ρ) ≫ μ ≫ p_*(δ⁻¹) = tensorμ ≫ ((M ⊗ M') ◁ ((u ⊗ v) ≫ μ_{O,O} ≫ p_*λ)) ≫ θ ≫ p_*ρ`.
   Either transpose along the adjunction and use naturality of `δ` in `D`, associativity and compatibility with
   braidings/unitors (`pullback_μ_*`, `pullback_braided`), or check on pure tensors `(m ⊗ t) ⊗ (m' ⊗ t')` (using the
   four-fold pure tensor criterion for morphisms out of `(A ⊗ B) ⊗ (C ⊗ D)`, from `tensorObj_hom_ext` + local
   generation by pure tensors): both sides are `(u t · v t') • η(m ⊗ m')`
   (`pushforward_rightUnitor_comp_app_projectionFormulaHom_tensorSections`, `pullbackTensorObjHom_app_unit_tensorSections`,
   `tensorSections_smul_left/right`, `associator/braiding_app_tensorSections`). ∎

Edge cases: for `a = 0` or `b = 0`, `W` contains unitors; for `c = 0` both sides are `0`. -/
theorem xiSectionMul_xiMonomial_xiMonomial {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) (a b : ℕ)
    (c : ((((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (c' : ((((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    xiSectionMul L M M' (xiMonomial L M a c) (xiMonomial L M' b c') =
      xiMonomial L (M.tensor M') (a + b) (tensorCoefficients L M M' rfl c c') := by
  have hW0 : (((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a).inv ⊗ₘ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b).inv) ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a b).hom ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b)).hom ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) (rfl : a + b = a + b))) = (((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a).inv ⊗ₘ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b).inv) ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a b).hom ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b)).hom) := by
    rw [CategoryTheory.eqToHom_refl, CategoryTheory.Category.comp_id]
  have hW : ((AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules a ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl a ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) ⊗ₘ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules b ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl b ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ AlgebraicGeometry.Scheme.Modules.pushforwardUnitMul (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom = (((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a).inv ⊗ₘ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b).inv) ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a b).hom ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b)).hom ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) (rfl : a + b = a + b))) ≫ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (a + b) ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (a + b) ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) :=
    (AlgebraicGeometry.Scheme.totalSpace.monomialUnit_mul L.toModules a b).trans (congrArg (fun w => w ≫ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (a + b) ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (a + b) ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) hW0).symm
  have hgen := AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_mul_general (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules) (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules a ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl a ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules b ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl b ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) (((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a).inv ⊗ₘ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b).inv) ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a b).hom ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b)).hom ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) (rfl : a + b = a + b))) (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (a + b) ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (a + b) ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total) hW
  have hmor := CategoryTheory.MonoidalCategory.monomial_mul_bridge (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj ((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules ((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules) (L.coefficientModuleIso M a) (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a)) ((M.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules a ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl a ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom)
    (L.coefficientModuleIso M' b) (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M'.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b)) ((M'.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules b ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl b ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M'.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules)).hom) ((CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules) (self := AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv ≫ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules).inv)) (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules) (((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a).inv ⊗ₘ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b).inv) ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a b).hom ≫ (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b)).hom ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) (rfl : a + b = a + b))) (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.tensor M').toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b))) (L.coefficientModuleIso (M.tensor M') (a + b)) (((M.tensor M').toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (a + b) ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (a + b) ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (M.tensor M').toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.tensor M').toModules)).hom) hgen
  have hL : xiSectionMul L M M' (xiMonomial L M a c) (xiMonomial L M' b c') =
      (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj ((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules ((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules).hom ≫ (((L.coefficientModuleIso M a).inv ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) a)).hom ≫ ((M.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules a ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl a ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom)) ⊗ₘ ((L.coefficientModuleIso M' b).inv ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M'.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) b)).hom ≫ ((M'.toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules b ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl b ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M'.toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules)).hom))) ≫ ((CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules) (self := AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv ≫ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules).inv))).val.app (Opposite.op ⊤)).hom (sectionTensor c c') := by
    rw [xiMonomial_eq_app, xiMonomial_eq_app]
    refine (xiSectionMul_eq_app_tensorSections L M M' _ _).trans ?_
    exact congrArg _ ((AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal_μ_tensorSections
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules)
        ⊤ _ _).symm.trans
      (congrArg _ (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections _ _ ⊤ c c').symm))
  have hR : xiMonomial L (M.tensor M') (a + b) (tensorCoefficients L M M' rfl c c') =
      ((tensorCoefficientsHom L M M' (rfl : a + b = a + b) ≫ ((L.coefficientModuleIso (M.tensor M') (a + b)).inv ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.tensor M').toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (a + b))).hom ≫ (((M.tensor M').toModules ◁ (AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (a + b) ≫ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (a + b) ≫ AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)) ≫ (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (M.tensor M').toModules (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)) ≫ (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.tensor M').toModules)).hom))).val.app (Opposite.op ⊤)).hom (sectionTensor c c') :=
    (xiMonomial_eq_app L (M.tensor M') (a + b) _).trans rfl
  exact hL.trans ((congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom (sectionTensor c c')) hmor).trans hR.symm)

/-- The tensor product of coefficients transported along `h : a + b = q`: `h ▸ tensorCoefficients rfl c c' = tensorCoefficients h c c'`. -/
theorem tensorCoefficients_cast {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (h : a + b = q)
    (c : ((((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (c' : ((((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    (h ▸ tensorCoefficients L M M' rfl c c' :
      (((((M.tensor M').zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) =
      tensorCoefficients L M M' h c c' := by
  subst h
  rfl

/-- ξ-coefficients outside the support vanish. -/
theorem xiCoefficient_eq_zero_of_not_mem {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) {a : ℕ}
    (ha : a ∉ (xiCoefficient_finite_support L M P).toFinset) : xiCoefficient L M P a = 0 := by
  by_contra h
  exact ha ((xiCoefficient_finite_support L M P).mem_toFinset.mpr h)

/-- **The ξ-coefficients of a product are given by convolution**: `(P·P')_q = Σ_{a+b=q} c_a ⊗ c'_b`.
(Expanding a substituted polynomial in `ξ`; `Sym(L^∨)` is a graded algebra, `ξ^a·ξ^b = ξ^{a+b}`.)

Proof (assembled from `xiSectionMul_xiMonomial_xiMonomial`):
`P = Σ_{a∈F} c_a ξ^a`, `P' = Σ_{b∈F'} c'_b ξ^b` (`eq_sum_xiMonomial`, `F`, `F'` the supports), `xiSectionMul` is
biadditive (`xiSectionMul_sum_left/right`), the product of monomials is `(c_a ξ^a)(c'_b ξ^b) = (c_a ⊗ c'_b) ξ^{a+b}`,
and then take the `q`-th coefficient (`xiCoefficient_sum`, `xiCoefficient_xiMonomial`: `c_a ⊗ c'_b` for `a + b = q`,
otherwise `0`). Finally the sums over `F ×ˢ F'` and over `antidiagonal q` are both reduced to the sum over their
intersection (`Finset.sum_subset`: the terms outside `F ×ˢ F'` vanish by `xiCoefficient_eq_zero_of_not_mem` and
`tensorCoefficients_zero_left/right`, the terms outside the antidiagonal by `dif_neg`), and `Finset.sum_attach`
converts back to the `attach` form. -/
theorem xiCoefficient_mul {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) (q : ℕ) :
    xiCoefficient L (M.tensor M') (xiSectionMul L M M' P P') q
      = ∑ ab ∈ (Finset.HasAntidiagonal.antidiagonal q).attach,
          tensorCoefficients L M M' (Finset.HasAntidiagonal.mem_antidiagonal.mp ab.2)
            (xiCoefficient L M P ab.1.1) (xiCoefficient L M' P' ab.1.2) := by
  -- G ab := the (a, b)-term, as a function of ab : ℕ × ℕ (0 unless a + b = q)
  set G : ℕ × ℕ → (((((M.tensor M').zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj
      (Opposite.op ⊤)) : Type u) := fun ab =>
    if h : ab.1 + ab.2 = q then tensorCoefficients L M M' h (xiCoefficient L M P ab.1) (xiCoefficient L M' P' ab.2)
    else 0 with hG
  set F := (xiCoefficient_finite_support L M P).toFinset with hF
  set F' := (xiCoefficient_finite_support L M' P').toFinset with hF'
  have hP := eq_sum_xiMonomial L M P
  have hP' := eq_sum_xiMonomial L M' P'
  -- expand P and P' (only in the `xiSectionMul` arguments)
  have h1 : xiCoefficient L (M.tensor M') (xiSectionMul L M M' P P') q =
      ∑ a ∈ F, ∑ b ∈ F', G (a, b) := by
    refine (congrArg (fun Q => xiCoefficient L (M.tensor M') Q q)
      (congrArg₂ (fun P₀ P₀' => xiSectionMul L M M' P₀ P₀') hP hP')).trans ?_
    rw [xiSectionMul_sum_left, xiCoefficient_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [xiSectionMul_sum_right, xiCoefficient_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [xiSectionMul_xiMonomial_xiMonomial, xiCoefficient_xiMonomial]
    simp only [hG]
    split_ifs with h
    · exact tensorCoefficients_cast L M M' h _ _
    · rfl
  rw [h1, ← Finset.sum_product' F F' (fun a b => G (a, b))]
  -- both sums equal the sum over the intersection
  have hzero_outside_anti : ∀ ab : ℕ × ℕ, ab ∉ Finset.HasAntidiagonal.antidiagonal q → G ab = 0 := by
    intro ab hab
    have : ¬ ab.1 + ab.2 = q := fun h => hab (Finset.HasAntidiagonal.mem_antidiagonal.mpr h)
    simp only [hG, dif_neg this]
  have hzero_outside_prod : ∀ ab : ℕ × ℕ, ab ∉ F ×ˢ F' → G ab = 0 := by
    intro ab hab
    simp only [hG]
    split_ifs with h
    · rw [Finset.mem_product, not_and_or] at hab
      rcases hab with ha | hb
      · rw [xiCoefficient_eq_zero_of_not_mem L M P ha]
        exact tensorCoefficients_zero_left L M M' h _
      · rw [xiCoefficient_eq_zero_of_not_mem L M' P' hb]
        exact tensorCoefficients_zero_right L M M' h _
    · rfl
  have hL : ∑ ab ∈ F ×ˢ F', G ab = ∑ ab ∈ (F ×ˢ F') ∩ Finset.HasAntidiagonal.antidiagonal q, G ab :=
    (Finset.sum_subset Finset.inter_subset_left fun ab hab hab' =>
      hzero_outside_anti ab fun h => hab' (Finset.mem_inter.mpr ⟨hab, h⟩)).symm
  have hR : ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal q, G ab =
      ∑ ab ∈ (F ×ˢ F') ∩ Finset.HasAntidiagonal.antidiagonal q, G ab :=
    (Finset.sum_subset Finset.inter_subset_right fun ab hab hab' =>
      hzero_outside_prod ab fun h => hab' (Finset.mem_inter.mpr ⟨h, hab⟩)).symm
  rw [hL, ← hR, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal q) G]
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp only [hG, dif_pos (Finset.HasAntidiagonal.mem_antidiagonal.mp ab.2)]

/-- **The ξ-degree of a product is subadditive**: `xiDegree (P·P') ≤ xiDegree P + xiDegree P'` (degrees add when a
substituted polynomial is expanded in `ξ`).

Proof: by `Finset.max_le` it suffices that every index `a` of a nonzero coefficient of the product satisfies
`a ≤ d + d'` (`d = xiDegree P`, `d' = xiDegree P'`, in `WithBot ℕ`). Suppose `a > d + d'`; by the convolution formula
`xiCoefficient_mul` the `a`-th coefficient is `Σ_{i+j=a} tensorCoefficients (c_i) (c'_j)`. For each `(i, j)`: if
`i ≤ d` and `j ≤ d'` then `a = i + j ≤ d + d'` (`add_le_add`), a contradiction; so `i > d` or `j > d'`, hence
`c_i = 0` or `c'_j = 0` (`xiCoefficient_eq_zero_of_xiDegree_lt`) and the term is `0`
(`tensorCoefficients_zero_left / _right`). The whole sum is `0`, contradicting "the `a`-th coefficient is nonzero". ∎ -/
theorem xiDegree_mul_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiDegree L (M.tensor M') (xiSectionMul L M M' P P') ≤ xiDegree L M P + xiDegree L M' P' := by
  unfold xiDegree
  apply Finset.max_le
  intro a ha
  have hne : xiCoefficient L (M.tensor M') (xiSectionMul L M M' P P') a ≠ 0 :=
    (xiCoefficient_finite_support L (M.tensor M') (xiSectionMul L M M' P P')).mem_toFinset.mp ha
  by_contra hlt
  rw [not_le] at hlt
  apply hne
  rw [xiCoefficient_mul]
  apply Finset.sum_eq_zero
  intro ab _
  have hab : ab.1.1 + ab.1.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.mp ab.2
  by_cases hi : xiDegree L M P < (ab.1.1 : WithBot ℕ)
  · rw [xiCoefficient_eq_zero_of_xiDegree_lt L M P hi]
    exact tensorCoefficients_zero_left L M M' _ _
  · by_cases hj : xiDegree L M' P' < (ab.1.2 : WithBot ℕ)
    · rw [xiCoefficient_eq_zero_of_xiDegree_lt L M' P' hj]
      exact tensorCoefficients_zero_right L M M' _ _
    · exfalso
      rw [not_lt] at hi hj
      have : (a : WithBot ℕ) ≤ xiDegree L M P + xiDegree L M' P' := by
        rw [← hab]
        push_cast
        exact add_le_add hi hj
      exact absurd this (not_le_of_gt hlt)

/- `σ₀^*p^*M ≅ M` (`σ₀ ≫ p = 𝟙`: `pullbackComp`, `zeroSection_comp`, `pullbackId`); `(M.zpow 1) ⊗ L^{0} ≅ M`
   (`zpowOneIso`, `L.zpow 0 = O_X` and the right unitor). Pullback along the zero section = the 0-th coefficient, both
   transported to `Γ(C̃, M)` for comparison. -/

noncomputable def zeroSectionPullbackIso {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.zeroSection L.toModules)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ≅ M.toModules :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.zeroSection L.toModules)
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app M.toModules ≪≫
    CategoryTheory.eqToIso (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M.toModules)
      (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackId C.toScheme).app M.toModules

noncomputable def coefficientZeroIso {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) :
    ((M.zpow 1).tensor (L.zpow (-((0 : ℕ) : ℤ)))).toModules ≅ M.toModules :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
    CategoryTheory.MonoidalCategory.tensorIso M.zpowOneIso (CategoryTheory.Iso.refl _) ≪≫
    CategoryTheory.MonoidalCategory.rightUnitor M.toModules

/-- `zeroSectionPullbackIso` applied to `σ₀^*P` is `Scheme.restrictToZeroSection` (`TotalSpaceRestrictToZeroSection`;
the two differ only in the spelling of `eqToIso` and `pullbackCongr`, by proof irrelevance). -/
theorem zeroSectionPullbackIso_hom_app_eq_restrictToZeroSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    ((zeroSectionPullbackIso L M).hom.val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules) P)
      = AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules P := by
  have e : ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)).app M.toModules).hom =
      CategoryTheory.eqToHom (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M.toModules)
        (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)) :=
    CategoryTheory.eqToHom_app _ _
  exact (congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.zeroSection L.toModules ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)).obj M.toModules ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.CategoryStruct.id C.toScheme)).obj M.toModules =>
    ((((AlgebraicGeometry.Scheme.Modules.pullbackId C.toScheme).app M.toModules).hom.val.app (Opposite.op ⊤)).hom
      ((φ.val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.zeroSection L.toModules)
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app M.toModules).hom.val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules) P))))) e).symm

/- Restriction along the zero section is additive on sections: the section maps of the adjunction unit and of the
   isomorphism preserve addition. -/

theorem AlgebraicGeometry.Scheme.restrictToZeroSection_add {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {M : X.Modules}
    (a b : (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace V).hom).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V (a + b) =
      AlgebraicGeometry.Scheme.restrictToZeroSection V a + AlgebraicGeometry.Scheme.restrictToZeroSection V b := by
  exact AlgebraicGeometry.Scheme.restrictToZeroSection_map_add V a b

theorem AlgebraicGeometry.Scheme.restrictToZeroSection_sum {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {M : X.Modules} {ι : Type*} (s : Finset ι)
    (a : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace V).hom).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V (∑ i ∈ s, a i) =
      ∑ i ∈ s, AlgebraicGeometry.Scheme.restrictToZeroSection V (a i) :=
  AlgebraicGeometry.Scheme.restrictToZeroSection_map_sum V s a

/-- **`p^*s` restricts back to `s` along the zero section**: `σ₀^*(p^*s)` returns to `s` through `pullbackComp`,
`pullbackCongr`, `pullbackId`.

Proof: `ModuleSections.pullback_comp` (`σ₀^*p^* = (σ₀ ≫ p)^*`), `pullbackCongr_apply` (`σ₀ ≫ p = 𝟙`), then
`conjugateEquiv_pullbackId_hom` (compatibility of `pullbackId` with the unit) give `(𝟙)^*s ↦ s`.
(The same proof as the private lemma `realization_zero_restrict_direct` of `RealizationGeometricBack`, public here.) -/
theorem AlgebraicGeometry.Scheme.restrictToZeroSection_sectionPullbackAlong {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (M : X.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace V).hom s) = s := by
  exact AlgebraicGeometry.Scheme.restrictToZeroSection_sectionPullbackAlong_general V M s

/-- **The degree-0 monomial is a pullback along `p`**: `xiMonomial L M 0 c = p^*(coefficientZeroIso.hom c)` (the
constant term `π_L^*(ρ^*f_ℓ)` of the expansion).

Proof (at the level of morphisms; the auxiliary lemmas are in `TotLineMonomialZeroUnit`):
1. The equation of morphisms `coefficientZeroIso⁻¹ ≫ (coefficientModuleIso 0)⁻¹ ≫ monomialHom 0 ≫ θ ≫ p_*(ρ_{p^*M}) = unit_M`
   (`Modules.monomialZero_iso_cancel_bridge`: after cancelling the coefficient isomorphisms at `q = 0` what remains is
   `(ρ_ M)⁻¹ ≫ (M ◁ (Θ_0 ≫ ι_0 ≫ σ)) ≫ θ ≫ p_*(ρ_)`;
   `totalSpace.whiskerLeft_monomialUnit_zero_projectionFormulaHom_map_rightUnitor`: `Θ_0 ≫ ι_0 ≫ σ = T(η)` is the
   adjoint transpose, and `(M ◁ T(η)) ≫ θ ≫ p_*(ρ_) = ρ_ ≫ unit` (abstract lemma for monoidal adjunctions)).
2. Take `⊤`-sections: the right side is `sectionPullbackAlong p s` (the adjunction unit, `sectionPullbackAlong_eq_unit_val_app`),
   the left side is by definition `xiMonomial L M 0 (coefficientZeroIso.inv s)`; take `s := coefficientZeroIso.hom c` and
   use `app_top_hom_inv`.
(`sectionPullbackAlong_totalSpace_eq_xiMonomial_zero` of `ConeCoordinateFiniteXiExpansionConstantMonomial` and this
statement are one line apart; this one is upstream.) -/
theorem xiMonomial_zero_eq_sectionPullbackAlong {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (c : ((((M.zpow 1).tensor (L.zpow (-((0 : ℕ) : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    xiMonomial L M 0 c =
      sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        (((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom c) := by
  have hmor : (coefficientZeroIso L M).inv ≫ (L.coefficientModuleIso M 0).inv ≫
        AlgebraicGeometry.Scheme.totalSpace.monomialHom L.toModules M.toModules 0 ≫
        AlgebraicGeometry.Scheme.Modules.projectionFormulaHom
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map
          (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).unit.app M.toModules :=
    AlgebraicGeometry.Scheme.Modules.monomialZero_iso_cancel_bridge (ρ_ M.toModules)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.zpow 1).toModules
        (L.zpow (-((0 : ℕ) : ℤ))).toModules)
      M.zpowOneIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
        (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules 0))
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0))
      (L.zpowNegIso 0) rfl rfl _ _ _ _
      (AlgebraicGeometry.Scheme.totalSpace.whiskerLeft_monomialUnit_zero_projectionFormulaHom_map_rightUnitor
        L.toModules M.toModules)
  have hW : ∀ s : (M.toModules.val.obj (Opposite.op ⊤) : Type u),
      sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom s =
        xiMonomial L M 0 (((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom s) := by
    intro s
    rw [AlgebraicGeometry.Scheme.sectionPullbackAlong_eq_unit_val_app, ← hmor,
      AlgebraicGeometry.Scheme.Modules.app_top_comp, AlgebraicGeometry.Scheme.Modules.app_top_comp,
      AlgebraicGeometry.Scheme.Modules.app_top_comp, AlgebraicGeometry.Scheme.Modules.app_top_comp,
      AlgebraicGeometry.Scheme.Modules.pushforward_map_val_app_top, xiMonomial_eq_app]
    rfl
  rw [hW, AlgebraicGeometry.Scheme.Modules.app_top_hom_inv]

/-- **The degree-0 monomial restricts along the zero section to its coefficient**: from
`xiMonomial_zero_eq_sectionPullbackAlong` and `restrictToZeroSection_sectionPullbackAlong`. -/
theorem restrictToZeroSection_xiMonomial_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (c : ((((M.zpow 1).tensor (L.zpow (-((0 : ℕ) : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (xiMonomial L M 0 c) =
      ((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom c := by
  exact (congrArg (AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules)
    (xiMonomial_zero_eq_sectionPullbackAlong L M c)).trans
    (AlgebraicGeometry.Scheme.restrictToZeroSection_sectionPullbackAlong L.toModules M.toModules _)

/-- **Positive-degree monomials vanish on the zero section**: for `q ≥ 1`, `restrictToZeroSection L (xiMonomial L M q c) = 0`.
This is what `realization_xi_zero_restrict` (`RealizationGeometricBack`) actually uses. (`P|_{ξ=0} = ρ^*f`: `ξ` is `0`
on the zero section.)

Proof: `xiMonomial L M q c = totalSpace.monomial L M q (coefficientModuleIso⁻¹ c)`, and
`totalSpace.restrictToZeroSection_monomial_pos` (`TotLineMonomialZeroSection`, for line bundles on any scheme): at the
level of morphisms `(M ◁ (Θ_q ≫ ι_q ≫ σ)) ≫ θ ≫ p_*((ρ_ p^*M).hom ≫ R) = 0` (`R` = the restriction morphism along the zero
section), checked on pure tensors `m ⊗ t` by `tensorObj_hom_ext`: the value is `σ₀^♯(σ(ι_q(Θ_q t))) • R(p^*m)`, and
`σ₀^♯ ∘ σ = ε` is the augmentation (universal property of the relative Spec `relativeSpecHomEquiv.apply_symm_apply`,
Stacks 01LQ), with `ι_q ≫ ε = 0` (`q ≥ 1`), so it is `0`. -/
theorem restrictToZeroSection_xiMonomial_pos {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) {q : ℕ} (hq : 0 < q)
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (xiMonomial L M q c) = 0 := by
  unfold xiMonomial
  exact AlgebraicGeometry.Scheme.totalSpace.restrictToZeroSection_monomial_pos L.toModules M.toModules hq _

/-- **Pullback along the zero section = the 0-th ξ-coefficient** (both sides transported to `Γ(C̃, M)` through
`coefficientZeroIso` and `zeroSectionPullbackIso`). (`P|_{ξ=0} = ρ^*f`, the degree-0 term.)

Proof (assembled from `xiMonomial_zero_eq_sectionPullbackAlong` and `restrictToZeroSection_xiMonomial_pos`):
the right side is `restrictToZeroSection L P` by `zeroSectionPullbackIso_hom_app_eq_restrictToZeroSection`.
`P = Σ_q xiMonomial q c_q` (`eq_sum_xiMonomial`), both sides are additive group homomorphisms (`xiCoefficient_sum`,
`restrictToZeroSection_sum`, `map_sum` for the section map of `coefficientZeroIso`), so compare monomial by monomial:
for `q = 0` the left side is `c_0` (`xiCoefficient_xiMonomial`) and so is the right side
(`restrictToZeroSection_xiMonomial_zero`); for `q ≥ 1` the left side `xiCoefficient (xiMonomial q c) 0 = 0`
(`xiCoefficient_xiMonomial`, `dif_neg`) and the right side is `0` by `restrictToZeroSection_xiMonomial_pos`. -/
theorem xiCoefficient_zero_eq_zeroSection {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    ((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom (xiCoefficient L M P 0)
      = ((zeroSectionPullbackIso L M).hom.val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules) P) := by
  rw [zeroSectionPullbackIso_hom_app_eq_restrictToZeroSection]
  have key : ∀ (s : Finset ℕ)
      (c : ∀ q : ℕ, ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)),
      ((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom
          (xiCoefficient L M (∑ q ∈ s, xiMonomial L M q (c q)) 0)
        = AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (∑ q ∈ s, xiMonomial L M q (c q)) := by
    intro s c
    rw [xiCoefficient_sum, AlgebraicGeometry.Scheme.restrictToZeroSection_sum]
    refine (map_sum ((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom _ s).trans ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rw [restrictToZeroSection_xiMonomial_zero, xiCoefficient_xiMonomial]
      rfl
    · rw [restrictToZeroSection_xiMonomial_pos L M hq, xiCoefficient_xiMonomial, dif_neg hq.ne']
      exact map_zero _
  have h := key (xiCoefficient_finite_support L M P).toFinset (fun q => xiCoefficient L M P q)
  rw [← eq_sum_xiMonomial L M P] at h
  exact h

/-- **On an affine open with a frame, `Γ(p⁻¹V, O_Tot) ≅ O(V)[t]`** (an `O(V)`-algebra isomorphism; `ξ = t·ε`).
(In the paper: `C̃_(k)(L)` is locally `O(V)[t]/(t^{k+1})`; the `Tot` version drops the truncation.)

Proof sketch:
1. `Γ(p⁻¹V, O_Tot) = Γ(V, p_*O_Tot) ≅ Γ(V, ⊕_m S_m)` (`σ⁻¹`, `relativeSpec.structureIso`; as `O(V)`-algebras, `σ` being
   an algebra homomorphism).
2. `V` is affine hence quasi-compact and the `S_m` are quasi-coherent: `Γ(V, ⊕_m S_m) = ⊕_m Γ(V, S_m)`.
3. The frame `ε ∈ Γ(V, L)` is nowhere zero and gives `L|_V ≅ O_V`; the dual frame `t := ε^∨ ∈ Γ(V, L^∨)` gives
   `L^∨|_V ≅ O_V`, so `Γ(V, S_m) = Γ(V, Sym^m L^∨) = Γ(V, (L^∨)^{⊗m}) ≅ O(V)·t^m` (`symPowπ` is an isomorphism on a line
   bundle).
4. Multiplication: the graded multiplication of `Sym` is `t^a ⊗ t^b ↦ t^{a+b}`, so `⊕_m O(V)·t^m ≅ O(V)[t]` (the
   `AlgEquiv` of `Polynomial`, from bijectivity of `Polynomial.aeval t`). ∎

As formalized: `relativeSpec.sectionsAlgEquiv A ⟨V, hV⟩ : A.sectionsRing V ≃ₐ[Γ(V)] Γ(Spec_X A, π⁻¹V)` identifies the
right-hand algebra structure with `(p.app V).hom.toAlgebra`, and `totalSpace_exists_coordinate_of_isFrame`
(`…FrameCoordinateMonomialRingEquivCoordinate`) gives, under the same `letI` algebra structure, an `x ∈ Γ(p⁻¹V, O_Tot)`
such that `Polynomial.aeval x : Γ(V)[t] →ₐ[Γ(V)] Γ(p⁻¹V, O_Tot)` is bijective (with `τ₀(ξ|_{p⁻¹V}) = x`, i.e. `ξ = t·ε`);
this theorem is the inverse of the `AlgEquiv.ofBijective` of that bijection, the frame condition being obtained from the
`generates` field of `L.Frame V` through `LineBundle.Frame.isFrame`. Users needing the compatibility `ξ ↦ t·ε` should use
`totalSpace_exists_coordinate_of_isFrame` directly. -/
theorem totLine_sections_over_frame {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (V : C.toScheme.Opens) (hV : AlgebraicGeometry.IsAffineOpen V)
    (ε : L.Frame V) :
    /- `Γ(C̃, V) → Γ(Tot(L), p⁻¹V)` is the pullback of `p` on `V` (the natural algebra structure). -/
    letI : Algebra Γ(C.toScheme, V)
        Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) :=
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom.toAlgebra
    Nonempty (Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)
      ≃ₐ[Γ(C.toScheme, V)] Polynomial Γ(C.toScheme, V)) := by
  let _ : Algebra Γ(C.toScheme, V)
      Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) :=
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.app V).hom.toAlgebra
  obtain ⟨x, -, hx, -⟩ := totalSpace_exists_coordinate_of_isFrame L V hV ε.section_ ε.isFrame
  exact ⟨(AlgEquiv.ofBijective _ hx).symm⟩

end
