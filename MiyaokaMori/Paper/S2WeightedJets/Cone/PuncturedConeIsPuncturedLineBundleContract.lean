import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProduct
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S2WeightedJets.Cone.TautologicalBundleOnVariety
import MiyaokaMori.AlgebraicGeometry.Modules.TotLinePunctured
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # The pairing `⟨·,·⟩ : L ⊗ pr₂^*O_X(1) → pr₁^*A` and the two characterising properties

The pairing `⟨·,·⟩ : L ⊗ pr₂^*O_X(1) → pr₁^*A` (`L = pr₁^*A ⊗ pr₂^*O_X(−1)` on `C ×_k X`) and its version
on sections over a `T`-point; the universal data needed to compare `Z^×` with `Tot(L)^×`
(`Tot(L)^× → C × X`, the tautological section, the coordinates of `Z^×` over `C × X`); and the two
characterising properties `IsConeToTotalSpaceHom` / `IsTotalSpaceToConeHom`.
The pairing is compatible with pullback (`contractSections_pullback`).

Source: eq. (2.1) of the paper (`t^*A ⊗ x^*O_X(−1) = Hom(x^*O_X(1), t^*A)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

/-- The evaluation `ev : pr₂^*O_X(−1) ⊗ pr₂^*O_X(1) → O_{C×X}`: pullback commutes with `⊗` (Stacks 01CD,
`pullbackTensorObjIso`), followed by the pullback of the internal-Hom evaluation
`𝓗om(O_X(1), O_X) ⊗ O_X(1) → O_X` (`O_X(−1) = moduleSheafDual` is built by the same construction as
`internalHom _ O_X`), followed by `pr₂^*O_X ≅ O_{C×X}` (`pullbackUnitIso`). -/
noncomputable def conePuncturedLineBundle.eval {k : Type u} [Field k] (C : AlgebraicGeometry.Scheme.{u})
    {X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ} (e : ProjectiveEmbedding k X N) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (AlgebraicGeometry.Scheme.Modules.moduleSheafDual (e.oX 1)) ⊗
      (AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1)) ⟶
      SheafOfModules.unit (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (AlgebraicGeometry.Scheme.Modules.moduleSheafDual (e.oX 1))
      (e.oX 1)).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).map
      (AlgebraicGeometry.Scheme.Modules.internalHomEval (e.oX 1)
        (SheafOfModules.unit X.ringCatSheaf)) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom

/-- The pairing `⟨·,·⟩ : L ⊗ pr₂^*O_X(1) → pr₁^*A` (`L = conePuncturedLineBundle e A = pr₁^*A ⊗ pr₂^*O_X(−1)`):
`Modules.tensor ≅ ⊗` (`tensorIsoTensorObj`), the associator, the evaluation `conePuncturedLineBundle.eval`
on the second factor, and the right unitor.
It realizes `L` as `𝓗om(pr₂^*O_X(1), pr₁^*A)`: for line bundles, `M ⊗ Q^∨ ≅ 𝓗om(Q, M)`. -/
noncomputable def conePuncturedLineBundle.contract {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] :
    (conePuncturedLineBundle e A ⊗
      (AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1)) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A :=
  ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (AlgebraicGeometry.Scheme.Modules.moduleSheafDual (e.oX 1)))).hom ▷ _) ≫
    (α_ _ _ _).hom ≫ (_ ◁ conePuncturedLineBundle.eval C e) ≫ (ρ_ _).hom

/-- The pairing on a `T`-point: for a scheme `T` over `C ×_k X`, `w ∈ Γ(T, T.hom^*L)` and
`q ∈ Γ(T, T.hom^*pr₂^*O_X(1))`, `⟨w, q⟩ ∈ Γ(T, T.hom^*pr₁^*A)`: take `sectionTensor`, pass through
`Modules.tensor ≅ ⊗` and "pullback commutes with `⊗`" into `T.hom^*(L ⊗ pr₂^*O_X(1))`, then apply the
pullback of the pairing `contract`. -/
noncomputable def conePuncturedLineBundle.contractSections {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle]
    (T : CategoryTheory.Over (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    (w : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)).val.obj
      (Opposite.op ⊤) : Type u))
    (q : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)).val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (conePuncturedLineBundle.contract e A)).app ⊤
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom _ _).inv.app ⊤
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom.app ⊤ (sectionTensor w q)))

/-- The `i`-th homogeneous coordinate section `pr₂^*(e^*x_i)` of `pr₂^*O_X(1)` on `C ×_k X`, where
`e^*x_i = sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i) : Γ(e.oX 1, ⊤)` and
`e.oX 1 := (pullback e.emb).obj (projectiveSpaceTwist k N 1)`. -/
noncomputable def conePuncturedLineBundle.coordinate {k : Type u} [Field k] (C : AlgebraicGeometry.Scheme.{u})
    {X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ} (e : ProjectiveEmbedding k X N)
    (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1)).val.obj (Opposite.op ⊤) : Type u) :=
  sectionPullbackAlong
    (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i))

/-- The structure morphism `Tot(V)^× ↪ Tot(V) → X` of the punctured total space. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpacePunctured.toBase {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    (AlgebraicGeometry.Scheme.totalSpacePunctured V).toScheme ⟶ X :=
  (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom

/-- The tautological section on `Tot(V)^×`, in `Γ(Tot(V)^×, toBase^*V)`: the section corresponding under
`totalSpaceHomEquiv` to the open immersion `Tot(V)^× ↪ Tot(V)` (as a morphism over `X`). -/
noncomputable def AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase V)).obj V).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.totalSpaceHomEquiv V
    (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase V))
    (CategoryTheory.Over.homMk (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι rfl)

/-- `Z^× → C ×_k X` followed by `pr₁` is the base map `t`. -/
theorem puncturedConeToProduct.comp_fst {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    puncturedConeToProduct e E A hdeg ≫
        CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      puncturedConeToProduct.base e E A hdeg := by
  unfold puncturedConeToProduct
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

/-- The `i`-th coordinate `z_i` of `Z^×`, transported to `Γ(Z^×, g^*pr₁^*A)` (`g = Z^× → C ×_k X`):
`puncturedConeToProduct.coord` transported along `t = g ≫ pr₁` (`comp_fst`) and `pullbackComp`. -/
noncomputable def puncturedConeToProduct.coordOverProduct {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct e E A hdeg)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)).val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp (puncturedConeToProduct e E A hdeg)
      (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).inv.app A).app ⊤
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (puncturedConeToProduct.comp_fst e E A hdeg).symm).hom.app A).app ⊤
      (puncturedConeToProduct.coord e E A hdeg i))

/-- The characterising property (forward direction): `α : Z^× → Tot(L)^×` lies over `C ×_k X`, and its
corresponding section `w_α ∈ Γ(Z^×, g^*L)` satisfies `⟨w_α, g^*pr₂^*(e^*x_i)⟩ = z_i` (`i = 0, …, N`) —
i.e. `w_α` is the isomorphism `θ : Φ^*O_X(1) ≅ t^*A` sending `x^*x_i` to `z_i`. -/
def IsConeToTotalSpaceHom {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    (α : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶
      (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme) : Prop :=
  ∃ hα : α ≫ AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A) =
      puncturedConeToProduct e E A hdeg,
    ∀ i : Fin (N + 1),
      conePuncturedLineBundle.contractSections e A (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg))
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (conePuncturedLineBundle e A)
          (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg))
          (CategoryTheory.Over.homMk
            (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι)
            (by rw [CategoryTheory.Category.assoc]; exact hα)))
        (sectionPullbackAlong (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle.coordinate C e i)) =
      puncturedConeToProduct.coordOverProduct e E A hdeg i

/-- The characterising property (backward direction): `β : Tot(L)^× → Z^×` lies over `C ×_k X`, and the
pulled-back coordinates `β^*z_i` (transported to `Γ(Tot(L)^×, π^*pr₁^*A)`) equal the pairing of the
tautological section with `π^*pr₂^*(e^*x_i)` — i.e. `z_i = θ_w(x^*x_i)`. -/
def IsTotalSpaceToConeHom {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    (β : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶
      (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme) : Prop :=
  ∃ hβ : β ≫ puncturedConeToProduct e E A hdeg =
      AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A),
    ∀ i : Fin (N + 1),
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hβ).hom.app _).app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp β (puncturedConeToProduct e E A hdeg)).hom.app _).app ⊤
          (sectionPullbackAlong β (puncturedConeToProduct.coordOverProduct e E A hdeg i))) =
      conePuncturedLineBundle.contractSections e A
        (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)))
        (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection (conePuncturedLineBundle e A))
        (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
          (conePuncturedLineBundle.coordinate C e i))

/-! ## Transport lemmas for `contractSections_pullback` (stated for arbitrary schemes and modules, so that the
defeq cost is paid once) -/

section PullbackHelpers

variable {X₀ Y₀ Z₀ : AlgebraicGeometry.Scheme.{u}}

/-- Pulling a section back along `j` commutes with morphisms of sheaves of modules (`Hom.app` form; the
naturality of the adjunction unit). -/
private theorem sectionPullbackAlong_app (j : X₀ ⟶ Y₀) {M M' : Y₀.Modules} (φ : M ⟶ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong j (φ.app ⊤ s) =
      ((AlgebraicGeometry.Scheme.Modules.pullback j).map φ).app ⊤ (sectionPullbackAlong j s) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality φ
  exact congrArg (fun ψ => AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤ s) h

/-- Naturality of `pullbackComp` on global sections: `c_N (j^*g^*φ z) = (j ≫ g)^*φ (c_M z)`. -/
private theorem pullbackComp_hom_app_app_map (j : X₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀) {M N : Z₀.Modules}
    (φ : M ⟶ N)
    (z : ((((AlgebraicGeometry.Scheme.Modules.pullback j).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).val.obj (Opposite.op ⊤)) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app N).app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullback j).map
          ((AlgebraicGeometry.Scheme.Modules.pullback g).map φ)).app ⊤ z) =
      ((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ g)).map φ).app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app M).app ⊤ z) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.naturality φ
  exact congrArg (fun ψ => AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤ z) h

private theorem iso_inv_app_hom_app {M N : X₀.Modules} (α : M ≅ N)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) : α.inv.app ⊤ (α.hom.app ⊤ x) = x :=
  congrArg (fun ψ => AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤ x) α.hom_inv_id

private theorem iso_hom_app_inv_app {M N : X₀.Modules} (α : M ≅ N)
    (y : (N.val.obj (Opposite.op ⊤) : Type u)) : α.hom.app ⊤ (α.inv.app ⊤ y) = y :=
  congrArg (fun ψ => AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤ y) α.inv_hom_id

/-- The core transport: `pullbackComp` and `pullbackTensorObjIso.inv` are compatible on tensors of sections,
`c_{M⊗N} (j^*(κ_g (w ⊗ q))) = κ_{j≫g} (c_M (j^*w) ⊗ c_N (j^*q))`.
Proof: apply `δ_{j≫g}` to both sides (`pullbackTensorObjIso` is `asIso δ`), then use
`pullbackComp_hom_app_pullbackTensorObjHom`, `δ_g ∘ κ_g = id`, `pullbackTensorObjHom_app_unit_tensorSections`
and `tensorHom_tensorSections`. -/
private theorem pullbackComp_pullbackTensorObjIso_inv_tensorSections (j : X₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀)
    (M N : Z₀.Modules)
    (w : ((((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj (Opposite.op ⊤)) : Type u))
    (q : ((((AlgebraicGeometry.Scheme.Modules.pullback g).obj N).val.obj (Opposite.op ⊤)) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app
        (CategoryTheory.MonoidalCategoryStruct.tensorObj M N)).app ⊤
      (sectionPullbackAlong j
        ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g M N).inv.app ⊤
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ w q))) =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (j ≫ g) M N).inv.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤
          (((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app M).app ⊤ (sectionPullbackAlong j w))
          (((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app N).app ⊤
            (sectionPullbackAlong j q))) := by
  refine (iso_inv_app_hom_app (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (j ≫ g) M N) _).symm.trans
    (congrArg ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso (j ≫ g) M N).inv.app ⊤) ?_)
  have hT := AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackTensorObjHom j g M N
  refine (congrArg (fun ψ => AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤
    (sectionPullbackAlong j
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g M N).inv.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ w q)))) hT).trans ?_
  show (CategoryTheory.MonoidalCategoryStruct.tensorHom
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app M)
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app N)).app ⊤
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom j _ _).app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullback j).map
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N)).app ⊤
        (sectionPullbackAlong j
          ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g M N).inv.app ⊤
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ w q))))) = _
  have hB : ((AlgebraicGeometry.Scheme.Modules.pullback j).map
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N)).app ⊤
        (sectionPullbackAlong j
          ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g M N).inv.app ⊤
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ w q))) =
      sectionPullbackAlong j (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ w q) :=
    (sectionPullbackAlong_app j (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N) _).symm.trans
      (congrArg (sectionPullbackAlong j)
        (iso_hom_app_inv_app (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g M N)
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ w q)))
  refine (congrArg (fun z => (CategoryTheory.MonoidalCategoryStruct.tensorHom
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app M)
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app N)).app ⊤
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom j _ _).app ⊤ z)) hB).trans ?_
  have hδ := AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_unit_tensorSections j
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N) ⊤ w q
  refine (congrArg ((CategoryTheory.MonoidalCategoryStruct.tensorHom
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app M)
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app N)).app ⊤) hδ).trans ?_
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app M)
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j g).hom.app N) ⊤
    (sectionPullbackAlong j w) (sectionPullbackAlong j q)

end PullbackHelpers

/-- The pairing is compatible with pullback: for `T` over `C ×_k X` and `j : S → T`,
`j^*⟨w, q⟩ = ⟨j^*w, j^*q⟩` (both sides transported to `(j ≫ T.hom)^*` through `pullbackComp`).

Source: Stacks 01CD (pullback is a monoidal functor), and the pairing `contract` is a fixed morphism of
sheaves of modules on `C ×_k X`.

Proof: `contractSections T w q = (T.hom^* contract)(κ_T(w ⊗ q))`, where `κ_T` is the composite of
`tensorIsoTensorObj` and `pullbackTensorObjIso`. Pulling a section back along `j` is the component on `⊤`
of the adjunction unit (`sectionPullbackAlong`), which is natural in morphisms of sheaves of modules
(`sectionPullbackAlong_app`), so
`j^*((T.hom^*contract)(κ_T(w ⊗ q))) = (j^*T.hom^*contract)(j^*κ_T(w ⊗ q))`; then `pullbackComp` replaces
`j^*T.hom^*` by `(j ≫ T.hom)^*` (naturality of `pullbackComp`), and the general lemma
`pullbackComp_pullbackTensorObjIso_inv_tensorSections` (apply `δ_{j≫T.hom}`, then
`pullbackComp_hom_app_pullbackTensorObjHom`, `pullbackTensorObjHom_app_unit_tensorSections`,
`tensorHom_tensorSections`) replaces `j^*κ_T(w ⊗ q)` by `κ_S(j^*w ⊗ j^*q)`; `sectionTensor` composed with
`tensorIsoTensorObj.hom` is `tensorSections` by definition.
Note: `rw` cannot be used here (`Γ(M, ⊤)` and `M.val.obj (op ⊤)` differ at implicit transparency, so the
motive is not type-correct); everything goes through `congrArg`/`Eq.trans`. -/
theorem conePuncturedLineBundle.contractSections_pullback {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle]
    (T : CategoryTheory.Over (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (w : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)).val.obj
      (Opposite.op ⊤) : Type u))
    (q : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app _).app ⊤
        (sectionPullbackAlong j (conePuncturedLineBundle.contractSections e A T w q)) =
      conePuncturedLineBundle.contractSections e A (CategoryTheory.Over.mk (j ≫ T.hom))
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app _).app ⊤ (sectionPullbackAlong j w))
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app _).app ⊤ (sectionPullbackAlong j q)) := by
  unfold conePuncturedLineBundle.contractSections
  refine (congrArg (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app _).app ⊤)
    (sectionPullbackAlong_app j
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (conePuncturedLineBundle.contract e A)) _)).trans ?_
  refine (pullbackComp_hom_app_app_map j T.hom (conePuncturedLineBundle.contract e A) _).trans ?_
  refine congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ T.hom)).map
    (conePuncturedLineBundle.contract e A)).app ⊤ z) ?_
  exact pullbackComp_pullbackTensorObjIso_inv_tensorSections j T.hom _ _ w q

end
