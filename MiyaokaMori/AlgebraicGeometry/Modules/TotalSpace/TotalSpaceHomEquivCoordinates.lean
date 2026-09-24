import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality

/-! # Morphisms to the total space of a direct sum are determined by their coordinates

Statement: `V = ⨁_ℓ A_ℓ` is the biproduct of finitely many modules on `X` (locally free of finite type), `T` a scheme
over `X`, `g = T.hom`. Then an `X`-morphism `m : T → Tot(V)` is determined by its coordinate sections: if the sections
corresponding to `m₁`, `m₂` under `totalSpaceHomEquiv` have the same image under every projection
`g^*(π_ℓ) : g^*V → g^*A_ℓ`, then `m₁ = m₂` (`totalSpaceHom_ext_of_coordinates`). Accompanying coordinate calculus:
(a) a global section of `g^*(⨁ A_ℓ)` is determined by its coordinates (`pullback_biproduct_section_ext`);
(b) module morphisms commute with scalar multiplication on global sections, in particular the coordinates do
(`modules_hom_app_top_smul`), so the `ℓ`-th coordinate of the morphism corresponding to `u•σ` is `u •` (the `ℓ`-th
coordinate of `σ`) (`totalSpaceHomEquiv_symm_smul_coordinate`); (c) pullback of sections along `j` is compatible with
scalar multiplication, `j^*(a•s) = j^♯(a) • j^*s` (`sectionPullbackAlong_smul`), and commutes with module morphisms
(`sectionPullbackAlong_naturality`); (d) the `ℓ`-th coordinate after precomposition with `j` is the `ℓ`-th coordinate
pulled back along `j` and transported by `pullbackComp` (`totalSpaceHomEquiv_naturality_coordinate`).

Proof:
1. (a): `g^*` is a left adjoint, hence additive (`Adjunction.left_adjoint_additive`); the global sections functor
   `SheafOfModules.evaluation _ (op ⊤)` is additive. Apply both functors to `biproduct.total`: `Σ_ℓ π_ℓ ≫ ι_ℓ = 𝟙`
   gives `x = Σ_ℓ (g^*ι_ℓ)((g^*π_ℓ) x)`, so two sections with the same coordinates are equal.
2. Main statement: `totalSpaceHomEquiv` is a bijection (`Equiv.injective`), so (a) suffices.
3. (b): module morphisms on `⊤` are `Γ(T, O_T)`-linear (`map_smul`); apply after `Equiv.apply_symm_apply`.
4. (c): `sectionPullbackAlong` is the component at `⊤` of the adjunction unit `η_M : M → j_*j^*M`; `η_M` is `O_Y`-linear,
   and the `Γ(Y,O_Y)`-action on `j_*N` over `⊤` is by definition through `j^♯ = appTop`, so `map_smul` is the claim;
   commutation with morphisms is the naturality of `η`.
5. (d): `totalSpaceHomEquiv_naturality` gives the equation on sections; then the naturality in (c) and the naturality of
   `pullbackComp j g` (`NatTrans.naturality`) move the projection `π_ℓ` across.
-/
/- `sectionPullbackAlong` is by definition the adjunction unit, and `ModuleSections.pullback` is its `Γ`-typed
reducible abbreviation: the proofs below use `simp only [sectionPullbackAlong_eq_pullback]` (to reach the
latter) or plain `unfold sectionPullbackAlong` (to reach the unit). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.Modules.pullback_biproduct_section_ext {X T : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) {n : ℕ} (A : Fin n → X.Modules)
    (s t : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj (⨁ A)).val.obj (Opposite.op ⊤) : Type u))
    (h : ∀ ℓ, (((AlgebraicGeometry.Scheme.Modules.pullback g).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom s
      = (((AlgebraicGeometry.Scheme.Modules.pullback g).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom t) :
    s = t := by
  have : (AlgebraicGeometry.Scheme.Modules.pullback g).Additive :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).left_adjoint_additive
  let F := AlgebraicGeometry.Scheme.Modules.pullback g
  let E : T.Modules ⥤ ModuleCat (T.ringCatSheaf.obj.obj (Opposite.op (⊤ : T.Opens))) :=
    SheafOfModules.evaluation T.ringCatSheaf (Opposite.op (⊤ : T.Opens))
  have : E.Additive := inferInstanceAs (SheafOfModules.forget T.ringCatSheaf ⋙
      PresheafOfModules.evaluation T.ringCatSheaf.obj (Opposite.op (⊤ : T.Opens))).Additive
  have e : 𝟙 (E.obj (F.obj (⨁ A))) =
      ∑ ℓ, E.map (F.map (biproduct.π A ℓ)) ≫ E.map (F.map (biproduct.ι A ℓ)) := by
    rw [← E.map_id, ← F.map_id, ← biproduct.total, F.map_sum, E.map_sum]
    simp only [Functor.map_comp]
  have key : ∀ x : (((AlgebraicGeometry.Scheme.Modules.pullback g).obj (⨁ A)).val.obj (Opposite.op ⊤) : Type u),
      x = ∑ ℓ, (E.map (F.map (biproduct.ι A ℓ))).hom ((E.map (F.map (biproduct.π A ℓ))).hom x) := by
    intro x
    have := congrArg (fun φ => φ.hom x) e
    simp only [ModuleCat.hom_id, ModuleCat.hom_sum, ModuleCat.hom_comp, LinearMap.id_coe, id] at this
    refine this.trans ((LinearMap.sum_apply _ _ _).trans ?_)
    rfl
  rw [key s, key t]
  exact Finset.sum_congr rfl (fun ℓ _ => congrArg _ (h ℓ))

theorem sectionPullbackAlong_smul {X Y : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) {M : Y.Modules}
    (a : Γ(Y, ⊤)) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong j ((show Y.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • s)
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from j.appTop a) • sectionPullbackAlong j s := by
  unfold sectionPullbackAlong
  exact (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).val.app
    (Opposite.op ⊤)).hom.map_smul _ s

/-- An `X`-morphism to the total space of a biproduct is determined by its coordinate sections. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHom_ext_of_coordinates {X : AlgebraicGeometry.Scheme.{u}}
    {n : ℕ} (A : Fin n → X.Modules) [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    (T : CategoryTheory.Over X) (m₁ m₂ : T ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ A))
    (h : ∀ ℓ,
      (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T m₁)
        = (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T m₂)) :
    m₁ = m₂ :=
  (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T).injective
    (AlgebraicGeometry.Scheme.Modules.pullback_biproduct_section_ext T.hom A _ _ h)

/-- Module morphisms commute with the `Γ(T, O_T)`-scalar multiplication on global sections. -/
theorem AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul {T : AlgebraicGeometry.Scheme.{u}}
    {M N : T.Modules} (φ : M ⟶ N) (a : Γ(T, ⊤)) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (φ.val.app (Opposite.op ⊤)).hom ((show T.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • s)
      = (show T.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • (φ.val.app (Opposite.op ⊤)).hom s :=
  (φ.val.app (Opposite.op ⊤)).hom.map_smul _ s

/-- Pullback of sections along `j` commutes with module morphisms (`.val.app` form). -/
theorem sectionPullbackAlong_naturality {X Y : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) {M M' : Y.Modules}
    (φ : M ⟶ M') (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong j ((φ.val.app (Opposite.op ⊤)).hom s)
      = (((AlgebraicGeometry.Scheme.Modules.pullback j).map φ).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j s) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality φ
  exact congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤) s) h

/-- The `ℓ`-th coordinate of the morphism corresponding to `u•σ` is `u •` (the `ℓ`-th coordinate of `σ`). The
definition body of `twistedAffineCone.scale` has exactly this shape. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_smul_coordinate {X : AlgebraicGeometry.Scheme.{u}}
    {n : ℕ} (A : Fin n → X.Modules) [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    (T : CategoryTheory.Over X) (a : Γ(T.left, ⊤))
    (σ : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (⨁ A)).val.obj (Opposite.op ⊤) : Type u))
    (ℓ : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T
          ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T).symm
            ((show T.left.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • σ)))
      = (show T.left.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) •
          (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (biproduct.π A ℓ)).val.app
            (Opposite.op ⊤)).hom σ := by
  rw [Equiv.apply_symm_apply]
  exact AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul _ a σ

/-- The `ℓ`-th coordinate after precomposition with `j` is the `ℓ`-th coordinate pulled back along `j`, then
transported by `pullbackComp`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate {X : AlgebraicGeometry.Scheme.{u}}
    {n : ℕ} (A : Fin n → X.Modules) [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    (T : CategoryTheory.Over X) {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ A)) (ℓ : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ T.hom)).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) (CategoryTheory.Over.mk (j ≫ T.hom))
          ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app (A ℓ)).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j
            ((((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (biproduct.π A ℓ)).val.app
              (Opposite.op ⊤)).hom (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T m))) := by
  rw [AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality, sectionPullbackAlong_naturality]
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.naturality (biproduct.π A ℓ)
  exact (congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom
    (sectionPullbackAlong j (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T m))) h).symm

end
