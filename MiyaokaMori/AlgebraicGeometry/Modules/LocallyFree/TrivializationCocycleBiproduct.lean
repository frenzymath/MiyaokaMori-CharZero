import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow

/-! # The trivialization cocycle of a direct sum of line bundles

The (1×1) trivialization cocycles `d^i_{αα'}` of a family of line bundles `V_i` assemble into the
trivialization cocycle `diag(d^1, …, d^r)` of the direct sum `⨁_i V_i` (the split weighted bundle
`⊕_i Q_i` of Lemma 2.3 of the paper, whose transition matrices are the diagonal
part of `g`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A morphism of sheaves of modules commutes with restriction (elementwise form). -/
private theorem app_res_aux {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- A finite sum of morphisms acts on sections as the sum of the actions. -/
private theorem sum_app_apply_aux {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} {J : Type v}
    (s : Finset J) (φ : J → (M ⟶ N)) (W : X.Opens) (x : Γ(M, W)) :
    (∑ j ∈ s, φ j).app W x = ∑ j ∈ s, (φ j).app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AlgebraicGeometry.Scheme.Modules.Hom.add_app,
      AddCommGrpCat.hom_add_apply, ih]

/-- A section of a biproduct is the sum of its components `ι_j ∘ π_j` (`biproduct.total` on sections). -/
private theorem biproduct_section_decomp_aux {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V : Fin r → X.Modules) (W : X.Opens) (s : Γ(⨁ V, W)) :
    s = ∑ j, (biproduct.ι V j).app W ((biproduct.π V j).app W s) := by
  have h := congrArg (fun φ : (⨁ V ⟶ ⨁ V) => φ.app W s) (biproduct.total (f := V))
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.id_app, CategoryTheory.id_apply] at h
  rw [sum_app_apply_aux] at h
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h
  exact h.symm

private theorem π_app_ι_app_self_aux {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V : Fin r → X.Modules) (W : X.Opens) (j : Fin r) (x : Γ(V j, W)) :
    (biproduct.π V j).app W ((biproduct.ι V j).app W x) = x := by
  have h := congrArg (fun φ : (V j ⟶ V j) => φ.app W x) (biproduct.ι_π_self V j)
  simpa only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Hom.id_app, CategoryTheory.id_apply] using h

private theorem π_app_ι_app_ne_aux {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V : Fin r → X.Modules) (W : X.Opens) {i j : Fin r} (hij : i ≠ j) (x : Γ(V i, W)) :
    (biproduct.π V j).app W ((biproduct.ι V i).app W x) = 0 := by
  have h := congrArg (fun φ : (V i ⟶ V j) => φ.app W x) (biproduct.ι_π_ne V hij)
  simpa only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply] using h

/-- If every `V_i` has a `1×1` trivialization cocycle `(d_{αα'} i)` on the open cover `U`, then
`⨁_i V_i` has the trivialization cocycle `diag(d_{αα'})` on `U` (the local frames of a direct sum are
the unions of the local frames of the summands).

Proof sketch. The isomorphism `Γ(⨁V, W) ≅ ⊕ Γ(V_i, W)` itself is not needed; only `biproduct.total`
(`Σ_j π_j ≫ ι_j = 𝟙`) and `biproduct.ι_π_self` / `biproduct.ι_π_ne` on sections:
  `s = Σ_j ι_j(π_j s)`, `π_j ∘ ι_j = id`, `π_k ∘ ι_j = 0` (`j ≠ k`),
together with the compatibility of sheaf morphisms with restriction (`φ.mapPresheaf.naturality`) and
with `Γ(X, ·)`-scalars (`Hom.app_smul`).

Frames: by hypothesis `V_i` has a frame `e^i_α : Fin 1 → Γ(V_i, U_α)` on `U_α`; put
  `e_α i := (biproduct.ι V i).app (U α) (e^i_α 0) ∈ Γ(⨁V, U_α)`.
(1) `IsFrameOn (⨁V) (U α) (e α)`: for `W' ≤ U_α`, `e_α i |_{W'} = ι_i(e^i_α 0 |_{W'})` (naturality).
  Linear independence: if `Σ_j c_j • ι_j(b_j) = 0` (`b_j := e^j_α 0 |_{W'}`), applying `π_k` gives
  `c_k • b_k = 0`, hence `c_k = 0` by the linear independence of `b_k` (the `Fin 1` case).
  Spanning: `s = Σ_j ι_j(π_j s)` with `π_j s ∈ Γ(V_j, W') = span{b_j}`, so `π_j s = c_j • b_j` and
  `s = Σ_j c_j • ι_j(b_j)`.
(2) Transition relations: for `j`, `e_{α'} j` restricted to `U_α ⊓ U_α'` is
  `ι_j(e^j_{α'} 0 |) = ι_j((d_{αα'} j) • e^j_α 0 |)` (the `1×1` relation of `V_j`, `Fin.sum_univ_one`)
  `= (d_{αα'} j) • e_α j |` (`ι_j` commutes with scalars)
  `= Σ_i (diag(d_{αα'}))_{ij} • e_α i |` (`Matrix.diagonal_apply`, `Finset.sum_ite_eq`). -/
theorem IsTrivializationCocycle.biproduct {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {r : ℕ}
    (V : Fin r → X.Modules) (U : ι → X.Opens) (d : ∀ α α' : ι, Fin r → Γ(X, U α ⊓ U α'))
    (h : ∀ i, IsTrivializationCocycle (V i) U (fun α α' => Matrix.of fun _ _ : Fin 1 => d α α' i)) :
    IsTrivializationCocycle (⨁ V) U (fun α α' => Matrix.diagonal (d α α')) := by
  classical
  choose e he using h
  refine ⟨fun α j => (biproduct.ι V j).app (U α) (e j α 0), fun α => ?_, fun α α' j => ?_⟩
  · intro W' hW'
    have hres : ∀ j, (⨁ V).presheaf.map (homOfLE hW').op ((biproduct.ι V j).app (U α) (e j α 0)) =
        (biproduct.ι V j).app W' ((V j).presheaf.map (homOfLE hW').op (e j α 0)) :=
      fun j => (app_res_aux _ hW' _).symm
    have hb := fun j => (he j).1 α W' hW'
    constructor
    · rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h1 := congrArg ((biproduct.π V k).app W') hc
      simp only [hres, map_sum, map_zero, AlgebraicGeometry.Scheme.Modules.Hom.app_smul] at h1
      rw [Finset.sum_eq_single k (fun j _ hjk => by
          rw [π_app_ι_app_ne_aux V W' hjk, smul_zero]) (fun hk => absurd (Finset.mem_univ k) hk),
        π_app_ι_app_self_aux] at h1
      have hli := (Fintype.linearIndependent_iff.mp (hb k).1) (fun _ => c k)
      simpa only [Fin.sum_univ_one] using hli (by simpa only [Fin.sum_univ_one] using h1) 0
    · rw [eq_top_iff]
      intro s _
      rw [biproduct_section_decomp_aux V W' s]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hs : (biproduct.π V j).app W' s ∈
          Submodule.span Γ(X, W') (Set.range fun i => (V j).presheaf.map (homOfLE hW').op (e j α i)) := by
        rw [(hb j).2]; trivial
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hs
      rw [← hc, Fin.sum_univ_one, AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hres j⟩)
  · rw [← app_res_aux, (he j).2 α α' 0]
    simp only [Fin.sum_univ_one, Matrix.of_apply, AlgebraicGeometry.Scheme.Modules.Hom.app_smul,
      Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      app_res_aux]

end
