import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContractInjectiveEvalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence

/-! # Surjectivity of the pairing, and preservation of vanishing

Two properties of the pairing `⟨·,·⟩` (`T` over `C ×_k X`, `L = pr₁^*A ⊗ pr₂^*O_X(−1)`):
* surjectivity `exists_contractSections_eq`: for every morphism of sheaves of modules
  `ψ : T.hom^*pr₂^*O_X(1) ⟶ T.hom^*pr₁^*A` there is `w ∈ Γ(T, T.hom^*L)` with `⟨w, q⟩ = ψ(q)` for all
  global sections `q` (`L` realized as `𝓗om(pr₂^*O_X(1), pr₁^*A)`);
* preservation of vanishing `isZeroAt_contractSections`: if `w` vanishes at `p`, so does `⟨w, q⟩`.

Route for surjectivity: `κ⁻¹ ≫ T.hom^*contract` is an isomorphism (`isIso_contract`) and `− ⊗ Q'` is a
self-equivalence (`Q'` a line bundle, `isEquivalence_tensorRight_of_isLineBundle`), so
`(λ_ Q').hom ≫ ψ ≫ F⁻¹` lifts to `w₀ ▷ Q'`; put `w := w₀(1)`. `contract` is not unfolded (the unfolded
defeq check is expensive, see the header of `…ContractInjectiveEvalIso`).

Source: eq. (2.1) of the paper (`t^*A ⊗ x^*O_X(−1) = Hom(x^*O_X(1), t^*A)`);
Stacks 01CT, 01CM.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u u₁ v₁

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

/-- The pairing preserves "vanishing at `p`": `contractSections T w q` is a morphism of sheaves of modules applied
to `sectionTensor w q` (`isZeroAt_map` three times), and the tensor `w ⊗ q` of sections of line bundles vanishes
at `p` iff `w` or `q` vanishes at `p` (`mem_nonvanishingLocus_sectionTensor`; both factors `T.hom^*L` and
`T.hom^*pr₂^*O_X(1)` are line bundles, `IsLineBundle.pullback`). -/
theorem conePuncturedLineBundle.isZeroAt_contractSections {k : Type u} [Field k]
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
        (e.oX 1))).val.obj (Opposite.op ⊤) : Type u))
    (p : T.left) (hw : IsZeroAt w p) :
    IsZeroAt (conePuncturedLineBundle.contractSections e A T w q) p := by
  have h1 : (projectiveSpaceTwist k N 1).IsLineBundle := projectiveSpaceTwist_isLineBundle k N 1
  have h2 : (e.oX 1).IsLineBundle :=
    @AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _ e.emb (projectiveSpaceTwist k N 1) h1
  have h0 : IsZeroAt (sectionTensor w q) p := by
    by_contra hn
    have hmem := (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionTensor
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A))
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
          (e.oX 1))) w q p).1
      ((AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ _ _).2 hn)
    exact ((AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ _ _).1 hmem.1) hw
  have h1 := isZeroAt_map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A))
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1)))).hom (sectionTensor w q) p h0
  have h2 := isZeroAt_map (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom
    (conePuncturedLineBundle e A)
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
      (e.oX 1))).inv _ p h1
  have h3 := isZeroAt_map ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
    (conePuncturedLineBundle.contract e A)) _ p h2
  exact h3


/-! ## General lemmas (categorical, plus transport of sections) for `exists_contractSections_eq`

The route does not unfold `contract` into `(ι ▷ Q) ≫ α ≫ (M ◁ eval) ≫ ρ` (that defeq check is expensive, see
the header of `…ContractInjectiveEvalIso`). Instead: `F := κ⁻¹ ≫ T.hom^*contract` is an isomorphism
(`isIso_contract`), `Q'` is a line bundle so `− ⊗ Q'` is a self-equivalence
(`isEquivalence_tensorRight_of_isLineBundle`), hence `(λ_ Q').hom ≫ ψ ≫ F⁻¹ : 𝟙 ⊗ Q' ⟶ L' ⊗ Q'` comes from
some `w₀ ▷ Q'` by fullness; take `w := w₀(1)`. -/

namespace ConePairingAux

open CategoryTheory.MonoidalCategory

section Monoidal

variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]

/-- **Surjectivity of the pairing (categorical level).** If `F : L ⊗ Q ⟶ M` is an isomorphism and `− ⊗ Q` is a
full functor, then every `ψ : Q ⟶ M` is `(λ_ Q)⁻¹ ≫ (w ▷ Q) ≫ F`: lift `(λ_ Q).hom ≫ ψ ≫ F⁻¹ : 𝟙 ⊗ Q ⟶ L ⊗ Q`
along `− ⊗ Q` to `w ▷ Q`. -/
theorem exists_pairing_eq_of_isIso {L Q M : D} (F : L ⊗ Q ⟶ M) [IsIso F] [(tensorRight Q).Full]
    (ψ : Q ⟶ M) : ∃ w : 𝟙_ D ⟶ L, (λ_ Q).inv ≫ (w ▷ Q) ≫ F = ψ := by
  obtain ⟨w, hw⟩ := (tensorRight Q).map_surjective ((λ_ Q).hom ≫ ψ ≫ inv F)
  refine ⟨w, ?_⟩
  have hw' : w ▷ Q = (λ_ Q).hom ≫ ψ ≫ inv F := hw
  rw [hw']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]

end Monoidal

section Sections

variable {Y : AlgebraicGeometry.Scheme.{u}}

theorem comp_app_apply {A B E : Y.Modules} (f : A ⟶ B) (g : B ⟶ E) (U : Y.Opens) (x : Γ(A, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

theorem whiskerRight_app_tensorSections {A A' B : Y.Modules} (f : A ⟶ A') (U : Y.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

/-- `1 ⊗ q = (λ_ Q)⁻¹ q` (`leftUnitor_app_tensorSections` read backwards). -/
theorem tensorSections_one_left (Q : Y.Modules) (q : Γ(Q, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) Q ⊤ (1 : Γ(Y, ⊤)) q =
      (λ_ Q).inv.app ⊤ q := by
  have h := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections Q ⊤ (1 : Γ(Y, ⊤)) q
  rw [one_smul] at h
  have h2 := congrArg ((λ_ Q).inv.app ⊤) h
  refine Eq.trans ?_ h2
  have h3 := congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ ⊤
    (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) Q ⊤ (1 : Γ(Y, ⊤)) q))
    (λ_ Q).hom_inv_id
  exact h3.symm

/-- On sections: if `(λ_)⁻¹ ≫ (w₀ ▷ Q) ≫ F = ψ`, then `w := w₀(1)` satisfies `F(w ⊗ q) = ψ(q)`
(`whiskerRight_app_tensorSections`, `tensorSections_one_left`, `comp_app_apply`; the goal is not type-correct
at implicit transparency, so everything goes through `congrArg`/`Eq.trans` rather than `rw`). -/
theorem sections_pairing_eq {L Q M : Y.Modules} (F : L ⊗ Q ⟶ M) (ψ : Q ⟶ M)
    (w₀ : 𝟙_ Y.Modules ⟶ L) (hw₀ : (λ_ Q).inv ≫ (w₀ ▷ Q) ≫ F = ψ) (q : Γ(Q, ⊤)) :
    F.app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorSections L Q ⊤ (w₀.app ⊤ (1 : Γ(Y, ⊤))) q) =
      ψ.app ⊤ q := by
  have e1 := (whiskerRight_app_tensorSections w₀ ⊤ (1 : Γ(Y, ⊤)) q).symm
  have e2 := tensorSections_one_left Q q
  have e3 : ((λ_ Q).inv ≫ (w₀ ▷ Q) ≫ F).app ⊤ q = F.app ⊤ ((w₀ ▷ Q).app ⊤ ((λ_ Q).inv.app ⊤ q)) :=
    (comp_app_apply _ _ ⊤ q).trans (comp_app_apply _ _ ⊤ _)
  have e4 : ((λ_ Q).inv ≫ (w₀ ▷ Q) ≫ F).app ⊤ q = ψ.app ⊤ q :=
    congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ ⊤ q) hw₀
  refine (congrArg (F.app ⊤) e1).trans ?_
  refine (congrArg (fun z => F.app ⊤ ((w₀ ▷ Q).app ⊤ z)) e2).trans ?_
  exact e3.symm.trans e4

end Sections

end ConePairingAux

/-- **Surjectivity of the pairing.** For `T` over `C ×_k X` and any morphism of sheaves of modules
`ψ : T.hom^*pr₂^*O_X(1) ⟶ T.hom^*pr₁^*A`, there is `w ∈ Γ(T, T.hom^*L)` (`L = pr₁^*A ⊗ pr₂^*O_X(−1)`) with
`⟨w, q⟩ = ψ(q)` for every global section `q` (`contractSections e A T w q = (ψ.val.app (op ⊤)).hom q`). That
is, `L` is realized as `𝓗om(pr₂^*O_X(1), pr₁^*A)`, and `w ↦ ⟨w, ·⟩` is surjective on global sections
(injectivity is `contractSections_injective`).

Source: eq. (2.1) of the paper (`t^*A ⊗ x^*O_X(−1) = Hom(x^*O_X(1), t^*A)`); Stacks 01CT
(for finite locally free `𝓔`: `𝓔^∨ ⊗ 𝓕 ≅ 𝓗om(𝓔, 𝓕)`), 01CM (tensor–Hom adjunction).

Notation (line bundles on `T`, `IsLineBundle.pullback`; `O_X(±1)` are line bundles:
`projectiveSpaceTwist_isLineBundle`, `moduleSheafDual_isLineBundle`): `M' := T.hom^*pr₁^*A`,
`D' := T.hom^*pr₂^*O_X(−1)`, `Q' := T.hom^*pr₂^*O_X(1)`, `κ : T.hom^*L ≅ M' ⊗ D'` (`tensorIsoTensorObj`
followed by `pullbackTensorObjIso`, the isomorphism used in `contractSections`). By definition
(`contractSections`, `contract`, `conePuncturedLineBundle.eval`), `⟨w, q⟩ = (T.hom^*contract)(κ⁻¹(w ⊗ q))`,
and under the monoidal isomorphisms `T.hom^*contract` is `(α_)^{hom} ≫ (M' ◁ ev') ≫ (ρ_)^{hom}`, where
`ev' : D' ⊗ Q' → O_T` is the pullback along `pr₂`, `T.hom` of the evaluation `O_X(−1) ⊗ O_X(1) → O_X`
(`internalHomEval`) (through `pullbackTensorObjIso`, `pullbackUnitIso`).

Proof. `F := κ⁻¹ ≫ T.hom^*contract : L' ⊗ Q' ⟶ M'` is an isomorphism
(`conePuncturedLineBundle.isIso_contract`; pullback preserves isomorphisms), and `Q'` is a line bundle
(`IsLineBundle.pullback` twice), so `− ⊗ Q'` is a self-equivalence of the sheaves of modules on `T`, in
particular a full functor (`isEquivalence_tensorRight_of_isLineBundle`); hence
`(λ_ Q').hom ≫ ψ ≫ F⁻¹ : 𝟙 ⊗ Q' ⟶ L' ⊗ Q'` is some `w₀ ▷ Q'` (`ConePairingAux.exists_pairing_eq_of_isIso`),
so `(λ_ Q')⁻¹ ≫ (w₀ ▷ Q') ≫ F = ψ`. Put `w := w₀(1) ∈ Γ(T, L')`: `w ⊗ q = (w₀ ▷ Q')(1 ⊗ q)`
(`whiskerRight_app_tensorSections`) and `1 ⊗ q = (λ_ Q')⁻¹ q` (`leftUnitor_app_tensorSections`), so
`F(w ⊗ q) = ((λ_)⁻¹ ≫ (w₀ ▷ Q') ≫ F)(q) = ψ(q)` (`ConePairingAux.sections_pairing_eq`); and
`contractSections e A T w q` is by definition `F.app ⊤ (w ⊗ q)` (`sectionTensor` composed with
`tensorIsoTensorObj.hom` is `tensorSections`, definitionally).

Two alternative routes, kept as mathematical explanation (both unfold `contract` into
`(ι ▷ Q) ≫ α ≫ (M ◁ eval) ≫ ρ`, whose defeq check is too expensive):
(i) (01CT/01CM) `Λ : M' ⊗ D' → 𝓗om(Q', M') := tensorHomCurry ((α_)^{hom} ≫ (M' ◁ ev') ≫ (ρ_)^{hom})`
    (`tensorHomEquiv`) is an isomorphism: on an open `U` where `Q'` has a frame `q₀`, both
    `𝓗om(Q', M')|_U ≅ M'|_U` (`φ ↦ φ(q₀)`) and `(M' ⊗ D')|_U ≅ M'|_U` (`m ⊗ d ↦ ev'(d ⊗ q₀)·m`), and `Λ|_U` is the
    identity under these identifications; `ψ` corresponds to a global section `ψ̂` of `𝓗om(Q', M')`, and
    `w := κ⁻¹(Λ⁻¹ ψ̂)` works.
(ii) (without `𝓗om`) `c := ev'⁻¹(1) ∈ Γ(T, D' ⊗ Q')`, `w := κ⁻¹((ψ ⊗ id_{D'})(β(c)))` with `β` the braiding
    `D' ⊗ Q' ≅ Q' ⊗ D'`; `⟨w, q⟩ = ψ(q)` reduces by `whisker_exchange` to the zig-zag identity
    `(id_{Q'} ⊗ ev')(β c ⊗ q) = q`, checked on opens where `Q'` has a frame.
Edge cases: for `T = ∅` all section types are singletons and the statement is trivial; `N = 0` is not special. -/
theorem conePuncturedLineBundle.exists_contractSections_eq {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle]
    (T : CategoryTheory.Over (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
          (e.oX 1)) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)) :
    ∃ w : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)).val.obj
        (Opposite.op ⊤) : Type u),
      ∀ q : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
              (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
            (e.oX 1))).val.obj (Opposite.op ⊤) : Type u),
        conePuncturedLineBundle.contractSections e A T w q = (ψ.val.app (Opposite.op ⊤)).hom q := by
  -- `Q' = T.hom^*pr₂^*O_X(1)` is a line bundle, so `− ⊗ Q'` is a self-equivalence, in particular full
  have hQ1 : ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1)).IsLineBundle :=
    @AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _ (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) _ (ProjectiveEmbedding.oX_one_isLineBundle e)
  have hQ : ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1))).IsLineBundle :=
    @AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _ T.hom _ hQ1
  have hFull : (CategoryTheory.MonoidalCategory.tensorRight ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1)))).IsEquivalence :=
    @AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle _ _ hQ
  -- `F = κ⁻¹ ≫ T.hom^*contract` is an isomorphism (`isIso_contract`)
  have hc : CategoryTheory.IsIso (conePuncturedLineBundle.contract e A) := conePuncturedLineBundle.isIso_contract e A
  have hF : CategoryTheory.IsIso
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom (conePuncturedLineBundle e A) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1))).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (conePuncturedLineBundle.contract e A)) := inferInstance
  obtain ⟨w₀, hw₀⟩ := ConePairingAux.exists_pairing_eq_of_isIso
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom (conePuncturedLineBundle e A) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1))).inv ≫
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (conePuncturedLineBundle.contract e A)) ψ
  refine ⟨w₀.app ⊤ (1 : Γ(T.left, ⊤)), fun q => ?_⟩
  exact ConePairingAux.sections_pairing_eq _ ψ w₀ hw₀ q

end
