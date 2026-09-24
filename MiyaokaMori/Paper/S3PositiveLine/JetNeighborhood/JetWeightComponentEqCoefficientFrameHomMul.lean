import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap

/-! # Multiplicativity of `c ↦ c·ξ^n` at the level of morphisms (helper of `JetWeightComponentEqCoefficient`)

The morphism-level content behind the leaves `BasedJet.frameHom_pieceMul` and
`BasedJet.universalFrameAlg_isAlgebraMap` of `MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient`;
the main file only does the assembly on sections.

* `isQuasicoherent_of_isLineBundle` and `biproduct_section_eq_sum` are declared here and used by the main file,
  which imports this module; `tensorPowerToSymPart_symPartToMonoidalPow` appears here as a **private** copy
  (`…_frameHomMulAux`, with the same statement and proof) of the corresponding lemma of the main file.
* Variable level: `tensorHom_comp_mul_eq_of_retract` (`χ_i` a section of `σ_i`, `σ_{m+n}` mono,
  `mul ≫ σ = (σ ⊗ σ) ≫ cat` ⇒ `(χ ⊗ χ) ≫ mul = cat ≫ χ`), `pieceMul_assembly_aux` (three compatibilities chained
  into one), `QCAlgebra.IsAlgebraMapToPushforward.app_mul_of_comp_eq` (a morphism-level equation gives the
  multiplication formula on sections), `Modules.isAlgebraMap_mul_of_pieces` (decompose sections of a biproduct into
  components, reducing "preserves multiplication" to `ι_p a ⊗ ι_q b`).
* Concrete level (line bundle `N`, `D = N^∨`, `S = Sym D`):
  `powIso_tensorPowerToSymPart_symPartToMonoidalPow` (`χ_q ≫ σ_q = 𝟙`),
  `tensorHom_powIso_tensorPowerToSymPart_comp_mul` (`(χ_p ⊗ χ_q) ≫ S.mul = monoidalPowCat ≫ χ_{p+q}`; the "inverse"
  of `Modules.mul_comp_symPartToMonoidalPow`), `powIso_zero_comp_tensorPowerToSymPart_zero` (`χ_0 = S.one`),
  `truncatedJetAlgebra.pieceMul_comp_frameHomCore` (the morphism-level form of `frameHom_pieceMul`,
  = `pieceIso_mul` + the previous lemma + `tensor_ι_comp_totalMul`).
Source: proof of Lemma 3.1 of the paper; Stacks 01LQ (algebra maps of a relative Spec). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- **Leaf (general fact at variable level).** A line bundle is quasi-coherent.

    Proof (Stacks 01BE/01BI): a line bundle is locally isomorphic to `O`; `O` is quasi-coherent (take the trivial
    presentation `0 → O → O → 0`); quasi-coherence is local and invariant under isomorphism. In Mathlib,
    `SheafOfModules.IsQuasicoherent` is defined through `QuasicoherentData` (an open cover plus a presentation on each
    member); take the cover given by `IsLineBundle.exists_trivialization` and transport the trivial presentation of
    `O` along the trivializations. The instance "locally free ⇒ quasi-coherent" of Mathlib's `Sheaf/LocallyFree.lean`
    applies directly (it is not found by `infer_instance`, but can be applied explicitly).
    Edge case: trivial for the empty scheme. -/
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLineBundle {Y : AlgebraicGeometry.Scheme.{u}}
    (N : Y.Modules) [N.IsLineBundle] : N.IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree N -- general form: locally free ⇒ quasi-coherent

/-- **Leaf.** On a line bundle, "tensor power → `Sym^q` → tensor power" is the inverse of `powIso`:
`tensorPowerToSymPart ≫ symPartToMonoidalPow = powIso⁻¹`.

    Proof: the bodies of both morphisms are `unfold symGradedAlgebra; split`; when `L^∨` is quasi-coherent (previous
    leaf; `L^∨` is a line bundle by `SheafOfModules.IsLineBundle.dual`) both land in the first branch,
    `tensorPowerToSymPart = powIso.inv ≫ symPowπ` and `symPartToMonoidalPow = inv symPowπ`, so the composite is
    `powIso.inv ≫ symPowπ ≫ inv symPowπ = powIso.inv` (`IsIso.hom_inv_id`).
    Technically: first `have hq := isQuasicoherent_of_isLineBundle (dual L)`, then
    `unfold totalSpace.tensorPowerToSymPart Modules.symPartToMonoidalPow` and enter the first branch with `split` (or
    `simp only [dif_pos hq]`); `symGradedAlgebra` is a `dite` and the type of `part q` depends on the branch, so if
    necessary `generalize`/`rw [dif_pos hq]` on the whole `symGradedAlgebra V`.
    Without quasi-coherence the trivial branch for `q ≥ 1` would compare `0 ≫ 0` and the equation would be false, so
    the previous leaf is necessary. Private copy of the lemma of the same name in `JetWeightComponentEqCoefficient.lean`. -/
private theorem AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_symPartToMonoidalPow_frameHomMulAux
    {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules) [N.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.dual N).IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N q ≫
        AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) q =
      (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) q).inv := by
  -- both bodies take the quasi-coherent branch directly by `rw [dif_pos _]`; here the type-transport proof of the
  -- branch is abstracted into a variable and `symGradedAlgebra _ = symGradedAlgebraOfQC _ hq` is `subst`ituted.
  have hq : (AlgebraicGeometry.Scheme.Modules.dual N).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLineBundle _
  have casesOn_const : ∀ {P : Prop} {T : Type u} (d : Decidable P) (f : ¬P → T) (g : P → T) (hp : P),
      Decidable.casesOn (motive := fun _ => T) d f g = g hp := by
    intro P T d f g hp
    cases d with
    | isFalse h => exact absurd hp h
    | isTrue h => rfl
  unfold AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart
    AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
  rw [CategoryTheory.Category.assoc]
  refine (congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
    (AlgebraicGeometry.Scheme.Modules.dual N) q).inv ≫ t) ?_).trans (CategoryTheory.Category.comp_id _)
  generalize_proofs _ _ pf3 pf4 pf5 pf6
  have hS : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual N) =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC (AlgebraicGeometry.Scheme.Modules.dual N) hq := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hq
  change (pf4 pf3).mpr (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual N) q) ≫
    (pf5 pf3).mpr (@CategoryTheory.inv _ _ _ _
      (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual N) q) (pf6 pf3)) = 𝟙 _
  generalize AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual N) = S
    at hS pf4 pf5 ⊢
  subst hS
  exact CategoryTheory.IsIso.hom_inv_id
    (AlgebraicGeometry.Scheme.Modules.symPowπ (AlgebraicGeometry.Scheme.Modules.dual N) q)

/-- **Leaf (general fact at variable level).** A section of a finite biproduct decomposes into its components:
`x = Σ_q ι_q(π_q x)`.

    Proof: `CategoryTheory.Limits.biproduct.total : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙`; take sections over
    `U` and apply to `x`. One needs "a finite sum of morphisms acts on sections as the termwise sum": `Y.Modules` is
    preadditive and `f ↦ (f.val.app (op U)).hom x` is an additive group homomorphism (addition of `SheafOfModules.Hom`
    is defined pointwise through `.val`, `PresheafOfModules.add_app`), so use `map_sum`. Sections of a composite are
    the composite of the section maps (`comp_val`, `PresheafOfModules.comp_app`).
    Edge case: for an empty index set the biproduct is the zero object and `x = 0` is the empty sum. -/
theorem AlgebraicGeometry.Scheme.Modules.biproduct_section_eq_sum {Y : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (M : ι → Y.Modules) (U : Y.Opens)
    (x : ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op U) : Type u)) :
    x = ∑ q : ι, ((CategoryTheory.Limits.biproduct.ι M q).val.app (Opposite.op U)).hom
      (((CategoryTheory.Limits.biproduct.π M q).val.app (Opposite.op U)).hom x) := by
  -- "take sections over `U` and apply to `x`" is an additive group homomorphism; apply it to `biproduct.total`.
  let e : (CategoryTheory.Limits.biproduct M ⟶ CategoryTheory.Limits.biproduct M) →+
      ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op U) : Type u) :=
    { toFun := fun f => (f.val.app (Opposite.op U)).hom x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg e (CategoryTheory.Limits.biproduct.total (f := M))
  rw [map_sum] at h
  exact h.symm

/-! ## Variable level: three assembly lemmas in a monoidal category -/

section general

variable {C : Type*} [CategoryTheory.Category C] [CategoryTheory.MonoidalCategory C]

/-- If `χ_i` is a section of `σ_i` (`χ_i ≫ σ_i = 𝟙`), `σ_{mn}` is mono, and `mul ≫ σ_{mn} = (σ_m ⊗ σ_n) ≫ cat`, then
`(χ_m ⊗ χ_n) ≫ mul = cat ≫ χ_{mn}` (both sides followed by `σ_{mn}` are `cat`). -/
theorem AlgebraicGeometry.Scheme.tensorHom_comp_mul_eq_of_retract {Pm Pn Pmn Sm Sn Smn : C}
    (χm : Pm ⟶ Sm) (χn : Pn ⟶ Sn) (χmn : Pmn ⟶ Smn) (σm : Sm ⟶ Pm) (σn : Sn ⟶ Pn) (σmn : Smn ⟶ Pmn)
    [CategoryTheory.Mono σmn]
    (hm : χm ≫ σm = 𝟙 _) (hn : χn ≫ σn = 𝟙 _) (hmn : χmn ≫ σmn = 𝟙 _)
    (mul : Sm ⊗ Sn ⟶ Smn) (cat : Pm ⊗ Pn ⟶ Pmn) (hA : mul ≫ σmn = (σm ⊗ₘ σn) ≫ cat) :
    (χm ⊗ₘ χn) ≫ mul = cat ≫ χmn := by
  rw [← CategoryTheory.cancel_mono σmn, CategoryTheory.Category.assoc, hA, ← CategoryTheory.Category.assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, hm, hn,
    CategoryTheory.MonoidalCategory.id_tensorHom_id, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.assoc, hmn, CategoryTheory.Category.comp_id]

omit [CategoryTheory.MonoidalCategory C] in
/-- Two morphisms that become `𝟙` after the same monomorphism are equal. -/
theorem AlgebraicGeometry.Scheme.eq_of_comp_mono_eq_id {A B : C} (a b : A ⟶ B) (s : B ⟶ A)
    [CategoryTheory.Mono s] (ha : a ≫ s = 𝟙 A) (hb : b ≫ s = 𝟙 A) : a = b :=
  (CategoryTheory.cancel_mono s).1 (ha.trans hb.symm)

/-- Three compatibilities chained into one: `(f ⊗ g) ≫ cat = pm ≫ e`, `(χm ⊗ χn) ≫ mul = cat ≫ χmn` and
`(ιm ⊗ ιn) ≫ M = mul ≫ ιmn` imply `pm ≫ e ≫ χmn ≫ ιmn = ((f ≫ χm ≫ ιm) ⊗ (g ≫ χn ≫ ιn)) ≫ M`. -/
theorem AlgebraicGeometry.Scheme.pieceMul_assembly_aux {A B A' B' Q Q' Sm Sn Smn T : C}
    (f : A ⟶ A') (g : B ⟶ B') (pm : A ⊗ B ⟶ Q) (cat : A' ⊗ B' ⟶ Q') (e : Q ⟶ Q')
    (h1 : (f ⊗ₘ g) ≫ cat = pm ≫ e)
    (χm : A' ⟶ Sm) (χn : B' ⟶ Sn) (χmn : Q' ⟶ Smn) (mul : Sm ⊗ Sn ⟶ Smn)
    (h2 : (χm ⊗ₘ χn) ≫ mul = cat ≫ χmn)
    (ιm : Sm ⟶ T) (ιn : Sn ⟶ T) (ιmn : Smn ⟶ T) (M : T ⊗ T ⟶ T)
    (h3 : (ιm ⊗ₘ ιn) ≫ M = mul ≫ ιmn) :
    pm ≫ e ≫ χmn ≫ ιmn = ((f ≫ χm ≫ ιm) ⊗ₘ (g ≫ χn ≫ ιn)) ≫ M := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, CategoryTheory.Category.assoc,
    CategoryTheory.Category.assoc, h3, reassoc_of% h2, reassoc_of% h1]

end general

/-! ## Variable level: two translation lemmas to the level of sections -/

/-- A morphism-level equation `f ≫ Θ = (θM ⊗ θN) ≫ A.mul ≫ ψ` (`ψ` an algebra map) gives on sections the
multiplication formula `Θ(f(a ⊗ b)) = (θM ≫ ψ)(a) · (θN ≫ ψ)(b)`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.IsAlgebraMapToPushforward.app_mul_of_comp_eq
    {X T : AlgebraicGeometry.Scheme.{u}} {A : X.QCAlgebra} {g : T ⟶ X}
    {ψ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)}
    (hψ : A.IsAlgebraMapToPushforward g ψ) {M N P : X.Modules} (f : M ⊗ N ⟶ P)
    (Θ : P ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (θM : M ⟶ A.carrier) (θN : N ⟶ A.carrier)
    (ΘM : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (ΘN : N ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (h : f ≫ Θ = (θM ⊗ₘ θN) ≫ A.mul ≫ ψ) (hM : θM ≫ ψ = ΘM) (hN : θN ≫ ψ = ΘN)
    (V : X.Opens) (a : (M.val.obj (Opposite.op V) : Type u)) (b : (N.val.obj (Opposite.op V) : Type u)) :
    (show Γ(T, g ⁻¹ᵁ V) from (Θ.val.app (Opposite.op V)).hom
        ((f.val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections M N V a b))) =
      (show Γ(T, g ⁻¹ᵁ V) from (ΘM.val.app (Opposite.op V)).hom a) *
        (show Γ(T, g ⁻¹ᵁ V) from (ΘN.val.app (Opposite.op V)).hom b) := by
  subst hM hN
  have h1 := congrArg (fun φ : M ⊗ N ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf) =>
    (φ.val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections M N V a b)) h
  have h2 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections θM θN V a b
  have h3 := hψ.1 V ((θM.val.app (Opposite.op V)).hom a) ((θN.val.app (Opposite.op V)).hom b)
  refine h1.trans ?_
  show (ψ.val.app (Opposite.op V)).hom ((A.mul.val.app (Opposite.op V)).hom
      (((θM ⊗ₘ θN).val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections M N V a b))) = _
  rw [show ((θM ⊗ₘ θN).val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections M N V a b) =
    AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier V
      ((θM.val.app (Opposite.op V)).hom a) ((θN.val.app (Opposite.op V)).hom b) from h2]
  exact h3

/-- "Preserves multiplication" on a biproduct reduces to the components: if for all `p q`, `a ∈ M_p(V)`, `b ∈ M_q(V)`
we have `φ(mul(ι_p a ⊗ ι_q b)) = φ(ι_p a)·φ(ι_q b)`, then `φ(mul(x ⊗ y)) = φ(x)·φ(y)` for all `x y ∈ (⨁ M)(V)`
(`biproduct_section_eq_sum` + bilinearity of `tensorSections` + `Finset.sum_mul_sum`). -/
theorem AlgebraicGeometry.Scheme.Modules.isAlgebraMap_mul_of_pieces {X T : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ X) {ι : Type} [Fintype ι] (M : ι → X.Modules)
    (mul : CategoryTheory.Limits.biproduct M ⊗ CategoryTheory.Limits.biproduct M ⟶ CategoryTheory.Limits.biproduct M)
    (φ : CategoryTheory.Limits.biproduct M ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (V : X.Opens)
    (h : ∀ (p q : ι) (a : ((M p).val.obj (Opposite.op V) : Type u)) (b : ((M q).val.obj (Opposite.op V) : Type u)),
      (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom ((mul.val.app (Opposite.op V)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V
          (((CategoryTheory.Limits.biproduct.ι M p).val.app (Opposite.op V)).hom a)
          (((CategoryTheory.Limits.biproduct.ι M q).val.app (Opposite.op V)).hom b)))) =
      (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom
          (((CategoryTheory.Limits.biproduct.ι M p).val.app (Opposite.op V)).hom a)) *
        (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom
          (((CategoryTheory.Limits.biproduct.ι M q).val.app (Opposite.op V)).hom b)))
    (x y : ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op V) : Type u)) :
    (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom ((mul.val.app (Opposite.op V)).hom
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V x y))) =
      (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom x) *
        (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom y) := by
  -- bilinearity of `tensorSections` for finite sums, restated in the spelling of this statement (`ModuleCat` carrier)
  -- to avoid `rw` mismatches caused by different spellings of `Γ(A, U)`
  have hL : ∀ (a : ι → ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op V) : Type u))
      (b : ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op V) : Type u)),
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V (∑ j, a j) b =
        ∑ j, AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V (a j) b := fun a b =>
    map_sum (AddMonoidHom.mk' (fun a => AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.Limits.biproduct M) (CategoryTheory.Limits.biproduct M) V a b)
      (fun x y => AlgebraicGeometry.Scheme.Modules.tensorSections_add_left _ _ V x y b)) a Finset.univ
  have hR : ∀ (a : ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op V) : Type u))
      (b : ι → ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op V) : Type u)),
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V a (∑ j, b j) =
        ∑ j, AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V a (b j) := fun a b =>
    map_sum (AddMonoidHom.mk' (fun b => AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.Limits.biproduct M) (CategoryTheory.Limits.biproduct M) V a b)
      (fun x y => AlgebraicGeometry.Scheme.Modules.tensorSections_add_right _ _ V a x y)) b Finset.univ
  -- package "take sections over `V` and view them in `Γ(T, g⁻¹V)`" as an additive group homomorphism `Φ`; all
  -- subsequent rewriting happens on unwrapped terms
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ((CategoryTheory.Limits.biproduct M).val.obj (Opposite.op V) : Type u) →+ Γ(T, g ⁻¹ᵁ V),
      ∀ z, Φ z = (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom z) :=
    ⟨{ toFun := fun z => (show Γ(T, g ⁻¹ᵁ V) from (φ.val.app (Opposite.op V)).hom z)
       map_zero' := map_zero (φ.val.app (Opposite.op V)).hom
       map_add' := map_add (φ.val.app (Opposite.op V)).hom }, fun _ => rfl⟩
  have h' : ∀ (p q : ι) (a : ((M p).val.obj (Opposite.op V) : Type u)) (b : ((M q).val.obj (Opposite.op V) : Type u)),
      Φ ((mul.val.app (Opposite.op V)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V
          (((CategoryTheory.Limits.biproduct.ι M p).val.app (Opposite.op V)).hom a)
          (((CategoryTheory.Limits.biproduct.ι M q).val.app (Opposite.op V)).hom b))) =
        Φ (((CategoryTheory.Limits.biproduct.ι M p).val.app (Opposite.op V)).hom a) *
          Φ (((CategoryTheory.Limits.biproduct.ι M q).val.app (Opposite.op V)).hom b) := by
    intro p q a b
    rw [hΦ, hΦ, hΦ]
    exact h p q a b
  rw [← hΦ, ← hΦ, ← hΦ, AlgebraicGeometry.Scheme.Modules.biproduct_section_eq_sum M V x,
    AlgebraicGeometry.Scheme.Modules.biproduct_section_eq_sum M V y, hL, map_sum, map_sum, map_sum, map_sum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hR, map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => h' p q _ _

/-! ## Concrete level: a line bundle `N`, `D = N^∨`, `S = Sym D` -/

/-- `χ_q := powIso.hom ≫ tensorPowerToSymPart` is a section of `symPartToMonoidalPow`: `χ_q ≫ σ_q = 𝟙`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.powIso_tensorPowerToSymPart_symPartToMonoidalPow
    {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules) [N.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.dual N).IsLineBundle] (q : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) q).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N q) ≫
      AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) q = 𝟙 _ := by
  rw [CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_symPartToMonoidalPow_frameHomMulAux]
  exact CategoryTheory.Iso.hom_inv_id _

/-- Under `χ`, the multiplication of `Sym` corresponds to concatenation of tensor powers:
`(χ_p ⊗ χ_q) ≫ S.mul p q = monoidalPowCat p q ≫ χ_{p+q}` (the "inverse" of `Modules.mul_comp_symPartToMonoidalPow`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.tensorHom_powIso_tensorPowerToSymPart_comp_mul
    {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules) [N.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.dual N).IsLineBundle] (p q : ℕ) :
    (((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) p).hom ≫
          AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N p) ⊗ₘ
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) q).hom ≫
          AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N q)) ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual N)).mul p q =
      (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual N) p q).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) (p + q)).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N (p + q) := by
  have := AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_isIso (AlgebraicGeometry.Scheme.Modules.dual N) (p + q)
  exact AlgebraicGeometry.Scheme.tensorHom_comp_mul_eq_of_retract _ _ _
    (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) p)
    (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) q)
    (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) (p + q))
    (AlgebraicGeometry.Scheme.totalSpace.powIso_tensorPowerToSymPart_symPartToMonoidalPow N p)
    (AlgebraicGeometry.Scheme.totalSpace.powIso_tensorPowerToSymPart_symPartToMonoidalPow N q)
    (AlgebraicGeometry.Scheme.totalSpace.powIso_tensorPowerToSymPart_symPartToMonoidalPow N (p + q))
    _ _ (AlgebraicGeometry.Scheme.Modules.mul_comp_symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) p q)

/-- Weight-`0` piece: `χ_0 = S.one` (both become `𝟙` after `σ_0`: `powIso_tensorPowerToSymPart_symPartToMonoidalPow`,
`Modules.one_comp_symPartToMonoidalPow`). `monoidalPow D 0` and `𝟙_` are definitionally equal. -/
theorem AlgebraicGeometry.Scheme.totalSpace.powIso_zero_comp_tensorPowerToSymPart_zero
    {Y : AlgebraicGeometry.Scheme.{u}} (N : Y.Modules) [N.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.dual N).IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower (AlgebraicGeometry.Scheme.Modules.dual N) 0).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart N 0 =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual N)).one := by
  have := AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_isIso (AlgebraicGeometry.Scheme.Modules.dual N) 0
  exact AlgebraicGeometry.Scheme.eq_of_comp_mono_eq_id _ _
    (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N) 0)
    (AlgebraicGeometry.Scheme.totalSpace.powIso_tensorPowerToSymPart_symPartToMonoidalPow N 0)
    (AlgebraicGeometry.Scheme.Modules.one_comp_symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual N))

/-- **The morphism-level form of `frameHom_pieceMul`**: with
`θ'_n := pieceIso n ≫ powIso n ≫ tensorPowerToSymPart n ≫ totalIncl n : piece n ⟶ ⊕ Sym`,
`pieceMul p q ≫ θ'_{p+q} = (θ'_p ⊗ θ'_q) ≫ S.total.mul`
(`pieceIso_mul` + `tensorHom_powIso_tensorPowerToSymPart_comp_mul` + `tensor_ι_comp_totalMul`). -/
theorem truncatedJetAlgebra.pieceMul_comp_frameHomCore {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (p q : ℕ) :
    truncatedJetAlgebra.pieceMul L p q ≫ (truncatedJetAlgebra.pieceIso L (p + q)).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (p + q)).hom ≫
        AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (p + q) ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (p + q) =
      (((truncatedJetAlgebra.pieceIso L p).hom ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p).hom ≫
          AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules p ≫
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl p) ⊗ₘ
        ((truncatedJetAlgebra.pieceIso L q).hom ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom ≫
          AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q ≫
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q)) ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total.mul := by
  have h := AlgebraicGeometry.Scheme.pieceMul_assembly_aux (truncatedJetAlgebra.pieceIso L p).hom
    (truncatedJetAlgebra.pieceIso L q).hom (truncatedJetAlgebra.pieceMul L p q)
    (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p q).hom
    (truncatedJetAlgebra.pieceIso L (p + q)).hom (truncatedJetAlgebra.pieceIso_mul L p q)
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) p).hom ≫
      AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules p)
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom ≫
      AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules q)
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) (p + q)).hom ≫
      AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart L.toModules (p + q))
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).mul p q)
    (AlgebraicGeometry.Scheme.totalSpace.tensorHom_powIso_tensorPowerToSymPart_comp_mul L.toModules p q)
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl p)
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl q)
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl (p + q))
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total.mul
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.tensor_ι_comp_totalMul
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) p q)
  simpa only [CategoryTheory.Category.assoc] using h

end
