import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ConeMorphismScaleOfCoordinatesHelpers

/-! # The twist isomorphism on the punctured cone

`θ : g^*pr₂^*O_X(1) ≅ g^*pr₁^*A` (`g = Z^× → C ×_k X`), sending `g^*pr₂^*(e^*x_i)` to `z_i` (transported to
`Γ(Z^×, g^*pr₁^*A)`, i.e. `coordOverProduct`). This is the transport of the Stacks 01NE identification
"the pullback of `O(1)` is the given line bundle" (`projectivizationMorphism_pullback_twist`) along
`φ = Φ ≫ e.emb`, `Φ = g ≫ pr₂`, `t = g ≫ pr₁`.

Source: eq. (2.1) of the paper ("a nonzero vector determines a point of `X`");
Stacks 01NE. The seven-step chain is done once at the variable level
(`exists_pullback_twistIso_of_factor`), a bridge form (`…_of_factor_of_eq`) makes its instance syntactically the
concrete statement, and the concrete right-hand side enters only through the definitional equation
`puncturedConeToProduct.coordOverProduct.eq_1`. The single dependency on an auto-generated constant
(`conePuncturedLineBundle.eval._proof_1`, the proof-abstracted `HasPullback` instance inside the value of
`coordOverProduct`) is explained in the docstring of `exists_twistIso`; if the Contract module changes and
that name changes, replace it by the new name of the same abstracted instance (`#check @conePuncturedLineBundle.eval._proof_1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Seven isomorphisms of modules and, for each index `i`, a chain of seven pointwise equalities on global
sections give an isomorphism `M₁ ≅ M₈` sending `x₁ i` to `x₈ i` (namely the composite). Stated for abstract
isomorphisms so that the unfolding of `≪≫` and `≫` on sections happens on small terms. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_iso_of_seven_chain {W : AlgebraicGeometry.Scheme.{u}}
    {M₁ M₂ M₃ M₄ M₅ M₆ M₇ M₈ : W.Modules} {ι : Type*}
    (I₁ : M₁ ≅ M₂) (I₂ : M₂ ≅ M₃) (I₃ : M₃ ≅ M₄) (I₄ : M₄ ≅ M₅) (I₅ : M₅ ≅ M₆) (I₆ : M₆ ≅ M₇) (I₇ : M₇ ≅ M₈)
    {x₁ : ι → (M₁.val.obj (Opposite.op ⊤) : Type u)} {x₂ : ι → (M₂.val.obj (Opposite.op ⊤) : Type u)}
    {x₃ : ι → (M₃.val.obj (Opposite.op ⊤) : Type u)} {x₄ : ι → (M₄.val.obj (Opposite.op ⊤) : Type u)}
    {x₅ : ι → (M₅.val.obj (Opposite.op ⊤) : Type u)} {x₆ : ι → (M₆.val.obj (Opposite.op ⊤) : Type u)}
    {x₇ : ι → (M₇.val.obj (Opposite.op ⊤) : Type u)} {x₈ : ι → (M₈.val.obj (Opposite.op ⊤) : Type u)}
    (h₁ : ∀ i, ((I₁.hom.val.app (Opposite.op ⊤)).hom (x₁ i)) = x₂ i)
    (h₂ : ∀ i, ((I₂.hom.val.app (Opposite.op ⊤)).hom (x₂ i)) = x₃ i)
    (h₃ : ∀ i, ((I₃.hom.val.app (Opposite.op ⊤)).hom (x₃ i)) = x₄ i)
    (h₄ : ∀ i, ((I₄.hom.val.app (Opposite.op ⊤)).hom (x₄ i)) = x₅ i)
    (h₅ : ∀ i, ((I₅.hom.val.app (Opposite.op ⊤)).hom (x₅ i)) = x₆ i)
    (h₆ : ∀ i, ((I₆.hom.val.app (Opposite.op ⊤)).hom (x₆ i)) = x₇ i)
    (h₇ : ∀ i, ((I₇.hom.val.app (Opposite.op ⊤)).hom (x₇ i)) = x₈ i) :
    ∃ ψ : M₁ ≅ M₈, ∀ i, ((ψ.hom.val.app (Opposite.op ⊤)).hom (x₁ i)) = x₈ i := by
  refine ⟨I₁ ≪≫ I₂ ≪≫ I₃ ≪≫ I₄ ≪≫ I₅ ≪≫ I₆ ≪≫ I₇, fun i => ?_⟩
  rw [← h₇ i, ← h₆ i, ← h₅ i, ← h₄ i, ← h₃ i, ← h₂ i, ← h₁ i]
  rfl

/-- Mixed-spelling variant of `exists_iso_of_seven_chain`: the first four section identities are spelled with
`.val.app (op ⊤)).hom` (as `sectionPullbackAlong_comp`/`_congr` are), the last three with `Hom.app _ ⊤` (as
`projectivizationMorphism_pullback_twist` and the body of `puncturedConeToProduct.coordOverProduct` are); the
endpoints `M₁`, `M₈`, `x₁`, `x₈` are explicit so that the caller fixes them in the goal's own spelling and the
final `exact` is syntactic. All conversions between the two spellings happen here, on abstract modules. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_iso_of_seven_chain' {W : AlgebraicGeometry.Scheme.{u}}
    (M₁ M₈ : W.Modules) {M₂ M₃ M₄ M₅ M₆ M₇ : W.Modules} {ι : Type*}
    (I₁ : M₁ ≅ M₂) (I₂ : M₂ ≅ M₃) (I₃ : M₃ ≅ M₄) (I₄ : M₄ ≅ M₅) (I₅ : M₅ ≅ M₆) (I₆ : M₆ ≅ M₇) (I₇ : M₇ ≅ M₈)
    (x₁ : ι → (M₁.val.obj (Opposite.op ⊤) : Type u)) (x₈ : ι → (M₈.val.obj (Opposite.op ⊤) : Type u))
    {x₂ : ι → (M₂.val.obj (Opposite.op ⊤) : Type u)} {x₃ : ι → (M₃.val.obj (Opposite.op ⊤) : Type u)}
    {x₄ : ι → (M₄.val.obj (Opposite.op ⊤) : Type u)} {x₅ : ι → (M₅.val.obj (Opposite.op ⊤) : Type u)}
    {x₆ : ι → (M₆.val.obj (Opposite.op ⊤) : Type u)} {x₇ : ι → (M₇.val.obj (Opposite.op ⊤) : Type u)}
    (h₁ : ∀ i, ((I₁.hom.val.app (Opposite.op ⊤)).hom (x₁ i)) = x₂ i)
    (h₂ : ∀ i, ((I₂.hom.val.app (Opposite.op ⊤)).hom (x₂ i)) = x₃ i)
    (h₃ : ∀ i, ((I₃.hom.val.app (Opposite.op ⊤)).hom (x₃ i)) = x₄ i)
    (h₄ : ∀ i, ((I₄.hom.val.app (Opposite.op ⊤)).hom (x₄ i)) = x₅ i)
    (h₅ : ∀ i, (I₅.hom.app ⊤) (x₅ i) = x₆ i)
    (h₆ : ∀ i, (I₆.hom.app ⊤) (x₆ i) = x₇ i)
    (h₇ : ∀ i, (I₇.hom.app ⊤) (x₇ i) = x₈ i) :
    ∃ ψ : M₁ ≅ M₈, ∀ i, ((ψ.hom.val.app (Opposite.op ⊤)).hom (x₁ i)) = x₈ i := by
  refine ⟨I₁ ≪≫ I₂ ≪≫ I₃ ≪≫ I₄ ≪≫ I₅ ≪≫ I₆ ≪≫ I₇, fun i => ?_⟩
  rw [← h₇ i, ← h₆ i, ← h₅ i, ← h₄ i, ← h₃ i, ← h₂ i, ← h₁ i]
  rfl


/-- **Variable-level core of `exists_twistIso`.** Given the factorizations `t = g ≫ pr₁`, `g ≫ pr₂ = Φ`,
`Φ ≫ emb = φ` and an isomorphism `θ : φ^*O ≅ t^*A` sending `φ^*(x i)` to `z i`, there is an isomorphism
`ψ : g^*pr₂^*emb^*O ≅ g^*pr₁^*A` sending `g^*pr₂^*(emb^*(x i))` (with `emb^*(x i)` spelled as
`pullbackOn emb (x i) ⊤`) to `z i` transported by `pullbackCongr`/`pullbackComp`
(the spelling of `puncturedConeToProduct.coordOverProduct`). Proof: `ψ` is the seven-step composite
`pullbackComp g pr₂ ≪≫ pullbackCongr hsnd ≪≫ pullbackComp Φ emb ≪≫ pullbackCongr hfac ≪≫ θ ≪≫ pullbackCongr hfst ≪≫
(pullbackComp g pr₁)⁻¹`, and the section identities are `sectionPullbackAlong_comp`, `sectionPullbackAlong_congr`,
`pullbackOn_top`, `hθ`, and two `rfl`s, assembled by `exists_iso_of_seven_chain'`. Everything is
stated for variables (schemes, morphisms, modules), so no concrete pullback functor is ever unfolded.
Source: Stacks 01NE (bookkeeping around "pullback of `O(1)` is the given line
bundle"); eq. (2.1) of the paper. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_pullback_twistIso_of_factor
    {W P C X PN : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ P) (pr₁ : P ⟶ C) (pr₂ : P ⟶ X) (t : W ⟶ C) (Φ : W ⟶ X) (emb : X ⟶ PN) (φ : W ⟶ PN)
    (hfst : t = g ≫ pr₁) (hsnd : g ≫ pr₂ = Φ) (hfac : Φ ≫ emb = φ)
    {O : PN.Modules} {A : C.Modules} {ι : Type*}
    (x : ι → (O.val.obj (Opposite.op ⊤) : Type u))
    (z : ι → (((AlgebraicGeometry.Scheme.Modules.pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj O ≅
      (AlgebraicGeometry.Scheme.Modules.pullback t).obj A)
    (hθ : ∀ i, θ.hom.app ⊤ (sectionPullbackAlong φ (x i)) = z i) :
    ∃ ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback pr₂).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback emb).obj O)) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback g).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback pr₁).obj A),
      ∀ i, ((ψ.hom.val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong g
            (sectionPullbackAlong pr₂ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn emb (x i) ⊤)))) =
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp g pr₁).inv.app A).app ⊤
          (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hfst).hom.app A).app ⊤ (z i)) := by
  refine AlgebraicGeometry.Scheme.Modules.exists_iso_of_seven_chain' _ _
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp g pr₂).app _)
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hsnd).app _)
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp Φ emb).app O)
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hfac).app O)
    θ
    ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hfst).app A)
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp g pr₁).app A).symm
    _ _
    (x₂ := fun i => sectionPullbackAlong (g ≫ pr₂) (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn emb (x i) ⊤))
    (x₃ := fun i => sectionPullbackAlong Φ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn emb (x i) ⊤))
    (x₄ := fun i => sectionPullbackAlong (Φ ≫ emb) (x i))
    (x₅ := fun i => sectionPullbackAlong φ (x i))
    (x₆ := z)
    (x₇ := fun i =>
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hfst).hom.app A).app ⊤ (z i))
    (fun i => sectionPullbackAlong_comp g pr₂ _)
    (fun i => sectionPullbackAlong_congr hsnd _)
    (fun i => ?_)
    (fun i => sectionPullbackAlong_congr hfac _)
    hθ
    (fun i => rfl)
    (fun i => rfl)
  have hx : AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn emb (x i) ⊤ = sectionPullbackAlong emb (x i) :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn_top emb (x i)
  exact (congrArg (fun y => (((AlgebraicGeometry.Scheme.Modules.pullbackComp Φ emb).app O).hom.val.app
      (Opposite.op ⊤)).hom (sectionPullbackAlong Φ y)) hx).trans (sectionPullbackAlong_comp Φ emb (x i))


/-- **Bridge form of `exists_pullback_twistIso_of_factor`.** The concrete sections enter
through the variables `a`, `b` and the equations `ha`, `hb`, and the target module through `Q`/`hQ`, so that the
instance of this lemma is *syntactically* the concrete statement and the kernel never compares two spellings of a
section under `DFunLike.coe` (that comparison unfolds `Scheme.Modules.pullbackComp`/`pullbackCongr` completely and
does not finish in 60 s; see the docstring of `exists_twistIso`).

Argument order matters: `hb` is the **first explicit argument**, and `g`, `P`, `pr₁`, `t`, `hfst`, `z` are implicit,
so that in the concrete use they are all fixed by unification with the right-hand side of the definitional equation
`puncturedConeToProduct.coordOverProduct.eq_1` — i.e. with the *value* of `coordOverProduct`, whose `HasPullback`
instances and equation proof are the proof-abstracted constants `conePuncturedLineBundle.eval._proof_1` /
`coordOverProduct._proof_1`, not the instances of the declared types. (If `g` or `b` were explicit, their declared
types would fix `P`, `pr₁` with the direct instance `instHasPullback`, and the kernel check of `hb` would be the
catastrophic one.) `Q` is decoupled from `pr₁` for the same reason; `hQ` is `rfl` and only compares modules. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_pullback_twistIso_of_factor_of_eq
    {W P C X PN : AlgebraicGeometry.Scheme.{u}} {g : W ⟶ P} {pr₁ : P ⟶ C} {t : W ⟶ C}
    {hfst : t = g ≫ pr₁} {A : C.Modules} {ι : Type*}
    {z : ι → (((AlgebraicGeometry.Scheme.Modules.pullback t).obj A).val.obj (Opposite.op ⊤) : Type u)}
    {Q : W.Modules} {b : ι → (Q.val.obj (Opposite.op ⊤) : Type u)}
    (hb : ∀ i, HEq (b i) (((AlgebraicGeometry.Scheme.Modules.pullbackComp g pr₁).inv.app A).app ⊤
          (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hfst).hom.app A).app ⊤ (z i))))
    (pr₂ : P ⟶ X) (Φ : W ⟶ X) (emb : X ⟶ PN) (φ : W ⟶ PN) (hsnd : g ≫ pr₂ = Φ) (hfac : Φ ≫ emb = φ)
    {O : PN.Modules} (x : ι → (O.val.obj (Opposite.op ⊤) : Type u))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj O ≅
      (AlgebraicGeometry.Scheme.Modules.pullback t).obj A)
    (hθ : ∀ i, θ.hom.app ⊤ (sectionPullbackAlong φ (x i)) = z i)
    (a : ι → ((((AlgebraicGeometry.Scheme.Modules.pullback g).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback pr₂).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback emb).obj O))).val.obj (Opposite.op ⊤)) : Type u))
    (ha : ∀ i, a i = sectionPullbackAlong g
      (sectionPullbackAlong pr₂ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn emb (x i) ⊤)))
    (hQ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback pr₁).obj A) = Q) :
    ∃ ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback pr₂).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback emb).obj O)) ≅ Q,
      ∀ i, ((ψ.hom.val.app (Opposite.op ⊤)).hom (a i)) = b i := by
  subst hQ
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.Scheme.Modules.exists_pullback_twistIso_of_factor
    g pr₁ pr₂ t Φ emb φ hfst hsnd hfac x z θ hθ
  refine ⟨ψ, fun i => ?_⟩
  rw [ha i, eq_of_heq (hb i)]
  exact hψ i

set_option linter.auxLemma false in
/-- There is `θ : g^*pr₂^*O_X(1) ≅ g^*pr₁^*A` with `θ(g^*pr₂^*(e^*x_i)) = z_i` (`coordOverProduct`).

Source: eq. (2.1) of the paper ("a nonzero vector determines a point of `X`");
Stacks 01NE (`projectivizationMorphism_pullback_twist`).

Proof:
1. `projectivizationMorphism_pullback_twist` gives `θ₀ : φ^*O(1) ≅ t^*A` with `θ₀(φ^*x_i) = z_i` (`hθ`);
   `φ = Φ ≫ e.emb` (`IsClosedImmersion.lift_fac`, `hfac`), `Φ = g ≫ pr₂` (`pullback.lift_snd`, `hsnd`),
   `t = g ≫ pr₁` (`comp_fst`; it enters the proof as the proof constant abstracted from the body of
   `coordOverProduct`, see step 3).
2. The seven-step chain `ψ = pullbackComp g pr₂ ≪≫ pullbackCongr hsnd ≪≫ pullbackComp Φ emb ≪≫ pullbackCongr hfac ≪≫ θ₀ ≪≫
   pullbackCongr hfst ≪≫ (pullbackComp g pr₁)⁻¹` and the section identities (`sectionPullbackAlong_comp`/`_congr`,
   `pullbackOn_top`, `hθ`, two `rfl`s) are all done at the **variable level**:
   `exists_pullback_twistIso_of_factor` (assembled with `exists_iso_of_seven_chain'`).
3. The concrete statement is reached only through the bridge lemma `exists_pullback_twistIso_of_factor_of_eq`: the
   left-hand sections `a_i = g^*(coordinate C e i)` enter by `ha := rfl` (unfolding only the regular definitions
   `coordinate`/`coordinateSection`, cheap for the kernel), the right-hand sections `b_i = coordOverProduct e E A hdeg i`
   enter through the **definitional equation `coordOverProduct.eq_1`**, and the target module `Q` by `hQ := rfl`
   (comparing only modules).

**Why it must be written this way.** The bottleneck is not the elaborator (with `debug.skipKernelTC` the whole file
elaborates in about 19 s) but the **kernel**. In the **body** of `coordOverProduct` every instance
`HasPullback (C ↘ Spec k) (X ↘ Spec k)` has been replaced by Lean's `abstractNestedProofs` with the constant
`conePuncturedLineBundle.eval._proof_1` (67 occurrences, including the instance in the fiber product scheme `P`
itself), and `(comp_fst …).symm` with `coordOverProduct._proof_1`; the same terms written directly in statements and
proofs use `instHasPullback`. The two are equal by proof irrelevance, but the difference sits under
`DFunLike.coe`/`Hom.app`/`Iso.inv` (abbreviations/projections), where the kernel's "same head, compare arguments
first" shortcut applies only to regular definitions, so it unfolds `pullbackComp`/`pullbackCongr` completely — every
`rfl` of the form `coordOverProduct … i = <re-spelled body>` takes more than 60 s. Hence the right-hand side can only
enter through `eq_1`, and after instantiating the bridge lemma its right-hand side must be **verbatim** that of
`eq_1`: `pr₁`, `hfst` are obtained by unifying `hb` (`hb` is the first explicit argument; `g`/`pr₁`/`t`/`hfst`/`z`/`b`
are implicit), while `P` (the fiber product scheme) cannot be obtained by unification — assigning `?g := g` would
fix `P` to the `instHasPullback` version through the declared type of `g` — so `P` is given explicitly as
`@pullback … (conePuncturedLineBundle.eval._proof_1 C)` (the only reference to an auto-generated constant in this
file; `linter.auxLemma` is switched off on that line). The remaining reconciliations (the domain of the `Iso`,
`twistOne ↔ e.emb^*O(1)`; the `P`/`pr₁` instance differences at the level of modules; the `coe` of the variable
`ψ`) are cheap for the kernel. Note that the automatic `rfl` after `rw` closes `body = right-hand side of the lemma`
at reducible transparency, but that is the elaborator; the kernel does not accept it. -/
theorem puncturedConeToProduct.exists_twistIso {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    ∃ ψ : (AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct e E A hdeg)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
              (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
            (e.oX 1)) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct e E A hdeg)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
              (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A),
      ∀ i : Fin (N + 1),
        ((ψ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (puncturedConeToProduct e E A hdeg)
            (conePuncturedLineBundle.coordinate C e i))) =
          puncturedConeToProduct.coordOverProduct e E A hdeg i := by
  let _ := puncturedConeToProduct.overK e E A hdeg
  have hsnd : puncturedConeToProduct e E A hdeg ≫
      CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) = puncturedConeToProduct.toX e E A hdeg := by
    unfold puncturedConeToProduct
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hfac : puncturedConeToProduct.toX e E A hdeg ≫ e.emb =
      projectivizationMorphism (k := k)
        ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)
        (puncturedConeToProduct.coord e E A hdeg) (puncturedConeToProduct.coord_nowhereZero e E A hdeg) :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := projectivizationMorphism_pullback_twist (k := k)
    ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)
    (puncturedConeToProduct.coord e E A hdeg) (puncturedConeToProduct.coord_nowhereZero e E A hdeg)
  have hb0 := fun i : Fin (N + 1) => heq_of_eq (puncturedConeToProduct.coordOverProduct.eq_1 e E A hdeg i)
  have key := AlgebraicGeometry.Scheme.Modules.exists_pullback_twistIso_of_factor_of_eq
    (P := (@CategoryTheory.Limits.pullback _ _ _ _ _ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (conePuncturedLineBundle.eval._proof_1 C)))
    hb0
    (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (puncturedConeToProduct.toX e E A hdeg) e.emb _ hsnd hfac (projectiveSpaceCoordinate k N) θ hθ
    (fun i => sectionPullbackAlong (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle.coordinate C e i))
    -- `conePuncturedLineBundle.coordinate` is spelled with `sectionPullbackAlong e.emb _`, while the
    -- signature of the twist isomorphism expects `pullbackOn e.emb _ top`; bridge via `pullbackOn_top`.
    (fun i => by
      exact congrArg _ (congrArg _
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackOn_top (M := projectiveSpaceTwist k N 1)
          e.emb (projectiveSpaceCoordinate k N i)).symm)) rfl
  exact key

end
