import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAssemblyExists
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAssemblyUniqueTheorem
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Twist families on the pieces of `relativeProj.lift`

The framework for `relativeProj.lift_inducedBy` (`RelativeProjLiftEvaluation.lean`, part (a)): `Ψ_m`,
transported along `(τ ≫ π)^* ≅ g^*`, is induced by
`τ = relativeProj.lift S g M D`.

## Route (Stacks 01O4 (2), 01MN, 01NR, 01MO; chosen to avoid every chart change)

Write `τ := lift S f M D`, `π := (relativeProj S).hom`, `O(n) := relativeProj.twist S n`,
`α_n := (pullbackComp τ π).inv.app S_n ≫ τ^*(evaluation S n) : (τ≫π)^*S_n ⟶ τ^*O(n)` (`LiftData.evalHom`),
`β_n := (pullbackCongr lift_hom).hom.app S_n ≫ Ψ_n : (τ≫π)^*S_n ⟶ M^{⊗n}` (`LiftData.dataHom`),
`μ_{ab} : τ^*O(a) ⊗ τ^*O(b) ⟶ τ^*O(a+b)` the pulled-back twist multiplication (`LiftData.twistMulHom`).

A **twist family over an open `V ⊆ T`** (`LiftData.IsTwistFamilyOn`) is a family
`ψ_n : (τ^*O(n))|_{V₀} ⟶ (M^{⊗n})|_{V₀}`, `n : ℕ`, whose section maps over every open `A ≤ V` satisfy
(F) `ψ_n ∘ α_n = β_n` and (M) `ψ_{a+b}(μ_{ab}(x ⊗ y)) = ψ_a(x) ⊗ ψ_b(y)` (via `monoidalPowCat`).
The point of asking for *all* degrees and multiplicativity is that these two chart-free conditions pin the family
down (01O4: "up to strict equivalence") — so families built on different pieces of `lift`, with different affine
charts `W` of `X` and different trivializations `e` of `M`, agree on overlaps **without ever comparing two charts**:

1. `exists_lift_restrict`: every `t : T` lies in a piece `V' ∋ t` (affine, `V' ≤ U ⊓ f⁻¹W`) with
   `V'.ι ≫ lift = liftLocal S f M D U e W V' hV' hle` — the piece chosen inside the definition of `lift`.
2. `exists_twistFamily_of_piece` (**E**): on such a piece a twist family exists — the transport of the
   canonical family `φ^*O_{Proj A(W)}(n) → O_{V'}`, `a/s^k ↦ Φ(a)Φ(s)^{-k}`, for `φ = Proj.fromOfGlobalSections Φ`
   (Stacks 01O4 (2)).
3. `twistFamily_sectionMap_unique` (**U**): over an open `V` of a piece, any two twist families have
   the same section maps in every degree (01MN: `O(n)` is generated over `D₊(s)` by the fractions `a/s^k`, and
   `(a/s^k)·(s/1)^k = a/1` forces `ψ_n(a/s^k) ⊗ Ψ(s)^{⊗k} = Ψ(a)`, where `Ψ(s)` is a frame of `M^{⊗d}` on
   `τ⁻¹D₊(s)`).
4. Assembly (`lift_inducedBy`, from 1–3): choose a family per piece, the degree-`m` members agree on
   overlaps by 3 (`IsTwistFamilyOn.mono`), glue them with `Modules.exists_hom_of_sectionMap_agree`
   (`ModulesHomGlue.lean`), and check `α_m ≫ ψ = β_m` locally on the cover with (F).

## E and U are assembled from the absolute statements

Both are reduced to the **absolute** Stacks 01O4 (2) for `Proj.fromOfGlobalSections`
(`RelativeProjLiftEvaluationTwistFamilyAbsolute.lean`: `Proj.TwistFamily.exists_homFamily` (AE) and
`Proj.TwistFamily.IsSectionFamily.eq` (AU)) through the transport dictionary of
`RelativeProjLiftEvaluationTwistFamilyTransport.lean` (`twistTransport` `Θ_n`, `powTriv` `Λ_n`, four dictionary leaves
`twistTransport_evalHom`, `powTriv_dataHom`, `twistTransport_twistMulHom`, `powTriv_monoidalPowCat`; the generation
statement `span_range_pullbackSectionsOn_eq_top`). The assembly itself is in
`RelativeProjLiftEvaluationTwistFamilyAssembly*.lean` (`familyOfAbs`, `keyF`, `keyM`, `toSectionFamily`), stated with
definitionally equal working copies `evalHomAux`/`dataHomAux`/`twistMulHomAux`/`IsTwistFamilyOnAux` of the morphisms
below (this module cannot be imported there), and transferred here by `exact`.

Downstream only ever uses degree `m` (`PolarizationPullback.lean`, `ProjQuotientGivesLineBundle.lean`); the other
degrees are auxiliary. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **`lift` agrees with the piece chosen in its definition.** For every `t : T` there are an open `U ∋ t`
trivializing `M`, an affine open `W ∋ f t`, and an affine open `V' ∋ t` with `V' ≤ U ⊓ f⁻¹W`, such that
`V'.ι ≫ relativeProj.lift S f M D = relativeProj.liftLocal S f M D U e W V' hV' hle`.
Proof: `lift` is `Cover.glueMorphisms` over the cover `{V_t}`; `Cover.ι_glueMorphisms`
(same script as `projBundle.exists_lift_restrict`, `TotLineAffineOverBaseLiftRestrict.lean`). -/
theorem exists_lift_restrict (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (t : T) :
    ∃ (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
      (W : X.affineOpens) (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V')
      (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1),
      t ∈ V' ∧
        V'.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
          AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle := by
  let hU := fun t : T => SheafOfModules.IsLineBundle.locally_trivial (M := M) t
  let U : T → T.Opens := fun t => (hU t).choose
  let e : ∀ t, M.restrict (U t).ι ≅ SheafOfModules.unit (U t).toScheme.ringCatSheaf :=
    fun t => (hU t).choose_spec.snd.some
  let hW := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base t) (U := ⊤) trivial
  let W : T → X.affineOpens := fun t => ⟨(hW t).choose, (hW t).choose_spec.1⟩
  let hA := fun t : T =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t) (U := U t ⊓ f ⁻¹ᵁ (W t).1)
      ⟨(hU t).choose_spec.fst, (hW t).choose_spec.2.1⟩
  let Vt : T → T.Opens := fun t => (hA t).choose
  have hVt : ∀ t, AlgebraicGeometry.IsAffineOpen (Vt t) := fun t => (hA t).choose_spec.1
  have hle : ∀ t, Vt t ≤ U t ⊓ f ⁻¹ᵁ (W t).1 := fun t => (hA t).choose_spec.2.2
  have hcov : TopologicalSpace.IsOpenCover Vt := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, (hA t).choose_spec.2.1⟩
  refine ⟨U t, e t, W t, Vt t, hVt t, hle t, (hA t).choose_spec.2.1, ?_⟩
  exact (T.openCoverOfIsOpenCover Vt hcov).ι_glueMorphisms
    (fun t => AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D (U t) (e t) (W t) (Vt t) (hVt t) (hle t))
    (fun s t => AlgebraicGeometry.Scheme.relativeProj.liftLocal_compat S f M D
      (U s) (e s) (W s) (Vt s) (hVt s) (hle s) (U t) (e t) (W t) (Vt t) (hVt t) (hle t)) t

namespace LiftData

variable {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules} [M.IsLineBundle]
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

/-- `α_n := (pullbackComp τ π).inv.app S_n ≫ τ^*(evaluation S n) : (τ ≫ π)^* S_n ⟶ τ^* O(n)`, with
`τ = relativeProj.lift S f M D`. -/
def evalHom (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
        (S.part n) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ)) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
      (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app (S.part n) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
      (AlgebraicGeometry.Scheme.relativeProj.evaluation S n)

/-- `β_n := (pullbackCongr lift_hom).hom.app S_n ≫ Ψ_n : (τ ≫ π)^* S_n ⟶ M^{⊗n}`. -/
def dataHom (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
        (S.part n) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow M n :=
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (AlgebraicGeometry.Scheme.relativeProj.lift_hom S f M D)).hom.app (S.part n) ≫ D.Ψ n

/-- `μ_{a b} : τ^*O(a) ⊗ τ^*O(b) ⟶ τ^*O(a+b)`: the comparison isomorphism `δ⁻¹` of the (strong monoidal)
pullback followed by `τ^*` of the relative twist multiplication `twistMul S a b` (Stacks 01MO / 01NO). -/
def twistMulHom (a b : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) ⊗
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S ((a + b : ℕ) : ℤ)) :=
  CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
      (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)
      (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
      (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).map
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ))
          (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ))).inv ≫
        AlgebraicGeometry.Scheme.relativeProj.twistMul S (a : ℤ) (b : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (Nat.cast_add a b).symm))

/-- **Twist family on an open `V ≤ V₀`.** A family `ψ_n : (τ^*O(n))|_{V₀} ⟶ (M^{⊗n})|_{V₀}` (all `n : ℕ`) is a
*twist family over `V`* if, on every open `A ≤ V`, its section maps satisfy
* (F) the factorization `ψ_n ∘ α_n = β_n` (`evalHom`, `dataHom`), and
* (M) multiplicativity `ψ_{a+b}(μ_{ab}(x ⊗ y)) = monoidalPowCat(ψ_a x ⊗ ψ_b y)` (`twistMulHom`,
  `tensorSections`, `monoidalPowCat`).
Only section maps over opens `A ≤ V` are involved, so the predicate is monotone in `V` (`IsTwistFamilyOn.mono`)
and needs no restriction functor. -/
def IsTwistFamilyOn (V₀ : T.Opens)
    (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₀.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₀.ι)
    (V : T.Opens) (hV : V ≤ V₀) : Prop :=
  (∀ (n : ℕ) (A : T.Opens) (hA : A ≤ V)
      (s : Γ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.lift S f M D ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
          (S.part n), A)),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ n) A (hA.trans hV) ((D.evalHom n).app A s) =
        (D.dataHom n).app A s) ∧
  (∀ (a b : ℕ) (A : T.Opens) (hA : A ≤ V)
      (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)), A))
      (y : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)), A)),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ (a + b)) A (hA.trans hV)
          ((D.twistMulHom a b).app A (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A x y)) =
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom.app A
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A
            (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ a) A (hA.trans hV) x)
            (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ b) A (hA.trans hV) y)))

/-- The predicate only quantifies over opens `A ≤ V`, so it is monotone in `V`. -/
theorem IsTwistFamilyOn.mono {V₀ : T.Opens}
    {ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₀.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₀.ι}
    {V : T.Opens} {hV : V ≤ V₀} (H : D.IsTwistFamilyOn V₀ ψ V hV) {V' : T.Opens} (h : V' ≤ V) :
    D.IsTwistFamilyOn V₀ ψ V' (h.trans hV) :=
  ⟨fun n A hA s => H.1 n A (hA.trans h) s, fun a b A hA x y => H.2 a b A (hA.trans h) x y⟩

/-- **(E) Existence of a twist family on a piece of `lift`** (Stacks 01O4 (2): for the morphism `r : T → Proj_X S`
attached to `(L, ψ)` one has `r^*O(n) ≅ L^{⊗n}` compatibly with the multiplication maps and with `ψ`; 01MN, 01NQ,
01NR, 01MO).

**Setting.** `A := S.sectionsRing W = ⊕_n Γ(W, S_n)` with grading `𝒜 := S.sectionsGrading W`;
`Φ := (T.homOfLE hle).appTop ∘ liftLocalRingHom S f M D U e W : A →+* Γ(V', O)` (a ring hom: `liftLocalPiece_one`,
`liftLocalPiece_mul`); `φ := Proj.fromOfGlobalSections 𝒜 Φ _ : V' ⟶ Proj 𝒜`; by definition
`liftLocal … = φ ≫ (affineIso S W).inv ≫ (π⁻¹W).ι`, and `hτ` says this is `V'.ι ≫ τ`.

**Natural-language proof (complete, as things stand).**
1. *Canonical family on the absolute Proj (01O4 (2)).* For `s ∈ 𝒜_d`, `d > 0`: `φ⁻¹D₊(s) = V'.basicOpen (Φ s)`
   (Mathlib `Proj.fromOfGlobalSections_preimage_basicOpen`), and `Γ(D₊(s), O(n)) = {a/s^k : a ∈ 𝒜_{n+kd}}`
   (01MN; library: `Stacks01n2TwistStalkSections.twistSection`, `twistAway`). Put
   `χ_n(a/s^k) := Φ(a)·Φ(s)^{-k} ∈ Γ(V'.basicOpen (Φ s), O)` — `Φ(s)` is a unit there
   (`RingedSpace.isUnit_res_basicOpen`). Because `Φ` is a ring hom this respects the equivalence of fractions, is
   additive, is `Γ(D₊(s), O)`-linear (`Γ(D₊(s), O) = {b/s^k : b ∈ 𝒜_{kd}}` acts by the same formula), and is
   compatible with restriction `D₊(ss') ⊆ D₊(s)` (common denominators). The `D₊(s)` form a basis of `Proj 𝒜`, so
   `TopCat.Sheaf.restrictHomEquivHom` extends these section maps to a morphism `O(n) ⟶ φ_*O_{V'}` of sheaves of
   modules, whose adjoint transpose is `χ_n : φ^*O(n) ⟶ O_{V'}`. Multiplicativity `χ_{a+b}(xy) = χ_a(x)χ_b(y)` is
   checked on fractions (`Proj.twistMul` is pointwise multiplication of homogeneous fractions,
   `Proj.twistSectionMul`: `(a/s^k)(a'/s^{k'}) = aa'/s^{k+k'}`). On a global section `a/1 = Proj.twistSection 𝒜 a`
   (`a ∈ 𝒜_n`): `χ_n(φ^*(a/1)) = Φ(a)` (the case `k = 0`).
   (Equivalently, since `V'` is affine: `φ⁻¹D₊(s) = Spec Γ(V',O)[1/Φ(s)]`, `φ` restricted to it is
   `Spec.map (HomogeneousLocalization.Away.map Φ) ≫ Proj.awayι` (Mathlib `fromOfGlobalSections_morphismRestrict`,
   `toBasicOpenOfGlobalSections`), and `χ_n` is the base change of the module map `twistAway → Γ(V',O)[1/Φ(s)]`.)
2. *Transport to the piece.* Using only isomorphisms already in the library:
   (i) `(τ^*O(n))|_{V'} ≅ (V'.ι)^*τ^*O(n) ≅ (V'.ι ≫ τ)^*O(n) = liftLocal^*O(n)` (`restrictFunctorIsoPullback`,
   `pullbackComp`, `pullbackCongr hτ`);
   (ii) `liftLocal^*O(n) = φ^*(affineIso.inv)^*(ι^*O(n)) ≅ φ^*(affineIso.inv)^*(affineIso.hom)^*(Proj.twist 𝒜 n)
   ≅ φ^*(Proj.twist 𝒜 n)` (`twistAffineIso`, Stacks 01NR; `pullbackComp`, `pullbackCongr (Iso.inv_hom_id)`,
   `pullbackId`);
   (iii) `(M^{⊗n})|_{V'} ≅ ((V'.ι)^*M)^{⊗n} ≅ O_{V'}^{⊗n} ≅ O_{V'}` (`pullbackMonoidalPow`, `monoidalPowMap` of the
   trivialization `e` restricted to `V'` — `liftLocalTriv` further restricted along `V' ≤ U ⊓ f⁻¹W` —
   `unitPowCollapse`); these are exactly the isomorphisms in `liftLocalHom`.
   Set `ψ_n := (i) ≫ (ii) ≫ χ_n ≫ (iii)⁻¹`.
3. *(F).* Both sides of `ψ_n ∘ α_n = β_n` over `A ≤ V'` are additive, `O`-linear and natural in `A`; over `V'`
   the module `(τ≫π)^*S_n` is generated by the pullbacks `η(x)` of `x ∈ Γ(W, S_n)` (`W` affine, `S_n` quasi-coherent:
   `modulePullbackStalkTensorMap_bijective`), so it suffices to
   compare on `η(x)`. `α_n(η x)` restricted to `V'` is the pullback along `liftLocal` of `evaluationLocal S n W x`
   (`evaluationPresheafHom_app_affine`), i.e. by `evaluationLocal_eq` the transport under
   `twistAffineIso`/`affineIso` of `Proj.twistSection 𝒜 (S.sectionsOf W n x)`; by step 1, `χ_n` sends it to
   `Φ(sectionsOf x) = liftLocalPiece S f M D U e W n x` restricted to `V'` (`DirectSum.toSemiring_of`), and by the
   definition of `liftLocalPiece`/`liftLocalHom` this is `Ψ_n(η x)` read through (iii) — which is `β_n(η x)`
   restricted to `V'`.
4. *(M).* `twistMulHom` restricted to `π⁻¹W` is the transport of `Proj.twistMul 𝒜 a b` (`twistMul` is `glueHom` of
   `twistMulLocal`; `Modules.glueHom_app`), and `monoidalPowCat` on `O_{V'}^{⊗•}` corresponds under
   `unitPowCollapse` to multiplication in `Γ(-, O)` (the identities used in `liftLocalHomAux_mul`,
   `RelativeProjLift.lean` §LiftLocalHomMul). So (M) is the multiplicativity of `χ` from step 1.


**Edge cases.** `n = 0`: `χ_0` is the ring map induced by `Φ_0`, (F) is `liftLocalPiece_zero_apply`. `V' = ∅`:
vacuous. `d > 0` is needed for the basic-open basis (irrelevant ideal). The hypothesis `hτ` is supplied by
`exists_lift_restrict`. -/
theorem exists_twistFamily_of_piece
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hτ : V'.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle) :
    ∃ ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V'.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V'.ι,
      D.IsTwistFamilyOn V' ψ V' le_rfl := by
  obtain ⟨ψ, hψ⟩ := D.exists_twistFamily_of_piece' U e W V' hV' hle hτ
  exact ⟨ψ, hψ⟩

/-- **(U) Uniqueness of twist families over a piece** (Stacks 01O4: the pair `(L, ψ)` determines the morphism and
the isomorphism `r^*O(n) ≅ L^{⊗n}` "up to strict equivalence"; 01MN for the generators). Over an open `V` of a piece
`V'` (chart `W`, trivialization `e`), any two twist families `ψ¹` (on `V₁ ⊇ V`) and `ψ²` (on `V₂ ⊇ V`) have the same
section maps `Γ(τ^*O(n), V) → Γ(M^{⊗n}, V)` in every degree `n`.

**Natural-language proof (complete, as things stand; single chart `W`, no chart change).** Notation as in
`exists_twistFamily_of_piece`: `A = S.sectionsRing W`, `𝒜`, `Φ`, `φ = fromOfGlobalSections 𝒜 Φ _`,
`liftLocal = φ ≫ affineIso.inv ≫ (π⁻¹W).ι = V'.ι ≫ τ` (`hτ`).
1. *Localize.* Both section maps are additive and natural in the open (`sectionMapOfRestrictHom_nat`) and
   `O`-linear (`sectionMapOfRestrictHom_smul`); by the sheaf property it suffices to compare them after restriction to
   each member of the open cover of `V` by `V_s := V ⊓ V'.basicOpen (Φ s)`, `s ∈ 𝒜_d`, `d > 0` (these cover `V'`
   because `Φ` maps the irrelevant ideal onto `⊤`: Mathlib `openCoverOfMapIrrelevantEqTop`), and there on a set of
   local generators.
2. *Generators (01MN).* `V'.basicOpen (Φ s) = liftLocal⁻¹(D₊(s))` (`fromOfGlobalSections_preimage_basicOpen`,
   transported by `affineIso`), and `O(n)|_{π⁻¹W}` is the pullback under `affineIso` of `Proj.twist 𝒜 n`
   (`twistAffineIso`, 01NR), whose sections over `D₊(s)` are exactly the fractions `a/s^k`, `a ∈ 𝒜_{n+kd}`
   (`Stacks01n2TwistStalkSections`). A pullback `f^*F` is generated, locally, by the pullbacks of local sections of
   `F` (`modulePullbackStalkTensorMap_bijective`), so over `B ≤ V_s` the module `τ^*O(n)` is locally generated
   by the sections `σ_{a,k} := τ^*(a/s^k)`; two additive, `O`-linear, natural maps agreeing on these agree.
3. *Key identity.* In `Γ(τ^*O(n+kd), V_s)`: `μ(σ_{a,k} ⊗ τ^*(s/1)^{⊗k}) = τ^*(a/1)` — the fraction identity
   `(a/s^k)·(s/1)^k = a/1` (`Proj.twistSectionMul`), transported: `twistMulHom` restricted to `π⁻¹W` is
   `twistMulLocal S a b W`, the transport of `Proj.twistMul 𝒜` (`twistMul` is `glueHom` of `twistMulLocal`,
   `Modules.glueHom_app`). Here `τ^*(s/1)|_{V'} = α_d(η s)` and `τ^*(a/1)|_{V'} = α_{n+kd}(η a)` by
   `evaluationPresheafHom_app_affine` and `evaluationLocal_eq` (`x/1 = Proj.twistSection (sectionsOf x)`).
   For a twist family `ψ`: (M) iterated gives `ψ_{n+kd}(σ · (s/1)^k) = monoidalPowCat(ψ_n(σ) ⊗ ψ_d(s/1)^{⊗k})`, and
   (F) gives `ψ_d(s/1) = β_d(η s) = Ψ_d(η s) =: Ψ(s)` and `ψ_{n+kd}(a/1) = Ψ(a)`. Hence, for both families,
   `ψ_n(σ_{a,k}) ⊗ Ψ(s)^{⊗k} = Ψ(a)` in `Γ(M^{⊗(n+kd)}, V_s)` (through `monoidalPowCat`).
4. *Cancel the frame.* On `V_s`, `Ψ(s)` is a nowhere-vanishing section of the line bundle `M^{⊗d}`: through the
   trivialization `e` (restricted to `V'`), `e^{⊗d}(Ψ(s)) = Φ(s)` restricted to `V'.basicOpen (Φ s)`
   (`liftLocalPiece_apply`, definition of `liftLocalHom`), a unit (`RingedSpace.isUnit_res_basicOpen`). Tensoring
   with a nowhere-vanishing section of a line bundle is injective on sections (on a trivializing open it is
   multiplication by a unit; `M^{⊗kd}` is a line bundle, `Modules.monoidalPow_isLineBundle'`). Therefore
   `ψ¹_n(σ_{a,k}) = ψ²_n(σ_{a,k})`, and by 1–2 the section maps agree on `V`. ∎


**Edge cases.** `V = ∅`: trivial. `k = 0`: step 3 is (F) itself. `n = 0`: `σ = a/s^k` with `a ∈ 𝒜_{kd}`. The
hypothesis `hτ` comes from `exists_lift_restrict`; the two families may live on different opens
`V₁, V₂ ⊇ V` (this is how it is used on overlaps of pieces). -/
theorem twistFamily_sectionMap_unique
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
    (V' : T.Opens) (hV' : AlgebraicGeometry.IsAffineOpen V') (hle : V' ≤ U ⊓ f ⁻¹ᵁ W.1)
    (hτ : V'.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
      AlgebraicGeometry.Scheme.relativeProj.liftLocal S f M D U e W V' hV' hle)
    (V : T.Opens) (hV : V ≤ V') {V₁ V₂ : T.Opens}
    (ψ₁ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (ψ₂ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₂.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₂.ι)
    (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    (H₁ : D.IsTwistFamilyOn V₁ ψ₁ V h₁) (H₂ : D.IsTwistFamilyOn V₂ ψ₂ V h₂) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ₁ n) V h₁ =
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ₂ n) V h₂ := by
  exact D.twistFamily_sectionMap_unique' U e W V' hV' hle hτ V hV ψ₁ ψ₂ h₁ h₂ H₁ H₂ n

end LiftData

end AlgebraicGeometry.Scheme.relativeProj

end
