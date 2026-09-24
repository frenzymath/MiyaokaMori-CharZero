import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GeneratedInDegreeOneSections
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraGeneratedInDegreeOne
import MiyaokaMori.RingTheory.GradedRing.SymmetricAlgebraGrading
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective

/-! # The section ring of the symmetric algebra sheaf on an affine open is the symmetric algebra

Bridge sheaf → algebra for the (unweighted) symmetric algebra: on an **affine** open `U`, the section ring
`⨁_m Γ(U, Sym^m V)` of the sheaf-theoretic `symGradedAlgebra V` (`SheafSymmetricAlgebra.lean`)
is the algebraic symmetric algebra `Sym_{Γ(U)} Γ(U, V)` of the section module, with the `m`-th graded piece
going to the standard piece `symmetricPiece Γ(U) Γ(U,V) m = (range ι)^m` and the structure map going to
`algebraMap`.

Sources: Stacks 01CG (Sym^n of a quasi-coherent module is the sheafification of `U ↦ Sym^n Γ(U, F)`; on an
affine `U` with `F` quasi-coherent, `Γ(U, Sym^n F) = Sym^n Γ(U, F)`, Stacks 01I8 applied to the qc module
`Sym^n F`, cf. Stacks 01OB), Stacks 01N0 (generated in degree one), Bourbaki Algebra III §6 no. 1 (universal
property of `Sym`); §2 of the paper.

Unweighted sibling of `weightedSymAlgebra.exists_sectionsRing_equiv_symmetricAlgebra`
(`WeightedSymSectionsRingEquivSym.lean`); the skeleton below is transferred from there.

## Structure

The isomorphism is the inverse of the canonical `Γ(U)`-algebra map given by the universal property of the
symmetric algebra:

* `sectionsAlgebra`: the `Γ(U)`-algebra structure on the section ring via `sectionsUnitHom` (local instance);
* `genSections`: `Γ(U, V) → ⨁_m Γ(U, Sym^m V)`, `w ↦ of 1 ((symGen V).app U w)` — sections of the generator
  inclusion `symGen V : V → Sym^1 V` (`WeightedSymGenerator.lean`); it is `Γ(U)`-linear (`genLinear`);
* `symLiftHom : Sym_{Γ(U)} Γ(U, V) →+* ⨁_m Γ(U, Sym^m V)`: `SymmetricAlgebra.lift genLinear`. It sends
  `algebraMap` to `sectionsUnitHom` (`symLiftHom_algebraMap`), `ι w` to `genSections w` (`symLiftHom_ι`) and
  `symmetricPiece m` into `sectionsGrading m` (`symLiftHom_mem_sectionsGrading`, by `Submodule.pow_induction_on_left'`).
* **Surjectivity on affine `U`** (`symLiftHom_surjective`, proved): `Sym V` is generated in degree one
  (`symGradedAlgebra_generatedInDegreeOne`), so by Stacks 01N0 on sections
  (`GeneratedInDegreeOne.sectionsGrading_mem_closure`) every positive-degree section lies in the subring generated
  by `range sectionsUnitHom ∪ Γ(U, Sym^1 V)`; degree `0` is `sectionsUnitHom` because `O_X → Sym^0 V` is an
  isomorphism (`symGradedAlgebra_one_isIso`), and `Γ(U, Sym^1 V) = genSections (Γ(U, V))` because `symGen V` is an
  isomorphism (`symGen_isIso`). All of these are in the range of `symLiftHom`.
* **Injectivity on affine `U`** (`symLiftHom_injective`): from the algebra retraction
  `exists_algHom_retraction_genLinear`: a `Γ(U)`-algebra
  map `G : ⨁_m Γ(U, Sym^m V) → Sym_{Γ(U)} Γ(U, V)` with `G (genSections w) = ι w`. Then `G ∘ symLift = id`
  (`SymmetricAlgebra.algHom_ext`), so `symLiftHom` is injective. The retraction is derived from
  `symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap`
  (`TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective.lean`, the same statement in the *total*
  encoding `Γ(U, ∐_m Sym^m V)`) by composing with the ring homomorphism
  `GradedQCAlgebra.sectionsToTotalRingHom U : ⨁_m Γ(U, Sym^m V) → Γ(U, ∐_m Sym^m V)`. The isomorphism facts
  `isIso_symPowπ_zero`, `isIso_symPowπ_one`, `isIso_one`, `isIso_symGen` are proved here under their own names
  (namespace `symGradedAlgebra`); `symLiftHom_surjective` uses them.
* From injectivity alone: `symLiftHom a ∈ sectionsGrading m ↔ a ∈ symmetricPiece m`
  (`symLiftHom_mem_sectionsGrading_iff`, by comparing the two `DirectSum.decompose`; the decomposition of
  `Sym` is `MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricGrading`).
* The target theorem takes `e := (RingEquiv.ofBijective symLiftHom _).symm`.

An alternative piece-by-piece route (identify `Γ(U, V^{⊗m}) = Γ(U,V)^{⊗m}` and `Γ(U, Sym^m V) = Sym^m Γ(U, V)`
through the bijectivity of `tensorSectionsHom` and the coequalizer description of `Sym^m` on affine opens)
remains a valid alternative proof of `symLiftHom_injective`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite DirectSum
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.symGradedAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (U : X.Opens)

/-- The `Γ(U)`-algebra structure on the section ring `⨁_m Γ(U, Sym^m V)` given by the structure map
`sectionsUnitHom`. **Local instance only** (registered with `attribute [local instance]` below):
`sectionsRing` is a `def`, so no other `Algebra Γ(X, U)` instance is visible on it. -/
@[instance_reducible] def sectionsAlgebra :
    Algebra Γ(X, U) ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U) :=
  ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U).toAlgebra

attribute [local instance] sectionsAlgebra

theorem smul_def' (c : Γ(X, U)) (z : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U) :
    c • z = (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U c * z := rfl

theorem algebraMap_eq (c : Γ(X, U)) :
    algebraMap Γ(X, U) ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U) c =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U c := rfl

/-- Sections of the generator inclusion `symGen V : V → Sym^1 V`, placed in degree `1` of the section ring. -/
def genSections (w : Γ(V, U)) : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U :=
  (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).ofPiece U 1
    ((AlgebraicGeometry.Scheme.Modules.symGen V).app U w)

theorem genSections_mem_sectionsGrading (w : Γ(V, U)) :
    genSections V U w ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U 1 :=
  ⟨_, rfl⟩

theorem genSections_add (w w' : Γ(V, U)) :
    genSections V U (w + w') = genSections V U w + genSections V U w' := by
  unfold genSections
  rw [map_add]
  exact map_add (DirectSum.of ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsPiece U) 1) _ _

theorem genSections_smul (c : Γ(X, U)) (w : Γ(V, U)) :
    genSections V U (c • w) = c • genSections V U w := by
  rw [smul_def']
  unfold genSections
  rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  exact ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom_mul_ofPiece U c _).symm

/-- `genSections` as a `Γ(U)`-linear map. -/
def genLinear : Γ(V, U) →ₗ[Γ(X, U)] (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U where
  toFun := genSections V U
  map_add' := genSections_add V U
  map_smul' := genSections_smul V U

/-- **The canonical algebra map** `Sym_{Γ(U)} Γ(U, V) → ⨁_m Γ(U, Sym^m V)` (universal property of the
symmetric algebra, generators sent to `genSections`). -/
def symLift :
    SymmetricAlgebra Γ(X, U) Γ(V, U) →ₐ[Γ(X, U)]
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U :=
  SymmetricAlgebra.lift (genLinear V U)

/-- `symLift` as a ring homomorphism (its type does not mention the local algebra instance). -/
def symLiftHom :
    SymmetricAlgebra Γ(X, U) Γ(V, U) →+* (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U :=
  (symLift V U).toRingHom

theorem symLiftHom_apply (a : SymmetricAlgebra Γ(X, U) Γ(V, U)) : symLiftHom V U a = symLift V U a := rfl

theorem symLiftHom_algebraMap (c : Γ(X, U)) :
    symLiftHom V U (algebraMap Γ(X, U) _ c) =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U c :=
  (symLift V U).commutes c

theorem symLiftHom_ι (w : Γ(V, U)) :
    symLiftHom V U (SymmetricAlgebra.ι Γ(X, U) Γ(V, U) w) = genSections V U w := by
  rw [symLiftHom_apply]
  exact SymmetricAlgebra.lift_ι_apply (genLinear V U) w

theorem symLiftHom_smul (c : Γ(X, U)) (a : SymmetricAlgebra Γ(X, U) Γ(V, U)) :
    symLiftHom V U (c • a) =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U c * symLiftHom V U a := by
  rw [Algebra.smul_def, map_mul, symLiftHom_algebraMap]

/-- **Standard pieces go to graded pieces**: `symLiftHom (symmetricPiece m) ⊆ sectionsGrading m`
(`symmetricPiece m = (range ι)^m`; induction `Submodule.pow_induction_on_left'`: `algebraMap r ↦ sectionsUnitHom r ∈
grading 0`, sums, and `ι w * x ↦ genSections w * symLiftHom x ∈ grading (1 + i)`). -/
theorem symLiftHom_mem_sectionsGrading {m : ℕ} {a : SymmetricAlgebra Γ(X, U) Γ(V, U)}
    (ha : a ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U) Γ(V, U) m) :
    symLiftHom V U a ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U m := by
  change a ∈ (LinearMap.range (SymmetricAlgebra.ι Γ(X, U) Γ(V, U))) ^ m at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [symLiftHom_algebraMap]
    exact ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnit U r).2
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul w hw i x hx ih =>
    obtain ⟨w, rfl⟩ := hw
    rw [map_mul, symLiftHom_ι]
    have := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading_mul_mem U
      (genSections_mem_sectionsGrading V U w) ih
    rwa [Nat.add_comm] at this

/-! ### `O_X → Sym^0 V` and `V → Sym^1 V` are isomorphisms (quasi-coherent `V`)

The same facts exist as `symPowπ_zero_isIso`, `symPowπ_one_isIso`, `symGradedAlgebra_one_isIso`, `symGen_isIso` in
`TotalSpaceSectionsRingEquivMvPolynomialSymSectionsSurjective.lean`; they are proved here under distinct names. -/

/-- The quotient map `𝟙_ = V^{⊗0} → Sym^0 V` is an isomorphism (no transpositions to quotient by). -/
theorem isIso_symPowπ_zero : IsIso (AlgebraicGeometry.Scheme.Modules.symPowπ V 0) := by
  let inv := AlgebraicGeometry.Scheme.Modules.symPowDesc V 0 (𝟙 _) (fun i => i.elim0)
  have h₁ : AlgebraicGeometry.Scheme.Modules.symPowπ V 0 ≫ inv = 𝟙 _ := by
    dsimp only [inv]
    rw [AlgebraicGeometry.Scheme.Modules.symPowπ_desc]
  have h₂ : inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ V 0 = 𝟙 _ := by
    apply (cancel_epi (AlgebraicGeometry.Scheme.Modules.symPowπ V 0)).1
    rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]
  exact ⟨inv, h₁, h₂⟩

/-- The quotient map `V^{⊗1} → Sym^1 V` is an isomorphism (the only "transposition" is the identity). -/
theorem isIso_symPowπ_one : IsIso (AlgebraicGeometry.Scheme.Modules.symPowπ V 1) := by
  have htr : ∀ i : Fin 1, AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V 1 i = 𝟙 _ := fun i => by
    rw [Fin.fin_one_eq_zero i]; rfl
  let inv := AlgebraicGeometry.Scheme.Modules.symPowDesc V 1 (𝟙 _) (fun i => by rw [htr i, Category.id_comp])
  have h₁ : AlgebraicGeometry.Scheme.Modules.symPowπ V 1 ≫ inv = 𝟙 _ := by
    dsimp only [inv]
    rw [AlgebraicGeometry.Scheme.Modules.symPowπ_desc]
  have h₂ : inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ V 1 = 𝟙 _ := by
    apply (cancel_epi (AlgebraicGeometry.Scheme.Modules.symPowπ V 1)).1
    rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]
  exact ⟨inv, h₁, h₂⟩

/-- For quasi-coherent `V` the unit `O_X → Sym^0 V` of `symGradedAlgebra V` is an isomorphism. -/
theorem isIso_one [hq : V.IsQuasicoherent] : IsIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).one := by
  have hE : AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V =
      AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC V hq := by
    delta AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    exact dif_pos hq
  rw [hE]
  exact isIso_symPowπ_zero V

/-- For quasi-coherent `V` the generator inclusion `symGen V : V → Sym^1 V` is an isomorphism. -/
theorem isIso_symGen [hq : V.IsQuasicoherent] : IsIso (AlgebraicGeometry.Scheme.Modules.symGen V) := by
  have h1 := isIso_symPowπ_one V
  unfold AlgebraicGeometry.Scheme.Modules.symGen
  rw [dif_pos hq]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h1 inferInstance)

/-- **Surjectivity of the canonical map on an affine open** (Stacks 01N0 on sections). The range of
`symLiftHom` is a subring containing `range sectionsUnitHom` (`symLiftHom_algebraMap`) and every degree-one section
(`symGen V` is an isomorphism for quasi-coherent `V`, `isIso_symGen`, so `Γ(U, Sym^1 V) = genSections (Γ(U, V))`,
and `genSections w = symLiftHom (ι w)`). A degree-`0` section is `sectionsUnitHom U r` because `O_X → Sym^0 V` is an
isomorphism (`isIso_one`); a section of positive degree lies in the subring generated by
`range sectionsUnitHom ∪ Γ(U, Sym^1 V)` by `GeneratedInDegreeOne.sectionsGrading_mem_closure` applied to
`symGradedAlgebra_generatedInDegreeOne`. Every element of the section ring is a finite sum of such
(`DirectSum.induction_on`). -/
theorem symLiftHom_surjective [V.IsQuasicoherent] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Function.Surjective (symLiftHom V U) := by
  let T : Subring ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U) :=
    (symLiftHom V U).range
  have hunit : ∀ r : Γ(X, U), (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U r ∈ T :=
    fun r => ⟨algebraMap Γ(X, U) _ r, symLiftHom_algebraMap V U r⟩
  have hone : IsIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).one := isIso_one V
  have hgen : IsIso (AlgebraicGeometry.Scheme.Modules.symGen V) := isIso_symGen V
  have hdeg1 : ∀ b : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsPiece U 1,
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).ofPiece U 1 b ∈ T := by
    intro b
    obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.Scheme.Modules.symGen V).app U)).2 b
    refine ⟨SymmetricAlgebra.ι Γ(X, U) Γ(V, U) w, ?_⟩
    rw [symLiftHom_ι]
    unfold genSections
    rw [hw]
  have hsub : (Set.range ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U) ∪
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U 1 :
        Set ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U))) ⊆ T := by
    rintro x (⟨r, rfl⟩ | ⟨b, rfl⟩)
    · exact hunit r
    · exact hdeg1 b
  intro x
  refine DirectSum.induction_on (β := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsPiece U)
    (motive := fun x => x ∈ T) x (Subring.zero_mem _) ?_ (fun x y hx hy => Subring.add_mem _ hx hy)
  rintro (_ | m) a
  · obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).one.app U)).2 a
    have h0 : DirectSum.of ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsPiece U) 0 a =
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U r := by
      show _ = DirectSum.of ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsPiece U) 0
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).one.app U r)
      rw [hr]
    rw [h0]
    exact hunit r
  · exact Subring.closure_le.mpr hsub
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.GeneratedInDegreeOne.sectionsGrading_mem_closure
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_generatedInDegreeOne V) hU (Nat.succ_pos m) ⟨a, rfl⟩)

/-- **A `Γ(U)`-algebra retraction of the degree-one inclusion.**
For `V` quasi-coherent and `U` affine there is a `Γ(U)`-algebra map `G : ⨁_m Γ(U, Sym^m V) → Sym_{Γ(U)} Γ(U, V)`
(the section ring carrying the algebra structure `sectionsAlgebra`, i.e. `algebraMap = sectionsUnitHom`) with
`G (genSections w) = ι w` for every `w ∈ Γ(U, V)`. Together with `symLiftHom_surjective` this says `symLiftHom` is
bijective and `G` is its inverse (`symLiftHom_injective`, `symLiftHom_bijective`).

Sources: Stacks 01CG (Sym of a quasi-coherent module), 01I8/01I9 (quasi-coherent modules on an affine scheme are
determined by their global sections; base change of sections), 01LQ (maps to a relative Spec are algebra maps);
Bourbaki Algebra III §6 no. 1 and no. 6; §2 of the paper.

**Proof (as formalized): derived from**
`symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap`
(`TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective.lean`), which is the same statement in the *total*
encoding `A_tot := Γ(U, ∐_m Sym^m V)` with the `Γ(U)`-algebra structure `sectionsUnit` and degree-one inclusion
`symGenTotalLinearMap V U w = (symGen V ≫ totalIncl 1).app U w`. Let `G_tot : A_tot →ₐ[Γ(U)] Sym_{Γ(U)} Γ(U,V)` be
that retraction and `θ := GradedQCAlgebra.sectionsToTotalRingHom U : A → A_tot` the ring homomorphism induced by the
inclusions `totalIncl m : Sym^m V → ∐ Sym^m V` (`θ (of m a) = (totalIncl m).app U a`, `sectionsToTotalRingHom_of`).
Set `G := G_tot ∘ θ`. It is a `Γ(U)`-algebra map: `θ (sectionsUnitHom U r) = sectionsUnit U r`
(`sectionsToTotalRingHom_sectionsUnitHom`) and `G_tot` commutes with `algebraMap`. On generators,
`θ (genSections w) = θ (of 1 ((symGen V).app U w)) = (totalIncl 1).app U ((symGen V).app U w)
= (symGen V ≫ totalIncl 1).app U w = symGenTotalLinearMap V U w` (`Hom.comp_app`), so
`G (genSections w) = G_tot (symGenTotalLinearMap V U w) = ι w`.

Direct proof of the retraction (the route of the total-encoding statement, kept for reference). Write `R := Γ(X, U)`,
`N := Γ(U, V)`, `B := Sym_R N`, `A := ⨁_m Γ(U, Sym^m V)`.
1. **A scheme with function ring `B`.** Let `T := Spec B` and `g : T → X` the composite
   `Spec B → Spec R ≅ U → X` (`Spec.map (algebraMap R B)` followed by `hU.fromSpec`, an open immersion with image
   `U`, `IsAffineOpen.fromSpec`). Then `g⁻¹ U = ⊤`, so `Γ(U, g_* O_T) = Γ(T, O_T) ≅ B` as `R`-algebras
   (`Scheme.ΓSpecIso`; the `R`-algebra structure of `Γ(T, O_T)` is `g^♯` on `U`, which is `algebraMap R B` under
   `ΓSpecIso` — `Spec.map_appTop` / `ΓSpecIso_naturality` plus `IsAffineOpen.fromSpec_app_top`-type identities).
2. **A module map `V → g_* O_T` inducing `ι : N → B` on `U`.** By the pullback–pushforward adjunction
   (`Modules.pullbackPushforwardAdjunction g`), `Hom_X(V, g_* O_T) ≅ Hom_T(g^* V, O_T)`. `g^* V` is quasi-coherent on
   the affine scheme `T` (`isQuasicoherent_pullback`), so by the affine tilde adjunction (`AffineTilde.exists_hom_of_linear`,
   `AffineTildeAdjunction.lean`) a morphism `g^* V → O_T` is the same as a `Γ(T, O_T)`-linear map
   `Γ(T, g^* V) → Γ(T, O_T)`. `Γ(T, g^* V) ≅ B ⊗_R N`: the pullback along the open immersion `fromSpec` has global
   sections `Γ(U, V) = N` (`PullbackSectionsNativeBaseChange` / `restrictFunctorIsoPullback` + `fromSpec ''ᵁ ⊤ = U`), and
   the pullback along `Spec (R → B)` of a quasi-coherent module has global sections `B ⊗_R (·)`
   (`SpecBaseChange.bijective_τ`, `PullbackSectionsSpecBaseChange.lean`, Stacks 01I9).
   Take the `B`-linear map `B ⊗_R N → B`, `b ⊗ n ↦ b · ι n` (`TensorProduct.lift`), giving `φ : V → g_* O_T` with
   `φ.app U = ι : N → B` under the identifications of step 1 (the unit of the adjunction on sections composed with `τ`
   is `n ↦ 1 ⊗ n`, `SpecBaseChange.τ_unit`).
3. **Degreewise maps `Φ_m : Sym^m V → g_* O_T`.** `g_* O_T` is an `O_X`-algebra sheaf (multiplication
   `pushforwardUnitMul g`, unit `pushforwardUnitOne g`; `TotalSpaceSectionConstructions.lean`,
   `ProjectiveBundleUniversalPropertyMonoidalPow.lean`). `V^{⊗m} → (g_* O_T)^{⊗m} → g_* O_T` (`monoidalPowMap φ m` then
   iterated multiplication, `unitPowCollapse`-style) is invariant under the adjacent transpositions because `g_* O_T`
   is commutative (`braiding` compatibility of `pushforwardUnitMul`), hence descends along `symPowπ V m` (`symPowDesc`)
   to `Φ_m`. Compatibilities `symGradedAlgebra.one ≫ Φ_0 = pushforwardUnitOne g` and
   `symPowMul m n ≫ Φ_{m+n} = (Φ_m ⊗ₘ Φ_n) ≫ pushforwardUnitMul g`: both sides are determined after precomposition
   with the epimorphism `symPowπ ⊗ₘ symPowπ` (`epi_tensorHom_of_epi`), where they agree by `tensorHom_symPowπ_symPowMul`
   and the concatenation compatibilities `monoidalPowCat_monoidalPowMap`, `unitPowCollapse_monoidalPowCat`
   (`ProjectiveBundleUniversalPropertyMonoidalPow.lean`); this is the argument of
   `totalSpace.algebraMapOfFunctionalCore_mul` / `_one` (`TotalSpaceSectionConstructions.lean`), there written for
   `V^∨` and a functional `g^* V^∨ → O_T`.
4. **Sections over `U`.** `GradedQCAlgebra.sectionsToRingHom` (`GradedQcAlgebraSectionsToQcAlgebra.lean`)
   turns the compatible family `Φ_m` into a ring homomorphism `A → Γ(U, g_* O_T)`, `of m a ↦ (Φ_m).app U a`; composed with
   `Γ(U, g_* O_T) ≅ B` (step 1) and using `Hom.app_smul` for `R`-linearity it is an `R`-algebra map `G`. On degree one,
   `G (genSections w) = (Φ_1).app U ((symGen V).app U w) = φ.app U w = ι w` by step 2
   (`symGen = (λ_)⁻¹ ≫ symPowπ 1 ≫ eqToHom`, `symPowπ_desc`; `monoidalPowMap φ 1` is `φ` up to the unitor).

Alternative route: build `G` degreewise as the inverse of `symLiftHom` on `Γ(U, Sym^m V)`: `Γ(U, V^{⊗m}) ≅ N^{⊗m}`
by induction along `monoidalPow` (bijectivity of `tensorSectionsHom` on affine opens, Stacks 01I8), `Γ(U, Sym^m V)` is
the quotient of `N^{⊗m}` by the adjacent transpositions (`symPowπ_app_surjective_of_isAffineOpen` and the kernel
description), and `N^{⊗m} → Sym^m_R N` kills `transp x - x` (`B` commutative); assemble with `DirectSum.toModule`,
multiplicativity from `tensorHom_symPowπ_symPowMul`. Longer (needs monoidal coherence on sections).

Edge cases: `U = ⊥` (`R = 0`, `B = 0`, `A = 0`; `G = 0`); `V = 0` (`N = 0`, `B = R`, `A = Γ(U, Sym^0 V) = R` — `Sym^m 0 = 0`
for `m ≥ 1`; `G = id`); `V` not quasi-coherent is excluded (the trivial branch of `symGradedAlgebra` gives `A = R` while
`N` may be nonzero, and no such `G` need exist). -/
theorem exists_algHom_retraction_genLinear [V.IsQuasicoherent] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    ∃ G : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U →ₐ[Γ(X, U)]
        SymmetricAlgebra Γ(X, U) Γ(V, U),
      ∀ w : Γ(V, U), G (genSections V U w) = SymmetricAlgebra.ι Γ(X, U) Γ(V, U) w := by
  let _ := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).total.sectionsUnit U).toAlgebra
  obtain ⟨G₁, hG₁⟩ :=
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap V ⟨U, hU⟩
  -- recast from `(⟨U, hU⟩ : X.affineOpens).1` to `U` (definitionally equal) so that `rw` sees `U` syntactically
  let G₀ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).total.sectionsRing U →ₐ[Γ(X, U)]
      SymmetricAlgebra Γ(X, U) Γ(V, U) := G₁
  have hG₀ : ∀ n : Γ(V, U), G₀ (AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap V U n) =
      SymmetricAlgebra.ι Γ(X, U) Γ(V, U) n := hG₁
  let Gθ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U →+*
      SymmetricAlgebra Γ(X, U) Γ(V, U) :=
    G₀.toRingHom.comp ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsToTotalRingHom U)
  refine ⟨{ toRingHom := Gθ, commutes' := fun r => ?_ }, fun w => ?_⟩
  · show G₀ ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsToTotalRingHom U
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U r)) = _
    rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.sectionsToTotalRingHom_sectionsUnitHom]
    exact G₀.commutes r
  · show G₀ ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsToTotalRingHom U
      (genSections V U w)) = _
    rw [← hG₀ w]
    congr 1
    refine ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsToTotalRingHom_of U 1
      ((AlgebraicGeometry.Scheme.Modules.symGen V).app U w)).trans ?_
    rw [AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap_apply,
      AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
    rfl

/-- **Injectivity of the canonical map on an affine open**: `symLiftHom` has the left inverse `G` of
`exists_algHom_retraction_genLinear` (`G ∘ symLift = id` by `SymmetricAlgebra.algHom_ext`, both sides being the
identity on `ι w`: `symLiftHom_ι`). -/
theorem symLiftHom_injective [V.IsQuasicoherent] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Function.Injective (symLiftHom V U) := by
  obtain ⟨G, hG⟩ := exists_algHom_retraction_genLinear V hU
  have hcomp : G.comp (symLift V U) = AlgHom.id _ _ := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun w => ?_)
    show G (symLift V U (SymmetricAlgebra.ι Γ(X, U) Γ(V, U) w)) = SymmetricAlgebra.ι Γ(X, U) Γ(V, U) w
    rw [← symLiftHom_apply, symLiftHom_ι, hG]
  intro a b hab
  have ha := DFunLike.congr_fun hcomp a
  have hb := DFunLike.congr_fun hcomp b
  rw [AlgHom.comp_apply, AlgHom.id_apply] at ha hb
  rw [← ha, ← hb]
  exact congrArg G hab

/-- **Bijectivity of the canonical map on an affine open** (`symLiftHom_injective`, `symLiftHom_surjective`). -/
theorem symLiftHom_bijective [V.IsQuasicoherent] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Function.Bijective (symLiftHom V U) :=
  ⟨symLiftHom_injective V hU, symLiftHom_surjective V hU⟩

/-- The decompositions of `symLiftHom a` (in `sectionsGrading`) and of `a` (in `symmetricPiece`) match
componentwise. -/
theorem decompose_symLiftHom (a : SymmetricAlgebra Γ(X, U) Γ(V, U)) (k : ℕ) :
    ((DirectSum.decompose ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U)
        (symLiftHom V U a) k : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U k) :
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U) =
      symLiftHom V U
        (DirectSum.decompose (MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U) Γ(V, U)) a k :
          SymmetricAlgebra Γ(X, U) Γ(V, U)) := by
  refine DirectSum.Decomposition.inductionOn
    (ℳ := MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U) Γ(V, U)) ?_ ?_ ?_ a
  · rw [map_zero, DirectSum.decompose_zero, DirectSum.decompose_zero, DirectSum.zero_apply,
      DirectSum.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_zero]
  · intro j x
    have hx : (x : SymmetricAlgebra Γ(X, U) Γ(V, U)) ∈
        MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U) Γ(V, U) j := x.2
    by_cases hjk : j = k
    · subst hjk
      rw [DirectSum.decompose_of_mem_same _ hx,
        DirectSum.decompose_of_mem_same _ (symLiftHom_mem_sectionsGrading V U hx)]
    · rw [DirectSum.decompose_of_mem_ne _ hx hjk,
        DirectSum.decompose_of_mem_ne _ (symLiftHom_mem_sectionsGrading V U hx) hjk, map_zero]
  · intro x y hx hy
    rw [map_add, DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.add_apply,
      DirectSum.add_apply, AddSubgroup.coe_add, Submodule.coe_add, map_add, hx, hy]

/-- **Graded pieces correspond** (needs only injectivity): `symLiftHom a ∈ sectionsGrading m ↔ a ∈ symmetricPiece m`. -/
theorem symLiftHom_mem_sectionsGrading_iff (hinj : Function.Injective (symLiftHom V U)) (m : ℕ)
    (a : SymmetricAlgebra Γ(X, U) Γ(V, U)) :
    symLiftHom V U a ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U m ↔
      a ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U) Γ(V, U) m := by
  refine ⟨fun h => ?_, symLiftHom_mem_sectionsGrading V U⟩
  set ℳ := MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U) Γ(V, U) with hℳ
  have hzero : ∀ k, k ≠ m → DirectSum.decompose ℳ a k = 0 := by
    intro k hk
    apply Subtype.ext
    apply hinj
    rw [ZeroMemClass.coe_zero, map_zero, ← decompose_symLiftHom,
      DirectSum.decompose_of_mem_ne _ h (Ne.symm hk)]
  have hdec : DirectSum.decompose ℳ a = DirectSum.of (fun k => ℳ k) m (DirectSum.decompose ℳ a m) := by
    refine DirectSum.ext fun k => ?_
    by_cases hk : k = m
    · subst hk
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne m k _ hk, hzero k hk]
  have ha : a = (DirectSum.decompose ℳ a m : _) := by
    conv_lhs => rw [← (DirectSum.decompose ℳ).symm_apply_apply a, hdec, DirectSum.decompose_symm_of]
  rw [ha]
  exact (DirectSum.decompose ℳ a m).2

end AlgebraicGeometry.Scheme.Modules.symGradedAlgebra

/-- **Section ring of `Sym V` on an affine open = algebraic symmetric algebra of the sections.**

Notation: `S := symGradedAlgebra V`, `R := Γ(X, U)`, `N := Γ(V, U)` (an `R`-module), `A := Sym_R N` with the
standard grading `symmetricPiece R N m = (range ι)^m`.

Proof: `e` is the inverse of the canonical algebra map `φ := symLiftHom V U : A → ⨁_m Γ(U, Sym^m V)`
(universal property of `Sym`, generators sent to the sections of `symGen V : V → Sym^1 V`), which is bijective on
affine `U` (`symLiftHom_bijective`: surjective by Stacks 01N0 on sections, `symLiftHom_surjective`;
injective by the algebra retraction `exists_algHom_retraction_genLinear`, `symLiftHom_injective`; that retraction
is derived from `symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap`).
The grading statement is `symLiftHom_mem_sectionsGrading_iff` (from injectivity: `φ (symmetricPiece m) ⊆
sectionsGrading m` by `Submodule.pow_induction_on_left'`, and the two `DirectSum.decompose` match componentwise);
the unit statement is `symLiftHom_algebraMap` (`φ` is an `R`-algebra map for the algebra structure given by
`sectionsUnitHom`).

Edge cases checked: `U = ⊥` (both sides are the zero ring: `R = 0`, every `R`-module is trivial, so
`Γ(U, symPow V m) = 0` and `Sym_0 0 = 0`; every element lies in every piece, `algebraMap` is the zero map);
`V = 0` (`Sym^0 = O_X`, `Sym^m = 0` for `m ≥ 1`; `Sym_R 0 = R`); `X` the empty scheme (only `U = ⊥`). The
hypothesis `IsQuasicoherent` is needed only so that `symGradedAlgebra V` is in its `symGradedAlgebraOfQC`
branch (for non-qc `V` it is the trivial algebra `O_X` in degree 0, and the statement would be false unless
`Γ(V, U) = 0`); no finiteness is needed. -/
theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.exists_sectionsRing_equiv_symmetricAlgebra
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsQuasicoherent] (U : X.AffineZariskiSite) :
    ∃ e : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U.toOpens ≃+*
        SymmetricAlgebra Γ(X, U.toOpens) Γ(V, U.toOpens),
      (∀ (m : ℕ) (a : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsRing U.toOpens),
        a ∈ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsGrading U.toOpens m ↔
          e a ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece Γ(X, U.toOpens) Γ(V, U.toOpens) m) ∧
      (∀ s : Γ(X, U.toOpens),
        e ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom U.toOpens s) =
          algebraMap Γ(X, U.toOpens) _ s) := by
  open AlgebraicGeometry.Scheme.Modules.symGradedAlgebra in
  have hbij := symLiftHom_bijective V U.2
  let e0 := RingEquiv.ofBijective (symLiftHom V U.toOpens) hbij
  refine ⟨e0.symm, fun m a => ?_, fun s => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, e0 b = a := hbij.2 a
    rw [e0.symm_apply_apply]
    exact symLiftHom_mem_sectionsGrading_iff V U.toOpens hbij.1 m b
  · apply e0.injective
    rw [e0.apply_symm_apply]
    exact (symLiftHom_algebraMap V U.toOpens s).symm

end
