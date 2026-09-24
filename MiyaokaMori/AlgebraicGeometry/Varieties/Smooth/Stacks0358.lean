import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme

/-! # Global sections of a normal integral scheme (Stacks 0358)

Stacks 0358: the ring of global sections of an integral normal scheme is an integrally closed
domain (used for the sections of open subschemes `f⁻¹U`; "`B_i = Γ(V_i, O)` is a normal domain" in
the proof of Stacks 035L).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 0358: the global sections of an integral normal scheme form an integrally closed domain. -/
theorem AlgebraicGeometry.Scheme.isIntegrallyClosed_Γ_of_isNormal (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [X.IsNormal] :
    IsIntegrallyClosed Γ(X, ⊤) := by
  classical
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) X.functionField) :=
    X.germToFunctionField_injective ⊤
  have : FaithfulSMul Γ(X, ⊤) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsIntegrallyClosedIn Γ(X, ⊤) X.functionField := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨hinj, fun {f} hf => ?_⟩
    -- Step 1: `f` lies in every stalk, hence is the generic germ of a local section near each point.
    have hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)) (hηU : genericPoint X ∈ U),
        X.presheaf.germ U (genericPoint X) hηU s = f := by
      intro x
      have hfx : _root_.IsIntegral (X.presheaf.stalk x) f := by
        let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
        have := AlgebraicGeometry.functionField_isScalarTower X ⊤ ⟨x, trivial⟩
        exact hf.tower_top
      have := AlgebraicGeometry.Scheme.IsNormal.integrallyClosed (X := X) x
      obtain ⟨t, ht⟩ := (isIntegrallyClosed_iff X.functionField).mp inferInstance hfx
      obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq t
      have : Nonempty U := ⟨⟨x, hxU⟩⟩
      have hηU : genericPoint X ∈ U :=
        ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ x, hxU⟩
      refine ⟨U, hxU, s, hηU, ?_⟩
      rw [← ht, X.algebraMap_germ_eq_germToFunctionField hxU s]
    choose U hxU s hηU hs using hloc
    -- Step 2: the local sections are compatible (X is integral, so the generic germ is injective).
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := by
      intro i j
      have hmem : genericPoint X ∈ U i ⊓ U j := ⟨hηU i, hηU j⟩
      apply AlgebraicGeometry.germ_injective_of_isIntegral X (genericPoint X) hmem
      rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
      exact (hs i).trans (hs j).symm
    -- Step 3: glue to a global section.
    have hcover : (⊤ : X.Opens) ≤ iSup U := fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
    obtain ⟨g, hg, -⟩ :=
      X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcover s hcompat
    have hg' : ∀ i, X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op g = s i := hg
    refine ⟨g, ?_⟩
    -- Step 4: the global section maps to `f` in the function field.
    have h1 : X.presheaf.germ ⊤ (genericPoint X) trivial g = f :=
      calc X.presheaf.germ ⊤ (genericPoint X) trivial g
          = X.presheaf.germ (U (genericPoint X)) (genericPoint X) (hηU _)
              (X.presheaf.map (homOfLE (le_top : U (genericPoint X) ≤ ⊤)).op g) :=
            (X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) (hηU _) g).symm
        _ = X.presheaf.germ (U (genericPoint X)) (genericPoint X) (hηU _) (s (genericPoint X)) :=
            congrArg _ (hg' (genericPoint X))
        _ = f := hs (genericPoint X)
    exact h1
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn Γ(X, ⊤) X.functionField

end
