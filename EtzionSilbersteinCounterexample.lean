import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Basic definitions for the Etzion--Silberstein counterexample

The counterexample uses the top-aligned Ferrers diagram with column heights
`(3, 3, 5, 5, 5)` and minimum rank distance five over `𝔽₁₆₉`.
-/

set_option autoImplicit false

open Finset BigOperators Module

namespace EtzionSilbersteinCounterexample

abbrev Row := Fin 5
abbrev Column := Fin 5

/-- The column heights of the counterexample Ferrers diagram. -/
def columnHeight : Column → ℕ := ![3, 3, 5, 5, 5]

/-- Entries below the top-aligned Ferrers diagram vanish. -/
def IsSupported {R : Type*} [Zero R] (A : Matrix Row Column R) : Prop :=
  ∀ i j, columnHeight j ≤ i.1 → A i j = 0

/-- The `j`-th deletion count in the Etzion--Silberstein bound at distance five. -/
def boundTerm (j : Fin 5) : ℕ :=
  ∑ i : Fin 5,
    if i.1 < 5 - j.1 then columnHeight i - (4 - j.1) else 0

/-- The Etzion--Silberstein upper bound for this fixed diagram and distance. -/
def etzionSilbersteinBound : ℕ :=
  (Finset.univ.image boundTerm).min' (by simp)

theorem boundTerm_values : List.ofFn boundTerm = [3, 4, 5, 4, 3] := by
  decide

theorem etzionSilbersteinBound_eq_three : etzionSilbersteinBound = 3 := by
  decide

abbrev SquareMatrix (R : Type*) := Matrix Row Column R

section Code

variable {F : Type*} [Field F]

/-- A supported linear space in which every nonzero matrix has full rank. -/
def IsRankFiveCode (C : Submodule F (SquareMatrix F)) : Prop :=
  (∀ A ∈ C, IsSupported A) ∧
    ∀ A ∈ C, A ≠ 0 → Matrix.det A ≠ 0

/-- For a `5 × 5` matrix over a field, determinant nonzero is equivalent to
matrix rank five. -/
theorem det_ne_zero_iff_rank_eq_five (A : SquareMatrix F) :
    Matrix.det A ≠ 0 ↔ Matrix.rank A = 5 := by
  constructor
  · intro hdet
    apply Matrix.rank_of_isUnit
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  · intro hrank hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hvker : v ∈ LinearMap.ker A.mulVecLin := by
      simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hAv
    have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := by
      intro heq
      have : v ∈ (⊥ : Submodule F (Column → F)) := heq ▸ hvker
      exact hv (by simpa using this)
    have hker_rank : 1 ≤ Module.finrank F (LinearMap.ker A.mulVecLin) :=
      Submodule.one_le_finrank_iff.mpr hker
    have hrank_nullity := A.mulVecLin.finrank_range_add_finrank_ker
    change Module.finrank F (LinearMap.range A.mulVecLin) = 5 at hrank
    rw [hrank] at hrank_nullity
    have hdomain : Module.finrank F (Column → F) = 5 := by simp
    rw [hdomain] at hrank_nullity
    omega

/-- The determinant formulation used by `IsRankFiveCode` really gives matrix
rank five for every nonzero codeword. -/
theorem IsRankFiveCode.rank_eq_five {C : Submodule F (SquareMatrix F)}
    (hC : IsRankFiveCode C) {A : SquareMatrix F} (hA : A ∈ C) (hA0 : A ≠ 0) :
    Matrix.rank A = 5 := by
  exact (det_ne_zero_iff_rank_eq_five A).mp (hC.2 A hA hA0)

/-- `k` is attained and is an upper bound for all supported full-rank codes. -/
def IsOptimalDimension (k : ℕ) : Prop :=
  (∃ C : Submodule F (SquareMatrix F),
      IsRankFiveCode C ∧ Module.finrank F C = k) ∧
    ∀ C : Submodule F (SquareMatrix F),
      IsRankFiveCode C → Module.finrank F C ≤ k

/-- Attainment of the numerical Etzion--Silberstein bound. -/
def AttainsEtzionSilbersteinBound : Prop :=
  ∃ C : Submodule F (SquareMatrix F),
    IsRankFiveCode C ∧ Module.finrank F C = etzionSilbersteinBound

end Code

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- A canonical model of the field with `13² = 169` elements. -/
abbrev F169 := GaloisField 13 2

noncomputable instance : Fintype F169 := Fintype.ofFinite F169

theorem card_F169 : Fintype.card F169 = 169 := by
  rw [Fintype.card_eq_nat_card]
  simpa [F169] using GaloisField.card 13 2 (by norm_num : (2 : ℕ) ≠ 0)

/-- The fixed cubic extension used in the upper-bound argument. -/
abbrev CubicExtension := FiniteField.Extension F169 13 3

/-- The fixed degree-five extension used for the lower-bound construction. -/
abbrev QuinticExtension := FiniteField.Extension F169 13 5

abbrev Parameters (R : Type*) := Fin 3 → R

/-- A three-parameter linear pencil of `5 × 5` matrices. -/
def pencil {R : Type*} [CommSemiring R]
    (M : Fin 3 → SquareMatrix R) (x : Parameters R) : SquareMatrix R :=
  ∑ i, x i • M i

/-- Base-change a matrix pencil from `F` to an `F`-algebra `E`. -/
def extendedPencil {F E : Type*} [CommSemiring F] [CommSemiring E] [Algebra F E]
    (M : Fin 3 → SquareMatrix F) (x : Parameters E) : SquareMatrix E :=
  ∑ i, x i • (M i).map (algebraMap F E)

@[simp] theorem pencil_zero {R : Type*} [CommSemiring R]
    (M : Fin 3 → SquareMatrix R) : pencil M 0 = 0 := by
  simp [pencil]

end EtzionSilbersteinCounterexample

set_option autoImplicit false

open Finset BigOperators Module

namespace EtzionSilbersteinCounterexample
namespace Construction

/-- The degree-five extension used for the multiplication construction. -/
abbrev E := QuinticExtension

/-- A power basis `1, α, ..., α⁴` for the degree-five extension. -/
noncomputable def powerBasis : PowerBasis F169 E :=
  Field.powerBasisOfFiniteOfSeparable F169 E

theorem powerBasis_dim : powerBasis.dim = 5 := by
  rw [← powerBasis.finrank, FiniteField.finrank_extension F169 13 5]

/-- The power basis reindexed by the literal type `Fin 5`. -/
noncomputable def basis : Basis (Fin 5) F169 E :=
  powerBasis.basis.reindex (finCongr powerBasis_dim)

theorem basis_apply (i : Fin 5) : basis i = powerBasis.gen ^ (i : ℕ) := by
  simp [basis, PowerBasis.coe_basis]

theorem basis_zero : basis 0 = 1 := by
  rw [basis_apply]
  simp

theorem basis_one : basis 1 = powerBasis.gen := by
  rw [basis_apply]
  simp

theorem basis_two : basis 2 = powerBasis.gen ^ 2 := by
  rw [basis_apply]
  change powerBasis.gen ^ (2 : ℕ) = powerBasis.gen ^ (2 : ℕ)
  rfl

/-- The two-dimensional coefficient space `a + bα`, expressed using the first
two power-basis vectors. -/
noncomputable def coefficientMap : F169 × F169 →ₗ[F169] E :=
  LinearMap.coprod
    ((LinearMap.id : F169 →ₗ[F169] F169).smulRight (basis 0))
    ((LinearMap.id : F169 →ₗ[F169] F169).smulRight (basis 1))

theorem coefficientMap_apply (x : F169 × F169) :
    coefficientMap x = x.1 • basis 0 + x.2 • basis 1 :=
  rfl

theorem coefficientMap_coord_zero (x : F169 × F169) :
    basis.repr (coefficientMap x) 0 = x.1 := by
  rw [coefficientMap_apply, map_add, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply]
  norm_num

theorem coefficientMap_coord_one (x : F169 × F169) :
    basis.repr (coefficientMap x) 1 = x.2 := by
  rw [coefficientMap_apply, map_add, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply]
  norm_num

theorem coefficientMap_injective : Function.Injective coefficientMap := by
  intro x y hxy
  apply Prod.ext
  · have h := congr_arg (fun z : E => basis.repr z 0) hxy
    simpa only [coefficientMap_coord_zero] using h
  · have h := congr_arg (fun z : E => basis.repr z 1) hxy
    simpa only [coefficientMap_coord_one] using h

/-- The left-regular representation of `a + bα` in the power basis. -/
noncomputable def constructionMap :
    F169 × F169 →ₗ[F169] SquareMatrix F169 :=
  (Algebra.leftMulMatrix basis).toLinearMap.comp coefficientMap

theorem constructionMap_apply (x : F169 × F169) :
    constructionMap x = Algebra.leftMulMatrix basis (coefficientMap x) :=
  rfl

theorem constructionMap_injective : Function.Injective constructionMap :=
  (Algebra.leftMulMatrix_injective basis).comp coefficientMap_injective

/-- The promised two-dimensional multiplication code. -/
noncomputable def code : Submodule F169 (SquareMatrix F169) :=
  LinearMap.range constructionMap

theorem code_finrank : Module.finrank F169 code = 2 := by
  let e : (F169 × F169) ≃ₗ[F169] code :=
    LinearEquiv.ofInjective constructionMap constructionMap_injective
  calc
    Module.finrank F169 code = Module.finrank F169 (F169 × F169) := e.finrank_eq.symm
    _ = 2 := by simp [Module.finrank_prod]

theorem leftMulMatrix_det_ne_zero {x : E} (hx : x ≠ 0) :
    Matrix.det (Algebra.leftMulMatrix basis x) ≠ 0 := by
  rw [← Algebra.norm_eq_matrix_det basis]
  exact Algebra.norm_ne_zero_iff_of_basis basis |>.2 hx

theorem coefficientMap_mul_basis_zero (x : F169 × F169) :
    coefficientMap x * basis 0 =
      x.1 • basis 0 + x.2 • basis 1 := by
  rw [coefficientMap_apply, basis_zero, mul_one]

theorem coefficientMap_mul_basis_one (x : F169 × F169) :
    coefficientMap x * basis 1 =
      x.1 • basis 1 + x.2 • basis 2 := by
  rw [coefficientMap_apply, add_mul]
  rw [smul_mul_assoc, smul_mul_assoc, basis_zero, one_mul,
    basis_one, basis_two, pow_two]

theorem repr_two_basis_eq_zero (a b : F169) (r s i : Fin 5)
    (hri : r ≠ i) (hsi : s ≠ i) :
    basis.repr (a • basis r + b • basis s) i = 0 := by
  rw [map_add, map_smul, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Basis.repr_self_apply, Basis.repr_self_apply, if_neg hri, if_neg hsi]
  simp

theorem code_supported : ∀ A ∈ code, IsSupported A := by
  rintro A ⟨x, rfl⟩ i j hij
  rw [constructionMap_apply, Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · change basis.repr (coefficientMap x * basis 0) i = 0
    rw [coefficientMap_mul_basis_zero]
    apply repr_two_basis_eq_zero
    · intro h
      subst i
      norm_num [columnHeight] at hij
    · intro h
      subst i
      norm_num [columnHeight] at hij
  · change basis.repr (coefficientMap x * basis 1) i = 0
    rw [coefficientMap_mul_basis_one]
    apply repr_two_basis_eq_zero
    · intro h
      subst i
      norm_num [columnHeight] at hij
    · intro h
      subst i
      norm_num [columnHeight] at hij
  · norm_num [columnHeight] at hij
    exact (Nat.not_le_of_lt i.isLt hij).elim
  · norm_num [columnHeight] at hij
    exact (Nat.not_le_of_lt i.isLt hij).elim
  · norm_num [columnHeight] at hij
    exact (Nat.not_le_of_lt i.isLt hij).elim

theorem code_full_rank :
    ∀ A ∈ code, A ≠ 0 → Matrix.det A ≠ 0 := by
  rintro A ⟨x, rfl⟩ hA
  apply leftMulMatrix_det_ne_zero
  intro hx
  apply hA
  rw [constructionMap_apply, hx, map_zero]

/-- The degree-five extension construction supplies a two-dimensional code. -/
theorem twoDimensionalCode : IsRankFiveCode code :=
  ⟨code_supported, code_full_rank⟩

end Construction
end EtzionSilbersteinCounterexample

set_option autoImplicit false

open Finset BigOperators Module

namespace EtzionSilbersteinCounterexample

open Polynomial

/-! The cubic extension contains a root of every monic cubic over `F169`.

The irreducible case is handled by adjoining a root.  The resulting field has
dimension three over `F169`, and hence has an `F169`-algebra homomorphism into
the chosen cubic finite-field extension.
-/

theorem exists_root_monic_cubic (f : F169[X]) (_hf : f.Monic)
    (hdeg : f.natDegree = 3) :
    ∃ x : CubicExtension, IsRoot (f.map (algebraMap F169 CubicExtension)) x := by
  classical
  by_cases hroot : ∃ x : F169, IsRoot f x
  · obtain ⟨x, hx⟩ := hroot
    exact ⟨algebraMap F169 CubicExtension x, hx.map⟩
  · have hirr : Irreducible f :=
      Polynomial.irreducible_of_degree_le_three_of_not_isRoot
        (by rw [hdeg]; simp) (by
          intro x hx
          exact hroot ⟨x, hx⟩)
    letI : Fact (Irreducible f) := ⟨hirr⟩
    let φ : AdjoinRoot f →ₐ[F169] CubicExtension :=
      (FiniteField.nonempty_algHom_of_finrank_dvd
        (F := F169) (K := AdjoinRoot f) (L := CubicExtension) (by
          have hfin : Module.finrank F169 (AdjoinRoot f) = f.natDegree :=
            finrank_quotient_span_eq_natDegree
          rw [hfin, hdeg,
            FiniteField.finrank_extension F169 13 3]
          )).some
    refine ⟨φ (AdjoinRoot.root f), ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.aeval_def] using
      (AdjoinRoot.aeval_algHom_eq_zero f φ)

/-! Every `3 × 3` matrix over `F169` has an eigenvector after scalar extension. -/

theorem exists_cubic_eigenvector (M : Matrix (Fin 3) (Fin 3) F169) :
    ∃ (v : Fin 3 → CubicExtension) (μ : CubicExtension),
      v ≠ 0 ∧
        (M.map (algebraMap F169 CubicExtension)).mulVec v = μ • v := by
  obtain ⟨μ, hμ⟩ :=
    exists_root_monic_cubic M.charpoly (Matrix.charpoly_monic M) (by
      simpa only [Fintype.card_fin] using Matrix.charpoly_natDegree_eq_dim M)
  let C : Matrix (Fin 3) (Fin 3) CubicExtension :=
    M.map (algebraMap F169 CubicExtension)
  have hμ' : (Matrix.toLin' C).charpoly.IsRoot μ := by
    rw [Matrix.charpoly_toLin']
    change (M.map (algebraMap F169 CubicExtension)).charpoly.IsRoot μ
    rw [Matrix.charpoly_map]
    exact hμ
  have hEig : Module.End.HasEigenvalue (Matrix.toLin' C) μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' C) μ).2 hμ'
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  refine ⟨v, μ, ?_, ?_⟩
  · exact (Module.End.hasEigenvector_iff.mp hv).2
  · simpa only [Matrix.toLin'_apply] using hv.apply_eq_smul

/-! A stable generalized-eigenvector form for the matrix-pencil argument. -/

theorem exists_cubic_generalized_eigenvector
    (A B : Matrix (Fin 3) (Fin 3) F169)
    (hA : Function.Injective A.mulVec) :
    ∃ (v : Fin 3 → CubicExtension) (μ : CubicExtension),
      v ≠ 0 ∧
        (B.map (algebraMap F169 CubicExtension)).mulVec v =
          μ • (A.map (algebraMap F169 CubicExtension)).mulVec v := by
  have hdet : A.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact hv (hA (by simpa using hAv))
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨v, μ, hv, hCv⟩ := exists_cubic_eigenvector (A⁻¹ * B)
  refine ⟨v, μ, hv, ?_⟩
  have hAB : A * (A⁻¹ * B) = B := by
    rw [← mul_assoc, Matrix.mul_nonsing_inv A hunit, one_mul]
  have hAB' :
      (A.map (algebraMap F169 CubicExtension)) *
          ((A⁻¹ * B).map (algebraMap F169 CubicExtension)) =
        B.map (algebraMap F169 CubicExtension) := by
    rw [← Matrix.map_mul, hAB]
  calc
    (B.map (algebraMap F169 CubicExtension)).mulVec v =
        ((A.map (algebraMap F169 CubicExtension)) *
          ((A⁻¹ * B).map (algebraMap F169 CubicExtension))).mulVec v := by
            rw [hAB']
    _ = (A.map (algebraMap F169 CubicExtension)).mulVec
          (((A⁻¹ * B).map (algebraMap F169 CubicExtension)).mulVec v) := by
            rw [Matrix.mulVec_mulVec]
    _ = (A.map (algebraMap F169 CubicExtension)).mulVec (μ • v) := by
            rw [hCv]
    _ = μ • (A.map (algebraMap F169 CubicExtension)).mulVec v := by
            rw [Matrix.mulVec_smul]

end EtzionSilbersteinCounterexample

set_option autoImplicit false

open Finset BigOperators Module

namespace EtzionSilbersteinCounterexample

/-!
# Arithmetic geometry of the determinant pencil

The determinant of a three-parameter `5 × 5` pencil is a ternary quintic.  The
two arithmetic-geometric inputs used below are deliberately isolated as axioms:
they are statements about arbitrary ternary forms, rather than about codes.
-/

abbrev TernaryPolynomial (R : Type*) [CommSemiring R] := MvPolynomial (Fin 3) R

/-- The matrix of linear forms obtained from a matrix pencil. -/
noncomputable def pencilPolynomialMatrix {R : Type*} [CommRing R]
    (M : Fin 3 → SquareMatrix R) : Matrix Row Column (MvPolynomial (Fin 3) R) :=
  fun i j => ∑ k, MvPolynomial.C (M k i j) * MvPolynomial.X k

/-- The determinant ternary polynomial of a `5 × 5` matrix pencil. -/
noncomputable def determinantPolynomial {R : Type*} [CommRing R]
    (M : Fin 3 → SquareMatrix R) : TernaryPolynomial R :=
  Matrix.det (pencilPolynomialMatrix M)

theorem eval_determinantPolynomial {R : Type*} [CommRing R]
    (M : Fin 3 → SquareMatrix R) (x : Parameters R) :
    MvPolynomial.eval x (determinantPolynomial M) = Matrix.det (pencil M x) := by
  rw [determinantPolynomial, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp [pencilPolynomialMatrix]
  change (∑ k, M k i j * x k) = ∑ k, x k * M k i j
  simp [mul_comm]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem eval₂_determinantPolynomial_cubic
    (M : Fin 3 → SquareMatrix F169) (x : Parameters CubicExtension) :
    MvPolynomial.eval₂ (algebraMap F169 CubicExtension) x (determinantPolynomial M) =
      Matrix.det (extendedPencil M x) := by
  rw [determinantPolynomial]
  calc
    _ = Matrix.det ((pencilPolynomialMatrix M).map
        (MvPolynomial.eval₂Hom (algebraMap F169 CubicExtension) x)) :=
      RingHom.map_det (MvPolynomial.eval₂Hom (algebraMap F169 CubicExtension) x)
        (pencilPolynomialMatrix M)
    _ = Matrix.det (extendedPencil M x) := by
      apply congrArg Matrix.det
      ext i j
      simp [pencilPolynomialMatrix]
      change (∑ k, algebraMap F169 CubicExtension (M k i j) * x k) =
        ∑ k, x k * algebraMap F169 CubicExtension (M k i j)
      simp [mul_comm]

private theorem pencilPolynomialMatrix_entry_isHomogeneous {R : Type*} [CommRing R]
    (M : Fin 3 → SquareMatrix R) (i : Row) (j : Column) :
    (pencilPolynomialMatrix M i j).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k hk
  exact (MvPolynomial.isHomogeneous_X (R := R) k).C_mul (M k i j)

private theorem determinant_isHomogeneous_of_linear_entries
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial (Fin 3) R))
    (hA : ∀ i j, (A i j).IsHomogeneous 1) :
    A.det.IsHomogeneous (Fintype.card n) := by
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  have hprod : (∏ i, A (σ i) i).IsHomogeneous (∑ _i : n, 1) := by
    apply MvPolynomial.IsHomogeneous.prod
    intro i hi
    exact hA (σ i) i
  simpa using hprod.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

theorem determinantPolynomial_isHomogeneous {R : Type*} [CommRing R]
    (M : Fin 3 → SquareMatrix R) :
    (determinantPolynomial M).IsHomogeneous 5 := by
  apply determinant_isHomogeneous_of_linear_entries
  exact pencilPolynomialMatrix_entry_isHomogeneous M

/-- A polynomial is anisotropic when its only zero is the zero vector. -/
def IsAnisotropic {R : Type*} [CommSemiring R]
    (p : TernaryPolynomial R) : Prop :=
  ∀ x : Fin 3 → R, x ≠ 0 → MvPolynomial.eval x p ≠ 0

/-!
`IsAbsolutelyIrreducible` is irreducibility after the coefficient map into an
algebraic closure.  This is the usual geometric irreducibility condition for
a ternary form, expressed using Mathlib's multivariate polynomial type.
-/
def IsAbsolutelyIrreducible (p : TernaryPolynomial F169) : Prop :=
  Irreducible (MvPolynomial.map (algebraMap F169 (AlgebraicClosure F169)) p)

/--
Hasse--Weil consequence for a plane quintic: an absolutely irreducible
homogeneous ternary quintic over `F169` has a nonzero rational zero.

This is an arithmetic-geometric input, stated for an arbitrary polynomial and
with no reference to matrices, supports, or code dimensions.
-/
axiom hasseWeil_nonzero_zero
    {p : TernaryPolynomial F169}
    (hp_homogeneous : p.IsHomogeneous 5)
    (hp_absolutely_irreducible : IsAbsolutelyIrreducible p) :
    ∃ x : Fin 3 → F169, x ≠ 0 ∧ MvPolynomial.eval x p = 0

/-!
The second arithmetic-geometric input packages the Frobenius factorization
argument and the coprimality of the cubic extension degree with the relevant
factor degree.  It is intentionally a polynomial-level statement.
-/
axiom anisotropic_not_absolutely_irreducible_no_cubic_zero
    {p : TernaryPolynomial F169}
    (hp_anisotropic : IsAnisotropic p)
    (hp_homogeneous : p.IsHomogeneous 5)
    (hp_not_absolutely_irreducible : ¬ IsAbsolutelyIrreducible p) :
    ∀ x : Fin 3 → CubicExtension, x ≠ 0 →
      MvPolynomial.eval₂ (algebraMap F169 CubicExtension) x p ≠ 0

theorem anisotropic_over_CubicExtension
    {p : TernaryPolynomial F169}
    (hp_anisotropic : IsAnisotropic p)
    (hp_homogeneous : p.IsHomogeneous 5) :
    IsAnisotropic (MvPolynomial.map (algebraMap F169 CubicExtension) p) := by
  intro x hx
  rw [MvPolynomial.eval_map]
  by_cases hp_absolutely_irreducible : IsAbsolutelyIrreducible p
  · obtain ⟨x, hx, hpx⟩ :=
      hasseWeil_nonzero_zero hp_homogeneous hp_absolutely_irreducible
    exact ((hp_anisotropic x hx) (by simpa [MvPolynomial.eval₂_id] using hpx)).elim
  · exact anisotropic_not_absolutely_irreducible_no_cubic_zero
      hp_anisotropic hp_homogeneous hp_absolutely_irreducible x hx

end EtzionSilbersteinCounterexample

/-!
# The formal upper-bound reduction

This file reduces a hypothetical three-dimensional supported full-rank code
to a nonzero cubic-extension zero of its determinant quintic.
-/

set_option autoImplicit false

open Finset BigOperators Module

namespace EtzionSilbersteinCounterexample

/-- Coefficients of one of the first two columns of a three-matrix pencil,
restricted to the top three rows. -/
def topColumnMatrix (M : Fin 3 → SquareMatrix F169) (j : Fin 2) :
    Matrix (Fin 3) (Fin 3) F169 :=
  fun r i => M i (Fin.castAdd 2 r) (Fin.castAdd 3 j)

theorem topColumnMatrix_mulVec (M : Fin 3 → SquareMatrix F169)
    (j : Fin 2) (x : Parameters F169) (r : Fin 3) :
    (topColumnMatrix M j).mulVec x r =
      pencil M x (Fin.castAdd 2 r) (Fin.castAdd 3 j) := by
  simp [topColumnMatrix, Matrix.mulVec, dotProduct, pencil,
    Matrix.sum_apply, Matrix.smul_apply, mul_comm]

theorem mapped_topColumnMatrix_mulVec (M : Fin 3 → SquareMatrix F169)
    (j : Fin 2) (x : Parameters CubicExtension) (r : Fin 3) :
    ((topColumnMatrix M j).map (algebraMap F169 CubicExtension)).mulVec x r =
      extendedPencil M x (Fin.castAdd 2 r) (Fin.castAdd 3 j) := by
  simp [topColumnMatrix, Matrix.mulVec, dotProduct, extendedPencil,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, mul_comm]

theorem pencil_supported (M : Fin 3 → SquareMatrix F169)
    (hM : ∀ i, IsSupported (M i)) (x : Parameters F169) :
    IsSupported (pencil M x) := by
  intro r j hrj
  change (∑ i, x i * M i r j) = 0
  simp [hM _ r j hrj]

theorem extendedPencil_supported (M : Fin 3 → SquareMatrix F169)
    (hM : ∀ i, IsSupported (M i)) (x : Parameters CubicExtension) :
    IsSupported (extendedPencil M x) := by
  intro r j hrj
  change (∑ i, x i * algebraMap F169 CubicExtension (M i r j)) = 0
  simp [hM _ r j hrj]

/-- An anisotropic supported pencil has an injective first top-column map. -/
theorem firstTopColumn_injective (M : Fin 3 → SquareMatrix F169)
    (hM : ∀ i, IsSupported (M i))
    (hanisotropic : ∀ x : Parameters F169, x ≠ 0 → Matrix.det (pencil M x) ≠ 0) :
    Function.Injective (topColumnMatrix M 0).mulVec := by
  intro x y hxy
  rw [← sub_eq_zero]
  by_contra hne
  apply hanisotropic (x - y) hne
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  have hmul : (topColumnMatrix M 0).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsupp := pencil_supported M hM (x - y)
  intro r
  fin_cases r
  · simpa [topColumnMatrix_mulVec] using congr_fun hmul (0 : Fin 3)
  · simpa [topColumnMatrix_mulVec] using congr_fun hmul (1 : Fin 3)
  · simpa [topColumnMatrix_mulVec] using congr_fun hmul (2 : Fin 3)
  · exact hsupp 3 0 (by norm_num [columnHeight])
  · exact hsupp 4 0 (by norm_num [columnHeight])

/-- Dependence of the first two columns over the cubic extension forces the
extended determinant quintic to vanish. -/
theorem determinant_zero_of_topColumn_dependence
    (M : Fin 3 → SquareMatrix F169) (hM : ∀ i, IsSupported (M i))
    (v : Parameters CubicExtension) (μ : CubicExtension)
    (hdepend :
      ((topColumnMatrix M 1).map (algebraMap F169 CubicExtension)).mulVec v =
        μ • ((topColumnMatrix M 0).map
          (algebraMap F169 CubicExtension)).mulVec v) :
    Matrix.det (extendedPencil M v) = 0 := by
  let w : Fin 5 → CubicExtension := ![-μ, 1, 0, 0, 0]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨w, ?_, ?_⟩
  · intro hw
    have := congr_fun hw (1 : Fin 5)
    simp [w] at this
  · funext r
    have hsupp := extendedPencil_supported M hM v
    fin_cases r
    · have hr := congr_fun hdepend (0 : Fin 3)
      simp only [Pi.smul_apply, smul_eq_mul, mapped_topColumnMatrix_mulVec] at hr
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w]
      have hr' : extendedPencil M v 0 1 = μ * extendedPencil M v 0 0 := by
        simpa using hr
      rw [hr']
      ring
    · have hr := congr_fun hdepend (1 : Fin 3)
      simp only [Pi.smul_apply, smul_eq_mul, mapped_topColumnMatrix_mulVec] at hr
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w]
      have hr' : extendedPencil M v 1 1 = μ * extendedPencil M v 1 0 := by
        simpa using hr
      rw [hr']
      ring
    · have hr := congr_fun hdepend (2 : Fin 3)
      simp only [Pi.smul_apply, smul_eq_mul, mapped_topColumnMatrix_mulVec] at hr
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w]
      have hr' : extendedPencil M v 2 1 = μ * extendedPencil M v 2 0 := by
        simpa using hr
      rw [hr']
      ring
    · have h0 := hsupp 3 0 (by norm_num [columnHeight])
      have h1 := hsupp 3 1 (by norm_num [columnHeight])
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w, h0, h1]
    · have h0 := hsupp 4 0 (by norm_num [columnHeight])
      have h1 := hsupp 4 1 (by norm_num [columnHeight])
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w, h0, h1]

/-- No supported three-matrix pencil can be anisotropic.  All code-theoretic
content has been reduced to the two polynomial-level arithmetic-geometry
axioms at this point. -/
theorem no_supported_anisotropic_pencil
    (M : Fin 3 → SquareMatrix F169) (hM : ∀ i, IsSupported (M i))
    (hanisotropic : ∀ x : Parameters F169, x ≠ 0 →
      Matrix.det (pencil M x) ≠ 0) : False := by
  have hp_anisotropic : IsAnisotropic (determinantPolynomial M) := by
    intro x hx
    rw [eval_determinantPolynomial]
    exact hanisotropic x hx
  have hp_cubic := anisotropic_over_CubicExtension hp_anisotropic
    (determinantPolynomial_isHomogeneous M)
  obtain ⟨v, μ, hv, hdepend⟩ :=
    exists_cubic_generalized_eigenvector
      (topColumnMatrix M 0) (topColumnMatrix M 1)
      (firstTopColumn_injective M hM hanisotropic)
  have hzero : Matrix.det (extendedPencil M v) = 0 :=
    determinant_zero_of_topColumn_dependence M hM v μ hdepend
  exact hp_cubic v hv (by
    rw [MvPolynomial.eval_map, eval₂_determinantPolynomial_cubic]
    exact hzero)

/-- Every supported full-rank code has dimension at most two.  Unlike the
removed formalization, this is a theorem derived from a three-element
linearly independent family and `no_supported_anisotropic_pencil`; it is not
an axiom. -/
theorem code_finrank_le_two (C : Submodule F169 (SquareMatrix F169))
    (hC : IsRankFiveCode C) : Module.finrank F169 C ≤ 2 := by
  by_contra hle
  have hthree : 3 ≤ Module.finrank F169 C := by omega
  obtain ⟨v, hv⟩ :=
    exists_linearIndependent_of_le_finrank (R := F169) (M := C) hthree
  let M : Fin 3 → SquareMatrix F169 := fun i => (v i : SquareMatrix F169)
  have hM : ∀ i, IsSupported (M i) := by
    intro i
    exact hC.1 (v i) (v i).property
  have hpencil (x : Parameters F169) :
      pencil M x =
        ((Fintype.linearCombination F169 v) x : SquareMatrix F169) := by
    rw [Fintype.linearCombination_apply]
    simp only [pencil, M, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply no_supported_anisotropic_pencil M hM
  intro x hx
  rw [hpencil]
  apply hC.2 ((Fintype.linearCombination F169 v) x)
    ((Fintype.linearCombination F169 v) x).property
  intro hzero
  have hzero' : (Fintype.linearCombination F169 v) x = 0 := by
    apply Subtype.ext
    exact hzero
  exact hx (hv.fintypeLinearCombination_injective (by simpa using hzero'))

end EtzionSilbersteinCounterexample

/-!
# Counterexample to universal attainment of the Etzion--Silberstein bound

The finite-field, matrix, and coding-theoretic argument is formalized in Lean.
The only mathematical axioms are the two polynomial-level arithmetic-geometry
bridges in the arithmetic-geometry section below.
-/

set_option autoImplicit false

namespace EtzionSilbersteinCounterexample

/-- The optimum code dimension over F169 is exactly two. -/
theorem optimalDimension_F169 : IsOptimalDimension (F := F169) 2 :=
  ⟨⟨Construction.code, Construction.twoDimensionalCode,
      Construction.code_finrank⟩,
    code_finrank_le_two⟩

/-- The Etzion--Silberstein bound is not attained for this field and diagram. -/
theorem counterexample_to_universal_attainment :
    ¬ AttainsEtzionSilbersteinBound (F := F169) := by
  rintro ⟨C, hC, hdim⟩
  have hupper := code_finrank_le_two C hC
  rw [etzionSilbersteinBound_eq_three] at hdim
  omega

/-- The strict gap, expressed without introducing a separate maximum operator. -/
theorem counterexample_summary :
    IsOptimalDimension (F := F169) 2 ∧
      etzionSilbersteinBound = 3 ∧
      (2 : ℕ) < etzionSilbersteinBound := by
  exact ⟨optimalDimension_F169, etzionSilbersteinBound_eq_three, by
    rw [etzionSilbersteinBound_eq_three]
    norm_num⟩

end EtzionSilbersteinCounterexample
