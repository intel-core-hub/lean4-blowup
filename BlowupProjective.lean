import BlowupGeometry

/-!
# ブローアップ(層4: 射影的な構成)

`𝔸² × ℙ¹` の閉集合を、座標 `(x, y, t, u)`(`MvPolynomial (Fin 4) k`、変数 `0, 1, 2, 3`)の
**`(t, u)` について斉次な多項式の零点集合**として記述する。

* `IsBihom d G`:`G(P, c v) = c^d G(P, v)`(`(t, u)` について `d` 次斉次)
* `evalPair P v G`:`G(P₀, P₁, v₀, v₁)`
* `projZeroSet G`:`{(P, L) | G(P, rep L) = 0}`(斉次なら代表元の取り方によらない)
* `blowEq = x u − t y` は 1 次斉次で、`blowupSet = projZeroSet blowEq`
* `E = blowupSet ∩ Z(x) ∩ Z(y)`、`φ⁻¹(Y) = projZeroSet (f(x, y))`
-/

open MvPolynomial Projectivization

namespace Blowup

section projective

variable {k : Type*} [Field k]

/-- `G(P₀, P₁, v₀, v₁)`。 -/
noncomputable def evalPair (P v : Fin 2 → k) (G : MvPolynomial (Fin 4) k) : k :=
  MvPolynomial.eval ![P 0, P 1, v 0, v 1] G

lemma evalPair_add (P v : Fin 2 → k) (p q : MvPolynomial (Fin 4) k) :
    evalPair P v (p + q) = evalPair P v p + evalPair P v q := map_add _ _ _

lemma evalPair_sub (P v : Fin 2 → k) (p q : MvPolynomial (Fin 4) k) :
    evalPair P v (p - q) = evalPair P v p - evalPair P v q := map_sub _ _ _

lemma evalPair_mul (P v : Fin 2 → k) (p q : MvPolynomial (Fin 4) k) :
    evalPair P v (p * q) = evalPair P v p * evalPair P v q := map_mul _ _ _

lemma evalPair_X0 (P v : Fin 2 → k) : evalPair P v (X 0) = P 0 := (eval_X (0 : Fin 4)).trans rfl

lemma evalPair_X1 (P v : Fin 2 → k) : evalPair P v (X 1) = P 1 := (eval_X (1 : Fin 4)).trans rfl

lemma evalPair_X2 (P v : Fin 2 → k) : evalPair P v (X 2) = v 0 := (eval_X (2 : Fin 4)).trans rfl

lemma evalPair_X3 (P v : Fin 2 → k) : evalPair P v (X 3) = v 1 := (eval_X (3 : Fin 4)).trans rfl

/-- `G` は `(t, u)` について `d` 次斉次。 -/
def IsBihom (d : ℕ) (G : MvPolynomial (Fin 4) k) : Prop :=
  ∀ (P v : Fin 2 → k) (c : k), evalPair P (c • v) G = c ^ d * evalPair P v G

lemma evalPair_smul_eq_zero_iff {d : ℕ} {G : MvPolynomial (Fin 4) k} (hG : IsBihom d G)
    (P v : Fin 2 → k) {c : k} (hc : c ≠ 0) :
    evalPair P (c • v) G = 0 ↔ evalPair P v G = 0 := by
  have hcd : c ^ d ≠ 0 := pow_ne_zero _ hc
  rw [hG P v c]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hcd
  · intro h
    rw [h, mul_zero]

/-- `G` の `𝔸² × ℙ¹` での零点集合(代表元で判定する)。 -/
def projZeroSet (G : MvPolynomial (Fin 4) k) :
    Set ((Fin 2 → k) × Projectivization k (Fin 2 → k)) :=
  {z | evalPair z.1 z.2.rep G = 0}

/-- 斉次な `G` の零点判定は、任意の代表元でできる。 -/
lemma mem_projZeroSet_iff {d : ℕ} {G : MvPolynomial (Fin 4) k} (hG : IsBihom d G)
    {P v : Fin 2 → k} {L : Projectivization k (Fin 2 → k)} (hv : v ≠ 0) (h : mk k v hv = L) :
    (P, L) ∈ projZeroSet G ↔ evalPair P v G = 0 := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff k _ _ L.rep_nonzero hv).mp ((mk_rep L).trans h.symm)
  have e : L.rep = (a : k) • v := ha.symm.trans (Units.smul_def a v)
  change evalPair P L.rep G = 0 ↔ _
  rw [e]
  exact evalPair_smul_eq_zero_iff hG P v a.ne_zero

/-- ブローアップの定義方程式 `x u − t y`(変数 `x, y, t, u = X 0, X 1, X 2, X 3`)。 -/
noncomputable def blowEq (k : Type*) [Field k] : MvPolynomial (Fin 4) k := X 0 * X 3 - X 2 * X 1

lemma evalPair_blowEq (P v : Fin 2 → k) :
    evalPair P v (blowEq k) = P 0 * v 1 - v 0 * P 1 := by
  rw [blowEq, evalPair_sub, evalPair_mul, evalPair_mul, evalPair_X0, evalPair_X3, evalPair_X2,
    evalPair_X1]

lemma isBihom_blowEq : IsBihom 1 (blowEq k) := by
  intro P v c
  rw [evalPair_blowEq, evalPair_blowEq]
  change P 0 * (c * v 1) - c * v 0 * P 1 = c ^ 1 * (P 0 * v 1 - v 0 * P 1)
  ring

/-- **ブローアップは `𝔸² × ℙ¹` の射影的な(`(t,u)` に斉次な方程式で切られる)部分集合**。 -/
theorem blowupSet_eq_projZeroSet : blowupSet k = projZeroSet (blowEq k) := by
  ext ⟨P, L⟩
  change P 0 * L.rep 1 = L.rep 0 * P 1 ↔ evalPair P L.rep (blowEq k) = 0
  rw [evalPair_blowEq]
  exact sub_eq_zero.symm

lemma isBihom_X0 : IsBihom 0 (X 0 : MvPolynomial (Fin 4) k) := by
  intro P v c
  rw [evalPair_X0, evalPair_X0]
  simp

lemma isBihom_X1 : IsBihom 0 (X 1 : MvPolynomial (Fin 4) k) := by
  intro P v c
  rw [evalPair_X1, evalPair_X1]
  simp

lemma mem_projZeroSet_X0 (P : Fin 2 → k) (L : Projectivization k (Fin 2 → k)) :
    (P, L) ∈ projZeroSet (X 0 : MvPolynomial (Fin 4) k) ↔ P 0 = 0 := by
  change evalPair P L.rep _ = 0 ↔ _
  rw [evalPair_X0]

lemma mem_projZeroSet_X1 (P : Fin 2 → k) (L : Projectivization k (Fin 2 → k)) :
    (P, L) ∈ projZeroSet (X 1 : MvPolynomial (Fin 4) k) ↔ P 1 = 0 := by
  change evalPair P L.rep _ = 0 ↔ _
  rw [evalPair_X1]

/-- **例外因子 `E` も射影的**:`E = X ∩ Z(x) ∩ Z(y)`。 -/
theorem exceptional_eq_projective :
    exceptional k = blowupSet k ∩ (projZeroSet (X 0) ∩ projZeroSet (X 1)) := by
  ext ⟨P, L⟩
  simp only [exceptional, Set.mem_inter_iff, Set.mem_setOf_eq, mem_projZeroSet_X0,
    mem_projZeroSet_X1]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro rfl
    simp
  · rintro ⟨a0, a1⟩
    ext i
    fin_cases i <;> simp [a0, a1]

/-- `f(x, y)` を `k[x, y, t, u]` の元と見る(`(t, u)` について 0 次斉次)。 -/
noncomputable def pullXY (f : Poly k) : MvPolynomial (Fin 4) k :=
  MvPolynomial.aeval (![X 0, X 1] : Fin 2 → MvPolynomial (Fin 4) k) f

lemma evalPair_pullXY (f : Poly k) (P v : Fin 2 → k) : evalPair P v (pullXY f) = eval P f := by
  unfold evalPair pullXY
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    congr 1
    fin_cases i <;> simp

/-- **全 transform の `X` への制限は `φ⁻¹(Y)`**:`projZeroSet (f(x,y)) = {z | f(z.1) = 0}`。 -/
theorem projZeroSet_pullXY (f : Poly k) :
    projZeroSet (pullXY f) = {z | eval z.1 f = 0} := by
  ext ⟨P, L⟩
  exact (show evalPair P L.rep (pullXY f) = 0 ↔ eval P f = 0 by rw [evalPair_pullXY])

/-- `φ⁻¹(Y) ∩ X` も射影的:`blowupSet ∩ projZeroSet (f(x,y))`。 -/
theorem preimage_eq_projective (f : Poly k) :
    blowupSet k ∩ {z | eval z.1 f = 0} = projZeroSet (blowEq k) ∩ projZeroSet (pullXY f) := by
  rw [blowupSet_eq_projZeroSet, projZeroSet_pullXY]

/-- 斉次多項式の族の零点集合として書ける集合(= `𝔸² × ℙ¹` の射影的閉集合)。 -/
def IsProjClosed (S : Set ((Fin 2 → k) × Projectivization k (Fin 2 → k))) : Prop :=
  ∃ 𝒢 : Set (MvPolynomial (Fin 4) k), (∀ G ∈ 𝒢, ∃ d, IsBihom d G) ∧
    S = {z | ∀ G ∈ 𝒢, z ∈ projZeroSet G}

theorem isProjClosed_blowupSet : IsProjClosed (blowupSet k) := by
  refine ⟨{blowEq k}, ?_, ?_⟩
  · intro G hG
    rw [Set.mem_singleton_iff] at hG
    exact ⟨1, hG ▸ isBihom_blowEq⟩
  · rw [blowupSet_eq_projZeroSet]
    ext z
    simp

theorem isProjClosed_exceptional : IsProjClosed (exceptional k) := by
  refine ⟨{blowEq k, X 0, X 1}, ?_, ?_⟩
  · intro G hG
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl | rfl
    · exact ⟨1, isBihom_blowEq⟩
    · exact ⟨0, isBihom_X0⟩
    · exact ⟨0, isBihom_X1⟩
  · rw [exceptional_eq_projective, blowupSet_eq_projZeroSet]
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩ G hG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
      rcases hG with rfl | rfl | rfl
      exacts [h1, h2, h3]
    · intro h
      exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩

end projective

end Blowup
