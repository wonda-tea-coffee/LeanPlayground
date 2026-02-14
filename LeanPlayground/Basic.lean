/-
# √2 の無理数性の証明 (Proof of Irrationality of √2)

Mathlibを使わず、Lean 4 の標準ライブラリのみで √2 が無理数であることを証明する。

## 証明の方針
背理法（無限降下法）を用いる。p² = 2q² と仮定すると、
p が偶数 → q が偶数 → ... と無限に 2 で割れることになり、
p + q の値が際限なく小さくなる。これは自然数の整礎性に矛盾する。

具体的には「p² = 2q² かつ p + q ≤ n ならば q = 0」を
n に関する帰納法で示す。
-/

/-! ## 補題: n² が偶数ならば n も偶数 -/

/-- n² が偶数ならば n も偶数。
    対偶を用いる: n が奇数なら (n%2)*(n%2) % 2 = 1*1 % 2 = 1 で n² も奇数。-/
theorem even_of_even_sq (n : Nat) (h : 2 ∣ n * n) : 2 ∣ n := by
  have hmul : n * n % 2 = (n % 2) * (n % 2) % 2 := Nat.mul_mod n n 2
  have hnn : n * n % 2 = 0 := by obtain ⟨k, hk⟩ := h; omega
  rw [hnn] at hmul
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact ⟨n / 2, by omega⟩
  · rw [h1] at hmul; simp at hmul

/-! ## 算術の補題 -/

/-- (2a)² = 2·(2·a²) -/
private theorem mul2_sq (a : Nat) : 2 * a * (2 * a) = 2 * (2 * (a * a)) := by
  calc 2 * a * (2 * a)
      = 2 * (a * (2 * a)) := by rw [Nat.mul_assoc]
    _ = 2 * (2 * a * a)   := by rw [Nat.mul_comm a (2 * a)]
    _ = 2 * (2 * (a * a)) := by rw [Nat.mul_assoc]

/-! ## 主定理: 無限降下法による証明 -/

/-- p² = 2q² かつ p + q ≤ n ならば q = 0。
    n に関する帰納法（無限降下法）で証明する。-/
theorem sqrt2_descent (n : Nat) :
    ∀ p q : Nat, p * p = 2 * (q * q) → p + q ≤ n → q = 0 := by
  induction n with
  | zero =>
    intro p q _ h_bound; omega
  | succ n ih =>
    intro p q h_eq h_bound
    -- Step 1: p² = 2q² より p² は偶数、よって p は偶数
    have h_p_even := even_of_even_sq p ⟨q * q, h_eq⟩
    obtain ⟨k, hk⟩ := h_p_even
    -- Step 2: p = 2k を代入して (2k)² = 2q²、すなわち 4k² = 2q²
    -- 両辺を 2 で割って q² = 2k²
    have h_4k : 2 * (2 * (k * k)) = 2 * (q * q) := by
      rw [← mul2_sq k, ← hk]; exact h_eq
    have h_q_eq : q * q = 2 * (k * k) :=
      (Nat.mul_left_cancel (by omega : 0 < 2) h_4k).symm
    -- Step 3: q² = 2k² より q² は偶数、よって q は偶数
    have h_q_even := even_of_even_sq q ⟨k * k, h_q_eq⟩
    obtain ⟨m, hm⟩ := h_q_even
    -- Step 4: q = 2m を代入して (2m)² = 2k²、すなわち 4m² = 2k²
    -- 両辺を 2 で割って k² = 2m²
    have h_4m : 2 * (2 * (m * m)) = 2 * (k * k) := by
      rw [← mul2_sq m, ← hm]; exact h_q_eq
    have h_k_eq : k * k = 2 * (m * m) :=
      (Nat.mul_left_cancel (by omega : 0 < 2) h_4m).symm
    -- Step 5: k + m < p + q なので帰納法の仮定が適用できる
    -- p = 2k, q = 2m より 2(k+m) = p+q ≤ n+1 なので k+m ≤ n
    have h_smaller : k + m ≤ n := by omega
    -- 帰納法の仮定より m = 0
    have hm0 := ih k m h_k_eq h_smaller
    -- m = 0 なので q = 2·0 = 0
    omega

/-! ## √2 の無理数性 -/

/-- **√2 の無理数性（自然数版）**：
    p² = 2q² を満たす自然数 p, q について q = 0 が成り立つ。
    すなわち、正の有理数 p/q で二乗して 2 になるものは存在しない。-/
theorem sqrt_two_irrational (p q : Nat) (h : p * p = 2 * (q * q)) : q = 0 :=
  sqrt2_descent (p + q) p q h (Nat.le_refl _)

/-- **系**：q ≠ 0 のとき p² ≠ 2q² -/
theorem sq_ne_two_mul_sq (p q : Nat) (hq : q ≠ 0) : p * p ≠ 2 * (q * q) :=
  fun h => hq (sqrt_two_irrational p q h)

/-- **√2 の無理数性（整数版）**：
    p² = 2q² を満たす整数 p, q について q = 0 が成り立つ。-/
theorem sqrt_two_irrational_int (p q : Int) (h : p * p = 2 * (q * q)) : q = 0 := by
  have hp := @Int.natAbs_mul_self (a := p)
  have hq := @Int.natAbs_mul_self (a := q)
  have h_nat : p.natAbs * p.natAbs = 2 * (q.natAbs * q.natAbs) := by omega
  have := sqrt_two_irrational p.natAbs q.natAbs h_nat
  omega
