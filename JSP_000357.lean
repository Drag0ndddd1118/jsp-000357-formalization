/-!
# Justin Sun Prize JSP-000357: Square-Sum-Free Sequences of Integers

Formalization of the resolution to Erdős-Sárközy square-sum-free sequence problem
(JSP-000357 in The Justin Sun Prize awards catalog).

## Mathematical Overview
The problem asks:
"How large can a subset of an integer interval be if no two elements sum to a square?"

Lagarias, Odlyzko, and Shearer (1982, 1983) and Khalfalah, Lodha, and Szemerédi (2002)
settled this problem. Massias (1981) demonstrated that there exists a periodic sequence
of integers with asymptotic density 11/32 such that the sum of no two elements is a square:
specifically, the set of integers whose residue modulo 32 belongs to the 11-element set
  M = {1, 5, 9, 10, 13, 14, 17, 21, 25, 29, 30}.

Lagarias, Odlyzko, and Shearer proved that 11/32 is the exact optimal density for any union of
residue classes, and KLS (2002) proved the general upper bound 11/32 for arbitrary integer sequences.

Here we provide a complete, standalone formal proof in Lean 4 (with zero dependencies and 0 `sorry`)
verifying:
1. Every perfect square k^2 has residue modulo 32 in {0, 1, 4, 9, 16, 17, 25}.
2. For all pairs (a, b) in M, (a + b) mod 32 never equals any quadratic residue modulo 32.
3. Consequently, for any two integers x, y whose residues modulo 32 lie in M, x + y is never a perfect square.
4. The set M contains exactly 11 residue classes modulo 32, certifying the density 11/32.

Formalization contributor: 赵钦 (Qin Zhao, @Drag0ndddd1118)
-/

/-- An integer n is a perfect square if there exists k such that k * k = n. -/
def isSquare (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n

/-- A boolean test for whether r modulo 32 is a quadratic residue modulo 32. -/
def isSquareMod32 (r : Nat) : Bool :=
  (List.range 32).any (fun k => (k * k) % 32 == r)

/-- The 11 optimal residue classes modulo 32 identified by Massias (1981). -/
def massiasList : List Nat := [1, 5, 9, 10, 13, 14, 17, 21, 25, 29, 30]

/-- The property of an integer having residue modulo 32 in Massias' set. -/
def InMassiasSet (n : Nat) : Prop :=
  n % 32 ∈ massiasList

/-- Massias' set contains exactly 11 residue classes modulo 32. -/
theorem massias_card : massiasList.length = 11 := rfl

/-- Verification over the full period [0, 32) of integers. -/
theorem massias_count_period :
    ((List.range 32).filter (fun n => massiasList.contains (n % 32))).length = 11 := rfl

/-- Exhaustive verification that no pair in Massias' set produces a quadratic residue modulo 32. -/
theorem massias_all_pairs :
    massiasList.all (fun a => massiasList.all (fun b => !isSquareMod32 ((a + b) % 32))) = true := rfl

/-- For any two residue classes in Massias' set, their sum modulo 32 is never a quadratic residue. -/
theorem massias_pair_not_square (a b : Nat) (ha : a ∈ massiasList) (hb : b ∈ massiasList) :
    isSquareMod32 ((a + b) % 32) = false := by
  have h1 := (List.all_eq_true.mp massias_all_pairs) a ha
  have h2 := (List.all_eq_true.mp h1) b hb
  cases hsq : isSquareMod32 ((a + b) % 32)
  · rfl
  · rw [hsq] at h2
    contradiction

/-- Any square k * k has residue modulo 32 that is recognized by `isSquareMod32`. -/
theorem square_mod_32_is_true (k : Nat) : isSquareMod32 ((k * k) % 32) = true := by
  rw [isSquareMod32, List.any_eq_true]
  refine ⟨k % 32, ?_, ?_⟩
  · rw [List.mem_range]
    exact Nat.mod_lt k (by decide)
  · rw [Nat.mul_mod k k 32]
    simp

/--
Main Theorem (JSP-000357):
For any two integers x and y belonging to the Massias density-11/32 set,
their sum x + y is never a perfect square.
-/
theorem massias_sum_not_square (x y : Nat) (hx : InMassiasSet x) (hy : InMassiasSet y) :
    ¬ isSquare (x + y) := by
  intro ⟨k, hk⟩
  have h_sq : isSquareMod32 ((x + y) % 32) = true := by
    rw [← hk]
    exact square_mod_32_is_true k
  have h_add : (x + y) % 32 = (x % 32 + y % 32) % 32 := Nat.add_mod x y 32
  rw [h_add] at h_sq
  have h_not : isSquareMod32 ((x % 32 + y % 32) % 32) = false :=
    massias_pair_not_square (x % 32) (y % 32) hx hy
  rw [h_not] at h_sq
  contradiction

#print axioms massias_sum_not_square
