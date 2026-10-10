import JSP_000357

namespace JSP000357

/--
Formal statement of JSP-000357:
How large can a subset of an integer interval be if no two elements sum to a square?

Mathematical resolution:
J. P. Massias (1981) demonstrated that there exists a periodic sequence of integers with asymptotic density 11/32
such that no two elements sum to a square: specifically, integers whose residues modulo 32 lie in
M = {1, 5, 9, 10, 13, 14, 17, 21, 25, 29, 30}.
Lagarias, Odlyzko, and Shearer (1983) and Khalfalah, Lodha, and Szemerédi (2002) established that 11/32
is the exact optimal density for integer sequences with no square sums.
-/
def jsp000357Statement : Prop :=
  ∀ (x y : Nat), InMassiasSet x → InMassiasSet y → ¬ isSquare (x + y)

end JSP000357
