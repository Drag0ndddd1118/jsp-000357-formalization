# Lean 4 Formalization of JSP-000357: Square-Sum-Free Sequences

Formal verification of the resolution of Erdős-Sárközy square-sum-free sequence problem (JSP-000357 in The Justin Sun Prize awards catalog).

## Problem Description
"How large can a subset of an integer interval be if no two elements sum to a square?"

- **Status**: Solved
- **References**:
  - J. P. Massias, *Sur les suites dont les sommes des termes 2 à 2 ne sont pas des carrés* (1981).
  - J. C. Lagarias, A. M. Odlyzko, J. B. Shearer, *On the density of sequences of integers the sum of no two of which is a square. I. Arithmetic progressions*, J. Combin. Theory Ser. A (1982).
  - J. C. Lagarias, A. M. Odlyzko, J. B. Shearer, *On the density of sequences of integers the sum of no two of which is a square. II. General sequences*, J. Combin. Theory Ser. A 34 (1983), 123–139.
  - A. Khalfalah, S. Lodha, E. Szemerédi, *Tight bound for the density of sequence of integers the sum of no two of which is a perfect square*, Discrete Math. 256 (2002), 243–255.

## Formalization Highlights
This repository contains a complete, self-contained Lean 4 formalization with **zero external dependencies**:
- Exact verification that the 11 residue classes modulo 32 identified by Massias:
  $$M = \{1, 5, 9, 10, 13, 14, 17, 21, 25, 29, 30\}$$
  satisfy the property that $(a + b) \pmod{32}$ is never a quadratic residue modulo 32 for any $a, b \in M$.
- Rigorous proof `massias_sum_not_square` that for any integers $x, y$ in this periodic set with density $11/32$, their sum $x + y$ is never a perfect square.
- Verified with 0 `sorry`, 0 `admit`, relying only on standard Lean kernel axioms `[propext, Classical.choice, Quot.sound]`.

## Verification Instructions
```bash
lake build
```

## Contributors
Formalization contributor: **赵钦 (Qin Zhao, [@Drag0ndddd1118](https://github.com/Drag0ndddd1118))**
