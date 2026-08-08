A baby construction of surreal numbers in Lean 4, initiated from an undergraduate independent study project in Fall 2025.
Via vibe-coding, we formalize the addition and multiplication of surreal numbers, and prove that it is a
totally ordered commutative ring.

## Blueprint

The mathematical blueprint and theorem dependency graph live in [`blueprint/`](blueprint/).
They document the actual Lean proof path from finite games and the recursive order through the
simultaneous Conway A/B/C induction to the linear ordered commutative ring structure on short
surreal numbers.

For a local build, follow [`blueprint/README.md`](blueprint/README.md). The web build includes an
interactive dependency graph and links each formalized item to its Lean declaration.
