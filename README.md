# SIDE-global-section

**Subject:** the construction era's verified Lean material for the global section — the
restricted product of the local Sonin closures over the places of ℚ, its `E₁` sector, the
finite-place models (charts, towers, sector arithmetic, quotient shadows), and the
purity-and-distance results at the banked cells. Companion to the build document
`THE_GLOBAL_SECTION.md` v1.0 (PLACE-papers, `phase2/method/`) and the relay acts it
consolidates.

**The register sentence, exactly:** *RH reduced to a single located clause, reduction
machine-verified* — never wider. Nothing in this repository moves that register: the one open
content here is row 24 of the correspondence (file E's Prop — stated, not proved, not
claimed; its truth at complete roster is `h2`, and the register moves only via the closure
protocol).

**The range law:** every numerical statement in this repository is a finite-instance
statement at its banked cells and no wider. Deeper tower levels and the level-limit objects
are undecided by these terminals, and nothing about them is claimed.

## Structure

- **`Core/`** — the vanilla load-bearing layer: **212 terminals** (103 construction-era + 11 purity-and-distance + 7 silence-theorem + 8 Plancherel-shadow + 3 cross-place + 3 pairing + 3 twisted + 3 deficit + 22 character-sum + 3 flatness + 3 silence-only-if + 6 product-minus-sum + 3 metaplectic-root + 2 twisted-root + 3 theta + 5 odd-pairing + 2 product-law + 4 tower-limit + 5 phase-plane + 4 lefschetz + 3 frame-boundary + 3 fourth-visit + 3 theta-continuation) across 40 modules plus their AxiomCheck
  audit files. Vanilla Lean 4 (`v4.29.1`, pinned in `lean-toolchain`), **no Mathlib import,
  decide/rfl only; every terminal prints "does not depend on any axioms"** — re-verified at
  assembly, `AXIOM_PRINTS.txt` (212/212). No terminal failed the bar; none is excluded.
- **`Interfaces/`** — the five Mathlib-facing files, each an **interface to the field's
  objects, never load-bearing for the programme's own claims** (the architecture ruling on
  their face). Expected profile `{propext, Classical.choice, Quot.sound}`; built against
  Mathlib at the declared pin (`v4.30.0-rc1`, mathlib4 `cecd0c4d56`); prints re-run at
  assembly, `AXIOM_PRINTS_INTERFACES.txt`. `FiniteInstanceIdentity.lean` is the one
  deliberate boundary object (correspondence row 24).
- **`CORRESPONDENCE.md`** — the spine: one row per keystone statement, with terminal names,
  verbatim axiom prints, three-grade rubric grades, and honest rows where a statement has no
  terminal.
- **`AllPrints.lean` / `AXIOM_PRINTS.txt`** — the generated audit driver and its output.

## Building (the verified path — no lakefile is shipped; these are the commands the assembly actually ran)

Core: `lean` at the pinned toolchain compiles each module standalone (sibling imports via
`LEAN_PATH`); `AllPrints.lean` re-runs every print. Interfaces: elaborate against a mathlib4
checkout at the declared pin (`lake env lean <file>` from the checkout).

## Provenance

Extracted from the relay working layer (`psinary-sketch/relay`, `tools/lean/`) at the
residence ruling of 2026-08-20; the relay copies carry residence notes pointing here. The
registrations and banks behind every bench-certified premise remain relay-resident by design
(`relay/data/`, each registration banked before its run). The Zenodo deposits are untouched
by this repository's creation; nothing here deposits.

---

*AI disclosure: Computational workflow assisted by Claude (Anthropic). Mathematical content,
proof strategies, theorem statements, and editorial decisions are the author's.*
