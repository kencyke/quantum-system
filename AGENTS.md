# AGENTS.md

## Important Instructions

- Use spaces only; never use tabs.
- Do not modify `lakefile.toml`.
- Do not use `python`, `cat`, `git checkout`, or `git reset`.
- When encountering the error `expected '{' or indented tactic sequence`, fix the indentation.
- Write all comments in English.
- Do not create namespaces or sections named `QuantumSystem`.
- Always implement full proofs. Do not ask whether to proceed full proofs or introduce helper lemmas. If needed for full proofs, implement all of them.
- Do not explore shorter proof paths before the current proof is completed. Only after completion may you consider improved approaches.
- Before ending the session, run `lake build` to ensure the project builds successfully.
- Do not stop until all todos or tasks are completed.
- If, after searching mathlib, the required lemmas cannot be found, do not stop. Implement them from scratch.
- Make modifications in order, starting from the top of the file.

## Prohibitions

The following tokens are strictly prohibited to use in this project:

- `sorry`
- `admit`
- `axiom`
- `set_option`
- `unsafe`
- `System`
- `open System`
- `Lean.Elab`
- `Lean.Meta`
- `Lean.Compiler`

## Search Mathlib

**DON'T:** Spend hours proving something mathlib already has

**DO:** Invest time in thorough searching first

### Quick Reference Workflow

```
1. Understand what you need mathematically
2. Identify keywords and type signature
3. Search using multiple strategies:
   - File organization (ls, find)
   - Keyword search (grep)
   - Naming conventions (grep with patterns)
4. Use Read tool to examine candidate files
5. Verify with #check
6. Import and use
7. If not found, search alternative phrasings
8. If still not found, prove it yourself (and consider contributing!)
```

This search workflow saves hours compared to reproving existing lemmas!

### Finding Existing Lemmas

#### Command-Line Search

**Basic file search:**
```bash
# Find files containing specific patterns
find .lake/packages/mathlib -name "*.lean" -exec grep -l "pattern1\|pattern2" {} \; | head -10

# Search with line numbers (for using Read tool)
grep -n "lemma.*keyword" path/to/file.lean | head -15

# Case-insensitive search
grep -in "keyword" path/to/file.lean

# Search for theorem OR lemma definitions
grep -n "theorem\|lemma" path/to/file.lean | grep "keyword"
```

**Example workflow:**
```bash
# Step 1: Identify keywords
# Looking for: "continuous functions preserve compact sets"
# Keywords: continuous, compact, preimage

# Step 2: Find relevant files
find .lake/packages/mathlib -name "*.lean" -exec grep -l "continuous.*compact\|compact.*continuous" {} \; | head -10
# Might return: Mathlib/Topology/Compactness.lean

# Step 3: Use Read tool to examine file
# Read: .lake/packages/mathlib/Mathlib/Topology/Compactness.lean

# Step 4: Search for specific lemmas with line numbers
grep -n "continuous.*isCompact\|isCompact.*continuous" .lake/packages/mathlib/Mathlib/Topology/Compactness.lean

# Step 5: Import and use
import Mathlib.Topology.Compactness
#check Continuous.isCompact_preimage
```

### Search Strategies

#### Strategy 1: Keyword-Based

**Use domain keywords:**
```bash
# Measure theory: measure, integrable, measurable, ae (almost everywhere)
find .lake/packages/mathlib -name "*.lean" -exec grep -l "integrable.*measurable" {} \;

# Topology: continuous, compact, open, closed
find .lake/packages/mathlib -name "*.lean" -exec grep -l "continuous.*compact" {} \;

# Algebra: ring, ideal, homomorphism
find .lake/packages/mathlib -name "*.lean" -exec grep -l "ring.*ideal" {} \;
```

**Include alternative spellings:**
```bash
# Sometimes capitalized, sometimes not
grep -i "KEYWORD" file.lean  # Case-insensitive

# Sometimes abbreviated
# "probability measure" might be "probMeasure" or "IsProbabilityMeasure"
grep "prob.*[Mm]easure\|[Mm]easure.*prob" file.lean
```

#### Strategy 2: Type-Based

**Search by type signature:**
```bash
# Looking for: (α → β) → (List α → List β)
# Search for "map" in List files
grep -n "map" .lake/packages/mathlib/Mathlib/Data/List/Basic.lean
```

**Use pattern matching:**
```bash
# Find all lemmas about indicators
grep -n "lemma.*indicator" .lake/packages/mathlib/Mathlib/MeasureTheory/Function/Indicator.lean
```

#### Strategy 3: Name Convention-Based (For Grep Search)

Mathlib follows consistent naming conventions - useful for grep, not loogle:

**Implications:** `conclusion_of_hypothesis`
```lean
continuous_of_isOpen_preimage  -- Continuous if all preimages of open sets are open
injective_of_leftInverse       -- Injective if has left inverse
```

**Equivalences:** `property_iff_characterization`
```lean
injective_iff_leftInverse      -- Injective ↔ has left inverse
compact_iff_finite_subcover    -- Compact ↔ finite subcover property
```

**Properties:** `structure_property_property`
```lean
Continuous.isCompact_preimage  -- Continuous functions preserve compactness
Measurable.comp                -- Composition of measurable functions
```

**Combining:** `operation_structure_structure`
```lean
add_comm                       -- Addition is commutative
mul_assoc                      -- Multiplication is associative
integral_add                   -- Integral is additive
```

**Search using these patterns (grep, not loogle):**
```bash
# Looking for: "conditional expectation of sum equals sum of conditional expectations"
# Convention: "condExp_add" or "add_condExp"
grep -n "condExp.*add\|add.*condExp" .lake/packages/mathlib/Mathlib/MeasureTheory/**/*.lean

# Looking for: "measure of union"
# Convention: "measure_union"
grep -n "measure_union" .lake/packages/mathlib/Mathlib/MeasureTheory/**/*.lean
```

#### Strategy 4: File Organization-Based

Mathlib is organized hierarchically:

```
Mathlib/
├── Algebra/
│   ├── Ring/          -- Ring theory
│   ├── Group/         -- Group theory
│   └── Field/         -- Field theory
├── Topology/
│   ├── Basic.lean     -- Core definitions
│   ├── Compactness.lean
│   └── MetricSpace/   -- Metric spaces
├── Analysis/
│   ├── Calculus/
│   └── SpecialFunctions/
├── MeasureTheory/
│   ├── Measure/       -- Measures
│   ├── Integral/      -- Integration
│   └── Function/
│       ├── ConditionalExpectation.lean
│       └── Indicator.lean
├── Probability/
│   ├── Independence.lean
│   ├── ProbabilityMassFunction/
│   └── ConditionalProbability.lean
└── Data/
    ├── List/          -- Lists
    ├── Finset/        -- Finite sets
    └── Real/          -- Real numbers
```

**Navigate by topic:**
```bash
# For measure theory lemmas:
ls .lake/packages/mathlib/Mathlib/MeasureTheory/

# For conditional expectation specifically:
ls .lake/packages/mathlib/Mathlib/MeasureTheory/Function/

# Read the file:
Read .lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation.lean
```

#### Missing Tactic Imports

When you see "unknown identifier 'ring'":

```lean
import Mathlib.Tactic.Ring          -- ring, ring_nf
import Mathlib.Tactic.Linarith      -- linarith, nlinarith
import Mathlib.Tactic.FieldSimp     -- field_simp
import Mathlib.Tactic.Continuity    -- continuity
import Mathlib.Tactic.Measurability -- measurability
import Mathlib.Tactic.Positivity    -- positivity
import Mathlib.Tactic.FunProp       -- fun_prop (Lean 4.13+)
```

### When Mathlib Doesn't Have It

#### Before giving up:

1. **Try alternative phrasings**
   - "continuous preimage compact" → "compact preimage continuous"
   - "integral sum" → "sum integral"

2. **Check if it's a special case**
   - Maybe mathlib has more general version
   - Check class hierarchy: `Continuous` vs `ContinuousOn`

3. **Look for building blocks**
   - Mathlib might have pieces you can combine
   - Example: No direct `condExp_indicator` but has `condExp_const` + `condExp_mul`
