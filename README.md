# Verification supplement

This supplement contains the Windows executables, C++17 source, and the data
needed to check the computer-assisted statements in the paper. Run commands
from this directory in Windows PowerShell or Command Prompt.

## Run the supplied executables

### 1. State graphs, periods, and rank/residue certificates

```text
bin\verify_l321_direction1.exe --all-starts --check data
```

The program regenerates every state and edge of the four finite state graphs,
checks the graph sizes, cyclic strongly connected components and periods, and
checks every row and every edge against the two complete rank/residue
certificates in `data`. A successful run ends with:

```text
PASS certificate t=4: every closed-walk length is divisible by 16
PASS certificate t=5: every closed-walk length is divisible by 2
```

These results correspond to Lemma 3.4(i)--(ii), the rank/residue statement in
Lemma 3.4, and the computer-assisted inputs used in the proofs of Theorems 1.1
and 1.2.

To regenerate the supplied data in a new directory, run:

```text
bin\verify_l321_direction1.exe --all-starts --export generated
```

This creates six files:

| Generated file | Meaning | Paper location |
|---|---|---|
| `t4_s15_certificate.tsv` | Rank and residue of every state for modulus 16 | Lemma 3.4(i) and Theorem 1.1 |
| `t5_s13_certificate.tsv` | Rank and residue of every state for modulus 2 | Lemma 3.4(i) and Theorem 1.2 |
| `t4_s15_core_states.csv` | Every state in the cyclic core for the `t=4`, span-15 graph | Lemma 3.4(ii) and Section 5 |
| `t4_s15_core_edges.txt` | Every edge in that cyclic core | Lemma 3.4(ii) and Section 5 |
| `t5_s13_core_states.csv` | Every state in the cyclic core for the `t=5`, span-13 graph | Lemma 3.4(i), (iii) |
| `t5_s13_core_edges.txt` | Every edge in that cyclic core | Lemma 3.4(i), (iii) and Theorem 1.2 |

The six files already present in `data` are the files used for the paper.

### 2. Finite-window parity statement

```text
bin\verify_l321_parity_local.exe
```

The program writes no files. It prints the complete graph counts, the ten
synchronous pruning snapshots, the surviving-edge parity checks, and the
length-32 counterexample. These outputs correspond to Lemma 3.4(iii)--(iv),
Theorem 4.1, and the proof of Theorem 1.2.

### 3. Complete return-word structure for `t=4`

```text
bin\verify_l321_templates.exe
```

The program writes no files. It independently reconstructs the recurrent
core, prints the complete first-return words, and checks their edge coverage,
least periods, label multiplicities, counting recurrences, and splice tests.
These outputs correspond to Lemma 3.4(ii) and the classification and counting
results in Section 5.

Each executable prints `PASS` only after all of its checks succeed. A failed
check terminates with a nonzero exit code and a diagnostic message.

## Source

The three files in `src` are the complete source of the supplied executables.
Each source file begins with its C++17 compilation command, run command, and a
short description of its functions and mathematical task. Only the C++17
standard library is required.
