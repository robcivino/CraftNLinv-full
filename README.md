# CRAFT nonlinear invariant attack, reproduction package

Code and data for the paper on nonlinear invariant attacks on full (32 round)
CRAFT. Two self contained programs, no dependencies, and the three library files.

## Files

- `craft_invattack.cpp`, C++17. The cipher with the designers' test vector, the
  free triple table, the affine system of a sequence, the weak tweak construction,
  the pattern test and the library key recovery procedure.
- `classify.c`, C. The classification that enumerates all cell separable invariant
  sequences of period dividing four and produces the library files.
- `p1.txt`, `p2.txt`, `p4_120.txt`, the library files (see below).
- `README.md`, this file.

## Build

The code uses only standard C and C++17 with the common `__builtin_*` intrinsics,
so any recent gcc or clang on any platform compiles it.

```
cc  -O2 -o classify        classify.c
c++ -std=c++17 -O2 -o craft_invattack craft_invattack.cpp
```

## The library files

A sequence is one line, `logkeys logpairs period` followed by the four mask groups,
each eight hex nibbles. `logkeys` is the base two logarithm of the weak key class
size, `logpairs` the same for the weak (key,tweak) pairs, `period` is 1, 2 or 4.

`classify` takes `PERIOD THRESHOLD OUTFILE`. A threshold of zero is an exhaustive
census. A positive threshold prunes any branch that cannot reach a class of size
two to the threshold, so the output is a complete census of every class at least
that large.

```
./classify 1 0   p1.txt        # period 1, exhaustive      -> 568 sequences
./classify 2 0   p2.txt        # period 2, exhaustive      -> 340716 sequences
./classify 4 120 p4_120.txt    # period 4, threshold 120   -> 38271 sequences
```

`p1.txt` and `p2.txt` are unconditional censuses. `p4_120.txt` is the threshold 120
census, the large class sequences, and it is the file the attack uses. Period one
and two run in seconds. The period four run at threshold 120 is the heavy one and
is best left to a fast machine.

## Running the attack

```
./craft_invattack selftest                         # cipher test vector and tables
./craft_invattack conditions 55555555 55555555 55555555 55555555   # one sequence
./craft_invattack phase1   [--keys N] [--seed s]   # verify the theorems on N keys
```

The key recovery reads the low key half out of the library and never uses the high
key half. The simulation does read the full true key, but only to print it and to
report whether the recovered low-key relations are correct, never inside the
recovery itself. With a library file given, the library is exactly that file, nothing
is added.

```
# the measurement reported in the paper, 5000 random keys with p4_120 alone
./craft_invattack attack --lib p4_120.txt --keys 5000 --budget 16 --seed 1

# the full library 
./craft_invattack attack --lib p4_120.txt --lib p2.txt --lib p1.txt --keys 1000 --budget 16 --seed 1
```

Each run prints, per key, the number of low key bits recovered from the invariants,
the number of chosen tweak queries, whether the recovered relations are consistent
with the true key, and the size of the exhaustive search that then finishes the key,
the unrecovered low bits together with the 64 blind high bits. At the end it prints
the average over the sample. Without `--seed` a fresh random seed is used and
printed, so any run can be repeated.

## Example run

`example_run.txt` is the full console output of the attack on a single key, produced
with

```
./craft_invattack attack --lib p4_120.txt --keys 1 --budget 16 --seed 1
```
