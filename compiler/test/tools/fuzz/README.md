# Differential fuzzing of dmd

Random programs whose behaviour is fully defined, compiled several ways and
compared. Any difference is a compiler bug: no output is compared with
anything that is allowed to vary.

| file | what it does |
|------|--------------|
| `progfuzz.py SEED` | prints a random D program: integer and floating point arithmetic, casts, shifts, division by constants and variables, control flow (if, loops, switch, break/continue, early returns), static and dynamic arrays and slices, structs passed and returned by value, closures and nested functions, templates, exceptions with `finally`, calls between the generated functions |
| `boundsfuzz.py SEED` | prints a random D program of `@safe` functions indexing arrays in loops and under guards, sometimes out of bounds: bounds from the lengths or off by one, indices offset by constants, counting up and down, `size_t` wraparound, signed indices, nested loops, arrays, indices and globals changed in the loop directly, through `ref` and by called functions; `main` catches each `RangeError` and prints its line |
| `abifuzz.py SEED DIR` | writes a calling convention test: functions with random parameter lists (integers, `bool`, `float`, `double`, structs of them, nested structs, static arrays, HFAs, many arguments so some go on the stack, C variadics) as `extern(D)`, `extern(C)` and in C, with callers in D and in C, and the output they must print |
| `fuzz.py prog SEEDS` | compiles each program with ldc2 (the reference) and with dmd in each configuration of `PROG_CONFIGS` (no flags, `-inline`, `-O` with the new and the old AArch64 code generator, `-O -inline`, `-O -inline -release`, `-boundscheck=off`), runs them and compares the output |
| `fuzz.py bounds SEEDS` | the same for the programs of `boundsfuzz.py`, without the configurations that turn the bounds checks off |
| `fuzz.py abi SEEDS` | compiles each ABI test with dmd without `-O`, with `-O` by the old code generator (`DMD_NEWCG=0`) and by the new one, with `-O -inline -release`, and with the C compiler, links every caller with every callee and compares with the expected output |
| `splitfuzz.py SEEDS` | writes a program of several modules, each a `progfuzz.py` program, sharing the instances of a module of templates, and checks it with `../splitcheck.py`: compiled with `-j=1` and with `-j=2,3,8` to an object file and to a library, with and without `-O -inline -release`, compared symbol by symbol and byte for byte across repeated compilations, and run from the `-j=1` and `-j=3` object files |
| `nightly.sh` | runs the program and ABI fuzzers over a seed range that changes every day, minimizing failing programs, and `splitfuzz.py` over a thirtieth as many seeds |

## Use

```
# against the dmd built in this repository (generated/<os>/release/64/dmd)
python3 compiler/test/tools/fuzz/fuzz.py prog 1-200 -j2
python3 compiler/test/tools/fuzz/fuzz.py abi 1-100 -j2

# another compiler, a subset of the configurations, reduction of failures
python3 compiler/test/tools/fuzz/fuzz.py prog 500-600 --dmd /path/to/dmd \
    --configs O,O-oldcg --minimize -v

compiler/test/tools/fuzz/nightly.sh [COUNT]
```

`--dmd`, `--ldc` and `--cc` (or `FUZZ_DMD`, `FUZZ_LDC`, `FUZZ_CC`) pick the
compilers, `--work` the directory for the temporary files and the failures
(default `$TMPDIR/dmd-fuzz`), `--size` the size of the programs.

Each failure is kept in `WORK/fail/`: `prog-SEED-CONFIG.d` with a `.txt`
giving the commands and the first differing line, `prog-SEED-CONFIG.min.d`
when minimized, and `abi-SEED/` with the sources and expected output of an ABI
test. The output names the first differing line, that is the function, of a
program, and the functions an ABI test got wrong for each caller and callee
combination (`new->old` is a caller built by the new code generator calling a
callee built by the old one).

## What the programs avoid

The generator keeps the programs free of undefined and implementation-defined
behaviour, so that the reference and dmd must agree:

* division and remainder only by constants other than 0 and -1, or by
  `(x & 15) | 1`;
* shift counts are constants below the width of the promoted left operand, or
  masked to it;
* array indices are masked to the length of the array;
* floating point values are kept multiples of 1/64 (1/8 for `float`) below
  2^12 (2^6) in magnitude by `fq`/`fqf`, and expressions are sums of at most
  three terms each a product of at most two of them, so every result is exact
  and fused multiply-add or extra precision cannot change it; they are
  converted to integers only within range;
* the generated functions only read global state, so the order in which the
  operands of an expression are evaluated cannot matter; a nested function
  that changes the variable it captures is called only from a statement of
  its own;
* functions called from expressions do not call other functions, which
  bounds the running time.

A reduced program from `--minimize` keeps the failure but can lose these
properties (a removed line can, for example, leave a variable unchanged that
bounded a loop), so check the reduced program before turning it into a test.
