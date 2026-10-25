# Tools

These files implement tools and utilities used by the test suite.

| File                                       | Purpose                                                                                         |
|--------------------------------------------|-------------------------------------------------------------------------------------------------|
| [`d_do_test.d`](d_do_test.d)               | Test runner for all non-`unit` tests                                                            |
| [`determinism.sh`](determinism.sh)         | Compile programs repeatedly, split and unsplit, and compare the outputs byte for byte           |
| [`splitcheck.py`](splitcheck.py)           | Compare split compilations (`-j=N`) with unsplit ones symbol by symbol (see below)              |
| [`dshell_prebuilt.d`](dshell_prebuilt.d)   | Common utilities for `dshell` tests                                                             |
| [`paths.d`](paths.d)                       | Definitions for [common environment variables](../README.md#environment-variables) (e.g. `DMD`) |
| [`sanitize_json.d`](sanitize_json.d)       | Remove platform-specific information from dmd's JSON output (`-X`)                              |
| [`unit_test_runner.d`](unit_test_runner.d) | Test runner for `unit` tests                                                                    |

---

## splitcheck.py

A compilation split across worker processes (`-j=N`) must generate the same code
and data as an unsplit one (`-j=1`). `splitcheck.py` compiles a program both ways
and compares the outputs function by function and symbol by symbol, and compiles
it repeatedly with each `-j=N` to check that the output is the same byte for byte.

```
compiler/test/tools/splitcheck.py [-j 2,3,8] [-r 3] [--cwd DIR] [--require-split] -- \
    generated/osx/release/64/dmd -O -inline -release -c -of=app.o app/*.d
```

The command compiles to one object file (`-c -of=`), to an object file per module
(`-c` without `-of`) or to a library (`-lib`); its `-j`, `-of` and `-od` are
replaced, and a command that would link is compiled with `-c`. It reads Mach-O
object files and archives itself (arm64 macOS).

Every defined external symbol must be defined by both outputs, in the same section
and with the same binding (global, weak, hidden), and its contents must be the
same once what only depends on where the parts were placed is normalized:

- a relocated field (a branch or `ADRP` target, a page offset, a pointer) is
  compared by the relocation's type, the symbol it refers to and the addend;
- a branch without a relocation by its offset in the function when it stays in it,
  otherwise by the symbol and offset it reaches;
- a reference to a local symbol (a string literal `_TMP123`, a frame description
  entry) by the contents of that symbol, as their names are numbered in the order
  a compiler process creates them;
- the counter in the names of the modules written for template instances and
  functions in object files of their own with `-lib` (`module.123`), which the
  workers number apart, in symbol names and in the names their ModuleInfo holds;
- the zeros after a data symbol, which align the next one: Mach-O records no
  symbol sizes;
- the CIE pointer of a frame description entry, the distance back to its CIE, and
  the CIEs themselves, which each part has and `ld -r` may merge;
- in a library, the copies of a weak definition that several members carry (a
  TypeInfo, a template instance's data) must be the same, and are compared once.

Local symbols are compared as a set of contents. With `DMD_SPLIT_LOG` it tells
whether each `-j=N` compilation was split, and why a worker gave the split up;
with `--require-split`, one that was not is an error. Any difference is a compiler
bug. `fuzz/splitfuzz.py` runs it on random multi-module programs.

---

The following files are deprecated and will be removed in the future.

| File                                       | Purpose                                                                                         |
|--------------------------------------------|-------------------------------------------------------------------------------------------------|
| `sh_do_test.sh`                            | Old test runner, superseded by `d_do_test.d`                                                    |
| `postscript.sh`                            | Setup before running bash scripts defined as `POSTSCRIPT`                                       |
| `common_funcs.sh`                          | Common functions for shell scripts                                                              |

---

Refer to [test/README.md](../README.md) for more general information on the test suite.
