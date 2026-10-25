#!/bin/sh
# Runs the program and ABI fuzzers over a range of seeds that changes every
# day, minimizing failing programs, and the split compilation check on random
# multi-module programs, and prints a summary.
#
# Usage: nightly.sh [COUNT] [extra fuzz.py options]
#   COUNT  seeds per fuzzer (default 300)
# Environment: FUZZ_DMD, FUZZ_LDC, FUZZ_CC, FUZZ_JOBS (default 2),
#   FUZZ_WORK (default $TMPDIR/dmd-fuzz-nightly)
set -u
here=$(cd "$(dirname "$0")" && pwd)
count=${1:-300}
[ $# -gt 0 ] && shift
jobs=${FUZZ_JOBS:-2}
work=${FUZZ_WORK:-${TMPDIR:-/tmp}/dmd-fuzz-nightly}
# days since the epoch pick a fresh block of seeds each day
day=$(( $(date +%s) / 86400 ))
from=$(( (day % 10000) * count + 1 ))
to=$(( from + count - 1 ))
mkdir -p "$work"
log="$work/nightly-$(date +%Y%m%d).log"
status=0
echo "seeds $from-$to, work $work" | tee "$log"
python3 "$here/fuzz.py" prog "$from-$to" -j "$jobs" --work "$work" --minimize "$@" >>"$log" 2>&1 || status=1
python3 "$here/fuzz.py" abi "$from-$to" -j "$jobs" --work "$work" "$@" >>"$log" 2>&1 || status=1
# split compilations against unsplit ones, on a thirtieth as many seeds, as each
# program is compiled some forty times
scount=$(( count / 30 > 0 ? count / 30 : 1 ))
sfrom=$(( (day % 10000) * scount + 1 ))
sto=$(( sfrom + scount - 1 ))
python3 "$here/splitfuzz.py" "$sfrom-$sto" -j "$jobs" --work "$work" >>"$log" 2>&1 || status=1
cat "$log"
echo "log: $log, failures in $work/fail"
exit $status
