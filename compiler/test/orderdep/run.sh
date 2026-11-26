#!/bin/sh
# usage: run.sh [path/to/dmd]
cd "$(dirname "$0")"
DMD=${1:-../../../generated/linux/release/64/dmd}
DMD_ORDERCHECK=1 "$DMD" -conf= -I../../../druntime/import -o- cases.d 2>&1 | diff -u expected.txt - && echo OK
