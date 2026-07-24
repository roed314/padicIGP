# The 2-adic Absolute Galois Group

See problem.tex for a detailed problem statement and the specification of the format for the relation file.  That file should be saved as `rel.txt` (which will then be copied to `DATA/2/rel.txt`).  See `DATA/3/rel.txt` for an example presentation file (a solution to the warm-up).

## Verification

To verify a presentation, run the `verify` script.  This script will save intermediate results, so it can be interrupted and rerun.  Here are some of the more common flags.

To run it in parallel, use the `-j` flag:

```
./verify -j 8
```

By default, the verification script runs on all the test groups.  If you want it to terminate early upon finding a group where the count predicted by the relation file does not match the correct value, use the `-e` flag:

```
./verify -e
```

For the full list of command line options, do `verify --help`.
