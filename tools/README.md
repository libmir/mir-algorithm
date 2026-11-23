# Documentation preview

The `Documentation` GitHub Actions workflow builds HTML on pull requests,
pushes to `master`, and manual runs. Download the `documentation-html` artifact
from a successful run and open `index.html`. This workflow does not publish a
website or require CircleCI/AWS credentials.

To reproduce the build on Linux, install LDC and ldmd2 **1.36.0**, Git, g++,
Ninja, and Python 3.9 or newer with pip, then run from the repository root:

```sh
python3 tools/build_docs.py build/docs
python3 -m http.server --directory build/docs/site 8000
```

Use a fresh output directory for each build. The script retains its cloned
inputs, isolated Python dependencies, Meson build, logs, and a version manifest
in that directory. It copies tracked build inputs from the working tree so
local source edits are included. The original checkout is not modified.

Run `python3 tools/test_build_docs.py` to check how the builder copies tracked
edits, additions, and deletions into its temporary source snapshot.

Meson 0.61.1, semver 2.13.0, and exact commits of `libmir/circle-dlang` and
`libmir/mir-core` are pinned in the script. The existing Ddoc templates and
styles are reused. HTML is compiled with warnings treated as errors.

This is an **HTML build check**, not an example-test check. It deliberately
selects the HTML targets from the old Meson template. The template's separately
extracted examples currently fail to compile in nine modules: bignum internal
kernel, bignum low-level view, date, linear and spline interpolation, normal
distribution functions, ndslice fuse, parse, and serde. Causes include missing
imports, private helper references, and extraction of disabled tests. The
existing compiler CI remains responsible for library tests.

Some legacy cross-references, search-domain settings, and template links still
need repair before deployment. A successful artifact build does not certify
those links or the external online example runner. Hosting migration is a
separate step.
