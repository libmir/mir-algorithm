#!/bin/bash

set -euo pipefail

# extract examples
# compile the examples
for file in $(find out -name "*.d") ; do
    echo "Testing: $file"
    dmd -de -lowmem -debug -unittest -mcpu=native -Isubprojects/mir-core/source -Isource -main -preview=dip1008 -run "$file"
done
