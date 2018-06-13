#!/bin/bash

set -euo pipefail

if [ ! -e test_extractor.d ] ; then
    wget https://raw.githubusercontent.com/dlang/tools/6b7ef76d679563e6fccef2a6b437008d96459e95/tests_extractor.d
fi

# extract examples
dub ./tests_extractor.d -i source -o out

# compile the examples
for file in $(find out -name "*.d") ; do
    echo "Testing: $file"
    $DMD -de -unittest -Isource -c -o- "$file"
done
