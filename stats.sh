#!/usr/bin/env bash

total_files=$(find src -name '*.hs' -type f | wc -l)
total_lines=$(find src -name '*.hs' -type f -exec cat {} \; | wc -l)
total_chars=$(find src -name '*.hs' -type f -exec cat {} \; | wc -c)

echo "#files created = $total_files"
echo "#lines written = $total_lines"
echo "#chars written = $total_chars"
