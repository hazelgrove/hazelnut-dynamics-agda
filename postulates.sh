#!/bin/bash

grep --color=auto -A 1 'postulate' *.agda

echo "---------------------------------------------------------------------------------------"
echo "used in:"
echo "---------------------------------------------------------------------------------------"

grep --color=auto "open import structural-assumptions" *.agda | cut -d ':' -f 1,1 | sort | uniq
