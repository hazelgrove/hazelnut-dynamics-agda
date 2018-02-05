#!/bin/bash

## display the difference between the sorted listing of all agda files in
## the directory and the names of modules imported (commented out or not)
## in all.agda

colordiff -u <(ls *.agda | xargs basename -s '.agda' | sort | grep -v 'all') <(cat all.agda | gsed 's/\s*--\s*//' | gsed 's/\s*open\s*import\s*//' | gsed '/^$/d' | sort)
