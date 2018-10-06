#!/bin/bash

grep --color=auto -A 1 'postulate' *.agda

echo "----------------------------------------------------------------"

grep --color=auto "open import structural" *.agda
