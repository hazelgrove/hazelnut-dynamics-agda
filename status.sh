#!/bin/bash
echo "todos:       " `grep -i todo *.agda | wc -l`
echo "postulates:  " `grep -i postulate *.agda | wc -l`
echo "bug @cyrus-: " `grep -i cyrus *.agda | wc -l`
