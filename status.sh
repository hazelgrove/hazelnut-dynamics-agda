#!/bin/bash
echo
echo "\`\`\`"
echo "Status as of " `date`
echo "todos:       " `grep -i todo * | wc -l`
echo "postulates:  " `grep -i postulate *.agda | wc -l`
echo "red brackets:" `grep -i 'red brackets' *.agda | wc -l`
echo "\`\`\`"
