#! /bin/bash
path=$( cd "$(dirname "${BASH_SOURCE[0]}")" ; pwd -P )
cd "$path"
grep -v "^c" $1 | ./a.out
