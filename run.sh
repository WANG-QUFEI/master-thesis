#!/bin/sh
if test -f "$1"; then
    stack exec -- siminitt $1
elif test -z $1; then
    stack exec -- siminitt test/loop1.smtt
else
    echo file does not exist
fi
