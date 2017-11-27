#!/bin/bash
for f in LowParse.Spec.*.fst LowParse.Impl.*.fst{,i}
do
    sed -i 's!GTot !GTot  !g' "$f"
    sed -i 's!GTot \+Type0!GTot Type0!g' "$f"
    sed -i 's!GTot  \+!Tot !g' "$f"
    sed -i 's!Ghost !Ghost  !g' "$f"
    sed -i 's!Ghost \+Type0!Ghost Type0!g' "$f"
    sed -i 's!Ghost  \+!Pure !g' "$f"
done
