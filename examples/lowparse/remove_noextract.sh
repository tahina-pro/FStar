for f in *.fst{,i}
do
    sed -i '/^noextract$/d' "$f"
done
