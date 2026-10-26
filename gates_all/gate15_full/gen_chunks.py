import sys, os
size = int(sys.argv[1]); qs = [int(x) for x in open("q27_certified.txt")]
os.makedirs("Gate15/Lots", exist_ok=True)
n = (len(qs) + size - 1) // size
for i in range(n):
    part = qs[i*size:(i+1)*size]
    with open("Gate15/Lots/Chunk%04d.lean" % i, "w") as f:
        f.write("import Gate15.Core\nnamespace Gate15\nset_option maxRecDepth 100000\n\n")
        f.write("def lots%04d : List Nat := [\n" % i + ",\n".join(map(str, part)) + "]\n\n")
        f.write("theorem lots%04d_checked : allOneBit lots%04d = true := by decide +kernel\n\n" % (i, i))
        f.write("theorem lots%04d_drop : ∀ q ∈ lots%04d, ∀ t,\n    iter 163 (seg33 (q + 2 ^ 27 * t)) < seg33 (q + 2 ^ 27 * t) :=\n  allOneBit_sound lots%04d lots%04d_checked\n\n" % (i, i, i, i))
        f.write("theorem lots%04d_count : lots%04d.length = %d := by decide +kernel\n\nend Gate15\n" % (i, i, len(part)))
with open("Gate15/All.lean", "w") as f:
    f.write("".join("import Gate15.Lots.Chunk%04d\n" % i for i in range(n)))
print(n, "chunks of up to", size)
