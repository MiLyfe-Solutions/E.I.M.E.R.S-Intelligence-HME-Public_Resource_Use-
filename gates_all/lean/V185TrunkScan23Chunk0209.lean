import V185TrunkScan23Chunk0208

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1235847 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 2, 5]
def baseStart_1235847 : Nat := 118140960795 + 1235847 * 2 ^ 59
def prefixEnd_1235847 : Nat := 4983230072969 + 3 ^ 40 * 1235847 * 2
def baseEnd_1235847 : Nat := 211527842139043825542983

theorem tailTrace_1235847 : CollatzResearch.WordTrace tailWord_1235847 prefixEnd_1235847 211527842139043825542983 := by
  unfold tailWord_1235847
  simp only [CollatzResearch.WordTrace]
  refine ⟨45075043153744859708897795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30050028769163239805931863 45075043153744859708897795)
  ·
    refine ⟨67612564730617289563346693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45075043153744859708897795 67612564730617289563346693)
    ·
      refine ⟨12677355886990741793127505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67612564730617289563346693 12677355886990741793127505)
      ·
        refine ⟨9508016915243056344845629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12677355886990741793127505 9508016915243056344845629)
        ·
          refine ⟨3565506343216146129317111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9508016915243056344845629 3565506343216146129317111)
          ·
            refine ⟨5348259514824219193975667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565506343216146129317111 5348259514824219193975667)
            ·
              refine ⟨8022389272236328790963501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348259514824219193975667 8022389272236328790963501)
              ·
                refine ⟨3008395977088623296611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8022389272236328790963501 3008395977088623296611313)
                ·
                  refine ⟨2256296982816467472458485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3008395977088623296611313 2256296982816467472458485)
                  ·
                    refine ⟨211527842139043825542983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2256296982816467472458485 211527842139043825542983)
                    ·
                      rfl

theorem cell23_1235847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_1235847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235847 prefixEnd_1235847 := by exact prefixLift 1235847
  have htrace : WordTrace (prefixWord ++ tailWord_1235847) baseStart_1235847 baseEnd_1235847 := by
    simpa [prefixWord, tailWord_1235847, baseEnd_1235847] using wordTrace_append hprefix tailTrace_1235847
  have hstable : (prefixWord ++ tailWord_1235847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235847).length < 2 ^ (prefixWord ++ tailWord_1235847).sum := by decide
  have hdescent : baseEnd_1235847 < baseStart_1235847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235862 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1235862 : Nat := 118140960795 + 1235862 * 2 ^ 59
def prefixEnd_1235862 : Nat := 4983230072969 + 3 ^ 40 * 1235862 * 2
def baseEnd_1235862 : Nat := 634591228626948917941381

theorem tailTrace_1235862 : CollatzResearch.WordTrace tailWord_1235862 prefixEnd_1235862 634591228626948917941381 := by
  unfold tailWord_1235862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817224390543157329418365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30050393499127011513795893 2817224390543157329418365)
  ·
    refine ⟨1056459146453683998531887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2817224390543157329418365 1056459146453683998531887)
    ·
      refine ⟨1584688719680525997797831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056459146453683998531887 1584688719680525997797831)
      ·
        refine ⟨2377033079520788996696747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584688719680525997797831 2377033079520788996696747)
        ·
          refine ⟨3565549619281183495045121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377033079520788996696747 3565549619281183495045121)
          ·
            refine ⟨2674162214460887621283841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565549619281183495045121 2674162214460887621283841)
            ·
              refine ⟨2005621660845665715962881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674162214460887621283841 2005621660845665715962881)
              ·
                refine ⟨1504216245634249286972161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005621660845665715962881 1504216245634249286972161)
                ·
                  refine ⟨1128162184225686965229121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504216245634249286972161 1128162184225686965229121)
                  ·
                    refine ⟨846121638169265223921841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128162184225686965229121 846121638169265223921841)
                    ·
                      refine ⟨634591228626948917941381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846121638169265223921841 634591228626948917941381)
                      ·
                        rfl

theorem cell23_1235862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1235862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235862 prefixEnd_1235862 := by exact prefixLift 1235862
  have htrace : WordTrace (prefixWord ++ tailWord_1235862) baseStart_1235862 baseEnd_1235862 := by
    simpa [prefixWord, tailWord_1235862, baseEnd_1235862] using wordTrace_append hprefix tailTrace_1235862
  have hstable : (prefixWord ++ tailWord_1235862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235862).length < 2 ^ (prefixWord ++ tailWord_1235862).sum := by decide
  have hdescent : baseEnd_1235862 < baseStart_1235862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235868 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 5]
def baseStart_1235868 : Nat := 118140960795 + 1235868 * 2 ^ 59
def prefixEnd_1235868 : Nat := 4983230072969 + 3 ^ 40 * 1235868 * 2
def baseEnd_1235868 : Nat := 70510478834541766051817

theorem tailTrace_1235868 : CollatzResearch.WordTrace tailWord_1235868 prefixEnd_1235868 70510478834541766051817 := by
  unfold tailWord_1235868
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537904543334390147706129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30050539391112520196941505 22537904543334390147706129)
  ·
    refine ⟨16903428407500792610779597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22537904543334390147706129 16903428407500792610779597)
    ·
      refine ⟨6338785652812797229042349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16903428407500792610779597 6338785652812797229042349)
      ·
        refine ⟨2377044619804798960890881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6338785652812797229042349 2377044619804798960890881)
        ·
          refine ⟨1782783464853599220668161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2377044619804798960890881 1782783464853599220668161)
          ·
            refine ⟨1337087598640199415501121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782783464853599220668161 1337087598640199415501121)
            ·
              refine ⟨1002815698980149561625841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337087598640199415501121 1002815698980149561625841)
              ·
                refine ⟨752111774235112171219381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002815698980149561625841 752111774235112171219381)
                ·
                  refine ⟨70510478834541766051817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 752111774235112171219381 70510478834541766051817)
                  ·
                    rfl

theorem cell23_1235868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_1235868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235868 prefixEnd_1235868 := by exact prefixLift 1235868
  have htrace : WordTrace (prefixWord ++ tailWord_1235868) baseStart_1235868 baseEnd_1235868 := by
    simpa [prefixWord, tailWord_1235868, baseEnd_1235868] using wordTrace_append hprefix tailTrace_1235868
  have hstable : (prefixWord ++ tailWord_1235868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235868).length < 2 ^ (prefixWord ++ tailWord_1235868).sum := by decide
  have hdescent : baseEnd_1235868 < baseStart_1235868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235890 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_1235890 : Nat := 118140960795 + 1235890 * 2 ^ 59
def prefixEnd_1235890 : Nat := 4983230072969 + 3 ^ 40 * 1235890 * 2
def baseEnd_1235890 : Nat := 70511734009474978710139

theorem tailTrace_1235890 : CollatzResearch.WordTrace tailWord_1235890 prefixEnd_1235890 70511734009474978710139 := by
  unfold tailWord_1235890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11269152873147269513178281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30051074328392718701808749 11269152873147269513178281)
  ·
    refine ⟨8451864654860452134883711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11269152873147269513178281 8451864654860452134883711)
    ·
      refine ⟨12677796982290678202325567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451864654860452134883711 12677796982290678202325567)
      ·
        refine ⟨19016695473436017303488351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12677796982290678202325567 19016695473436017303488351)
        ·
          refine ⟨28525043210154025955232527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19016695473436017303488351 28525043210154025955232527)
          ·
            refine ⟨42787564815231038932848791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28525043210154025955232527 42787564815231038932848791)
            ·
              refine ⟨64181347222846558399273187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42787564815231038932848791 64181347222846558399273187)
              ·
                refine ⟨96272020834269837598909781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64181347222846558399273187 96272020834269837598909781)
                ·
                  refine ⟨70511734009474978710139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 96272020834269837598909781 70511734009474978710139)
                  ·
                    rfl

theorem cell23_1235890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_1235890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235890 prefixEnd_1235890 := by exact prefixLift 1235890
  have htrace : WordTrace (prefixWord ++ tailWord_1235890) baseStart_1235890 baseEnd_1235890 := by
    simpa [prefixWord, tailWord_1235890, baseEnd_1235890] using wordTrace_append hprefix tailTrace_1235890
  have hstable : (prefixWord ++ tailWord_1235890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235890).length < 2 ^ (prefixWord ++ tailWord_1235890).sum := by decide
  have hdescent : baseEnd_1235890 < baseStart_1235890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235901 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1235901 : Nat := 118140960795 + 1235901 * 2 ^ 59
def prefixEnd_1235901 : Nat := 4983230072969 + 3 ^ 40 * 1235901 * 2
def baseEnd_1235901 : Nat := 634611254372474265353701

theorem tailTrace_1235901 : CollatzResearch.WordTrace tailWord_1235901 prefixEnd_1235901 634611254372474265353701 := by
  unfold tailWord_1235901
  simp only [CollatzResearch.WordTrace]
  refine ⟨45077012695549226931363557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30051341797032817954242371 45077012695549226931363557)
  ·
    refine ⟨8451939880415480049630667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45077012695549226931363557 8451939880415480049630667)
    ·
      refine ⟨12677909820623220074446001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451939880415480049630667 12677909820623220074446001)
      ·
        refine ⟨9508432365467415055834501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12677909820623220074446001 9508432365467415055834501)
        ·
          refine ⟨1782831068525140322968969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9508432365467415055834501 1782831068525140322968969)
          ·
            refine ⟨1337123301393855242226727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782831068525140322968969 1337123301393855242226727)
            ·
              refine ⟨2005684952090782863340091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337123301393855242226727 2005684952090782863340091)
              ·
                refine ⟨3008527428136174295010137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005684952090782863340091 3008527428136174295010137)
                ·
                  refine ⟨2256395571102130721257603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3008527428136174295010137 2256395571102130721257603)
                  ·
                    refine ⟨3384593356653196081886405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2256395571102130721257603 3384593356653196081886405)
                    ·
                      refine ⟨634611254372474265353701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3384593356653196081886405 634611254372474265353701)
                      ·
                        rfl

theorem cell23_1235901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1235901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235901 prefixEnd_1235901 := by exact prefixLift 1235901
  have htrace : WordTrace (prefixWord ++ tailWord_1235901) baseStart_1235901 baseEnd_1235901 := by
    simpa [prefixWord, tailWord_1235901, baseEnd_1235901] using wordTrace_append hprefix tailTrace_1235901
  have hstable : (prefixWord ++ tailWord_1235901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235901).length < 2 ^ (prefixWord ++ tailWord_1235901).sum := by decide
  have hdescent : baseEnd_1235901 < baseStart_1235901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235904 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_1235904 : Nat := 118140960795 + 1235904 * 2 ^ 59
def prefixEnd_1235904 : Nat := 4983230072969 + 3 ^ 40 * 1235904 * 2
def baseEnd_1235904 : Nat := 634612794814437753616187

theorem tailTrace_1235904 : CollatzResearch.WordTrace tailWord_1235904 prefixEnd_1235904 634612794814437753616187 := by
  unfold tailWord_1235904
  simp only [CollatzResearch.WordTrace]
  refine ⟨22538561057269179221861383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30051414743025572295815177 22538561057269179221861383)
  ·
    refine ⟨33807841585903768832792075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22538561057269179221861383 33807841585903768832792075)
    ·
      refine ⟨50711762378855653249188113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33807841585903768832792075 50711762378855653249188113)
      ·
        refine ⟨38033821784141739936891085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50711762378855653249188113 38033821784141739936891085)
        ·
          refine ⟨14262683169053152476334157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38033821784141739936891085 14262683169053152476334157)
          ·
            refine ⟨5348506188394932178625309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14262683169053152476334157 5348506188394932178625309)
            ·
              refine ⟨2005689820648099566984491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5348506188394932178625309 2005689820648099566984491)
              ·
                refine ⟨3008534730972149350476737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005689820648099566984491 3008534730972149350476737)
                ·
                  refine ⟨2256401048229112012857553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3008534730972149350476737 2256401048229112012857553)
                  ·
                    refine ⟨1692300786171834009643165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256401048229112012857553 1692300786171834009643165)
                    ·
                      refine ⟨634612794814437753616187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692300786171834009643165 634612794814437753616187)
                      ·
                        rfl

theorem cell23_1235904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_1235904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235904 prefixEnd_1235904 := by exact prefixLift 1235904
  have htrace : WordTrace (prefixWord ++ tailWord_1235904) baseStart_1235904 baseEnd_1235904 := by
    simpa [prefixWord, tailWord_1235904, baseEnd_1235904] using wordTrace_append hprefix tailTrace_1235904
  have hstable : (prefixWord ++ tailWord_1235904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235904).length < 2 ^ (prefixWord ++ tailWord_1235904).sum := by decide
  have hdescent : baseEnd_1235904 < baseStart_1235904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235924 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1235924 : Nat := 118140960795 + 1235924 * 2 ^ 59
def prefixEnd_1235924 : Nat := 4983230072969 + 3 ^ 40 * 1235924 * 2
def baseEnd_1235924 : Nat := 70513673825280852818455

theorem tailTrace_1235924 : CollatzResearch.WordTrace tailWord_1235924 prefixEnd_1235924 70513673825280852818455 := by
  unfold tailWord_1235924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22538925787232950929725413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30051901049643934572967217 22538925787232950929725413)
  ·
    refine ⟨4226048585106178299323515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22538925787232950929725413 4226048585106178299323515)
    ·
      refine ⟨6339072877659267448985273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226048585106178299323515 6339072877659267448985273)
      ·
        refine ⟨4754304658244450586738955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6339072877659267448985273 4754304658244450586738955)
        ·
          refine ⟨7131456987366675880108433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754304658244450586738955 7131456987366675880108433)
          ·
            refine ⟨5348592740525006910081325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7131456987366675880108433 5348592740525006910081325)
            ·
              refine ⟨2005722277696877591280497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5348592740525006910081325 2005722277696877591280497)
              ·
                refine ⟨1504291708272658193460373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005722277696877591280497 1504291708272658193460373)
                ·
                  refine ⟨70513673825280852818455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1504291708272658193460373 70513673825280852818455)
                  ·
                    rfl

theorem cell23_1235924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1235924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235924 prefixEnd_1235924 := by exact prefixLift 1235924
  have htrace : WordTrace (prefixWord ++ tailWord_1235924) baseStart_1235924 baseEnd_1235924 := by
    simpa [prefixWord, tailWord_1235924, baseEnd_1235924] using wordTrace_append hprefix tailTrace_1235924
  have hstable : (prefixWord ++ tailWord_1235924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235924).length < 2 ^ (prefixWord ++ tailWord_1235924).sum := by decide
  have hdescent : baseEnd_1235924 < baseStart_1235924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235944 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1235944 : Nat := 118140960795 + 1235944 * 2 ^ 59
def prefixEnd_1235944 : Nat := 4983230072969 + 3 ^ 40 * 1235944 * 2
def baseEnd_1235944 : Nat := 634633334040617597116003

theorem tailTrace_1235944 : CollatzResearch.WordTrace tailWord_1235944 prefixEnd_1235944 634633334040617597116003 := by
  unfold tailWord_1235944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22539290517196722637589443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30052387356262296850119257 22539290517196722637589443)
  ·
    refine ⟨33808935775795083956384165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22539290517196722637589443 33808935775795083956384165)
    ·
      refine ⟨6339175457961578241822031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33808935775795083956384165 6339175457961578241822031)
      ·
        refine ⟨9508763186942367362733047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339175457961578241822031 9508763186942367362733047)
        ·
          refine ⟨14263144780413551044099571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508763186942367362733047 14263144780413551044099571)
          ·
            refine ⟨21394717170620326566149357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263144780413551044099571 21394717170620326566149357)
            ·
              refine ⟨8023018938982622462306009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21394717170620326566149357 8023018938982622462306009)
              ·
                refine ⟨6017264204236966846729507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8023018938982622462306009 6017264204236966846729507)
                ·
                  refine ⟨9025896306355450270094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017264204236966846729507 9025896306355450270094261)
                  ·
                    refine ⟨846177778720823462821337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9025896306355450270094261 846177778720823462821337)
                    ·
                      refine ⟨634633334040617597116003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846177778720823462821337 634633334040617597116003)
                      ·
                        rfl

theorem cell23_1235944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1235944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235944 prefixEnd_1235944 := by exact prefixLift 1235944
  have htrace : WordTrace (prefixWord ++ tailWord_1235944) baseStart_1235944 baseEnd_1235944 := by
    simpa [prefixWord, tailWord_1235944, baseEnd_1235944] using wordTrace_append hprefix tailTrace_1235944
  have hstable : (prefixWord ++ tailWord_1235944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235944).length < 2 ^ (prefixWord ++ tailWord_1235944).sum := by decide
  have hdescent : baseEnd_1235944 < baseStart_1235944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235994 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1235994 : Nat := 118140960795 + 1235994 * 2 ^ 59
def prefixEnd_1235994 : Nat := 4983230072969 + 3 ^ 40 * 1235994 * 2
def baseEnd_1235994 : Nat := 634659008073342401490773

theorem tailTrace_1235994 : CollatzResearch.WordTrace tailWord_1235994 prefixEnd_1235994 634659008073342401490773 := by
  unfold tailWord_1235994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11270101171053075953624759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30053603122808202542999357 11270101171053075953624759)
  ·
    refine ⟨16905151756579613930437139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11270101171053075953624759 16905151756579613930437139)
    ·
      refine ⟨25357727634869420895655709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905151756579613930437139 25357727634869420895655709)
      ·
        refine ⟨9509147863076032835870891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25357727634869420895655709 9509147863076032835870891)
        ·
          refine ⟨14263721794614049253806337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9509147863076032835870891 14263721794614049253806337)
          ·
            refine ⟨10697791345960536940354753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14263721794614049253806337 10697791345960536940354753)
            ·
              refine ⟨8023343509470402705266065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10697791345960536940354753 8023343509470402705266065)
              ·
                refine ⟨6017507632102802028949549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8023343509470402705266065 6017507632102802028949549)
                ·
                  refine ⟨2256565362038550760856081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6017507632102802028949549 2256565362038550760856081)
                  ·
                    refine ⟨1692424021528913070642061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256565362038550760856081 1692424021528913070642061)
                    ·
                      refine ⟨634659008073342401490773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692424021528913070642061 634659008073342401490773)
                      ·
                        rfl

theorem cell23_1235994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1235994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1235994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1235994 prefixEnd_1235994 := by exact prefixLift 1235994
  have htrace : WordTrace (prefixWord ++ tailWord_1235994) baseStart_1235994 baseEnd_1235994 := by
    simpa [prefixWord, tailWord_1235994, baseEnd_1235994] using wordTrace_append hprefix tailTrace_1235994
  have hstable : (prefixWord ++ tailWord_1235994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235994).length < 2 ^ (prefixWord ++ tailWord_1235994).sum := by decide
  have hdescent : baseEnd_1235994 < baseStart_1235994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236001 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1236001 : Nat := 118140960795 + 1236001 * 2 ^ 59
def prefixEnd_1236001 : Nat := 4983230072969 + 3 ^ 40 * 1236001 * 2
def baseEnd_1236001 : Nat := 211554200812641291367747

theorem tailTrace_1236001 : CollatzResearch.WordTrace tailWord_1236001 prefixEnd_1236001 211554200812641291367747 := by
  unfold tailWord_1236001
  simp only [CollatzResearch.WordTrace]
  refine ⟨45080659995186944010003857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30053773330124629340002571 45080659995186944010003857)
  ·
    refine ⟨33810494996390208007502893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45080659995186944010003857 33810494996390208007502893)
    ·
      refine ⟨12678935623646328002813585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33810494996390208007502893 12678935623646328002813585)
      ·
        refine ⟨9509201717734746002110189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12678935623646328002813585 9509201717734746002110189)
        ·
          refine ⟨3565950644150529750791321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9509201717734746002110189 3565950644150529750791321)
          ·
            refine ⟨2674462983112897313093491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565950644150529750791321 2674462983112897313093491)
            ·
              refine ⟨4011694474669345969640237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674462983112897313093491 4011694474669345969640237)
              ·
                refine ⟨1504385428001004738615089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4011694474669345969640237 1504385428001004738615089)
                ·
                  refine ⟨1128289071000753553961317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504385428001004738615089 1128289071000753553961317)
                  ·
                    refine ⟨211554200812641291367747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1128289071000753553961317 211554200812641291367747)
                    ·
                      rfl

theorem cell23_1236001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1236001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236001 prefixEnd_1236001 := by exact prefixLift 1236001
  have htrace : WordTrace (prefixWord ++ tailWord_1236001) baseStart_1236001 baseEnd_1236001 := by
    simpa [prefixWord, tailWord_1236001, baseEnd_1236001] using wordTrace_append hprefix tailTrace_1236001
  have hstable : (prefixWord ++ tailWord_1236001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236001).length < 2 ^ (prefixWord ++ tailWord_1236001).sum := by decide
  have hdescent : baseEnd_1236001 < baseStart_1236001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236004 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1236004 : Nat := 118140960795 + 1236004 * 2 ^ 59
def prefixEnd_1236004 : Nat := 4983230072969 + 3 ^ 40 * 1236004 * 2
def baseEnd_1236004 : Nat := 634664142879887362365727

theorem tailTrace_1236004 : CollatzResearch.WordTrace tailWord_1236004 prefixEnd_1236004 634664142879887362365727 := by
  unfold tailWord_1236004
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540384707088037761181533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30053846276117383681575377 22540384707088037761181533)
  ·
    refine ⟨8452644265158014160443075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22540384707088037761181533 8452644265158014160443075)
    ·
      refine ⟨12678966397737021240664613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452644265158014160443075 12678966397737021240664613)
      ·
        refine ⟨2377306199575691482624615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12678966397737021240664613 2377306199575691482624615)
        ·
          refine ⟨3565959299363537223936923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377306199575691482624615 3565959299363537223936923)
          ·
            refine ⟨5348938949045305835905385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565959299363537223936923 5348938949045305835905385)
            ·
              refine ⟨4011704211783979376929039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5348938949045305835905385 4011704211783979376929039)
              ·
                refine ⟨6017556317675969065393559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011704211783979376929039 6017556317675969065393559)
                ·
                  refine ⟨9026334476513953598090339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017556317675969065393559 9026334476513953598090339)
                  ·
                    refine ⟨13539501714770930397135509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9026334476513953598090339 13539501714770930397135509)
                    ·
                      refine ⟨634664142879887362365727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13539501714770930397135509 634664142879887362365727)
                      ·
                        rfl

theorem cell23_1236004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1236004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236004 prefixEnd_1236004 := by exact prefixLift 1236004
  have htrace : WordTrace (prefixWord ++ tailWord_1236004) baseStart_1236004 baseEnd_1236004 := by
    simpa [prefixWord, tailWord_1236004, baseEnd_1236004] using wordTrace_append hprefix tailTrace_1236004
  have hstable : (prefixWord ++ tailWord_1236004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236004).length < 2 ^ (prefixWord ++ tailWord_1236004).sum := by decide
  have hdescent : baseEnd_1236004 < baseStart_1236004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236024 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_1236024 : Nat := 118140960795 + 1236024 * 2 ^ 59
def prefixEnd_1236024 : Nat := 4983230072969 + 3 ^ 40 * 1236024 * 2
def baseEnd_1236024 : Nat := 634674412492977284115635

theorem tailTrace_1236024 : CollatzResearch.WordTrace tailWord_1236024 prefixEnd_1236024 634674412492977284115635 := by
  unfold tailWord_1236024
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540749437051809469045563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30054332582735745958727417 22540749437051809469045563)
  ·
    refine ⟨33811124155577714203568345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22540749437051809469045563 33811124155577714203568345)
    ·
      refine ⟨25358343116683285652676259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33811124155577714203568345 25358343116683285652676259)
      ·
        refine ⟨38037514675024928479014389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25358343116683285652676259 38037514675024928479014389)
        ·
          refine ⟨3566017000783587044907599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38037514675024928479014389 3566017000783587044907599)
          ·
            refine ⟨5349025501175380567361399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566017000783587044907599 5349025501175380567361399)
            ·
              refine ⟨8023538251763070851042099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349025501175380567361399 8023538251763070851042099)
              ·
                refine ⟨12035307377644606276563149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023538251763070851042099 12035307377644606276563149)
                ·
                  refine ⟨4513240266616727353711181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12035307377644606276563149 4513240266616727353711181)
                  ·
                    refine ⟨1692465099981272757641693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4513240266616727353711181 1692465099981272757641693)
                    ·
                      refine ⟨634674412492977284115635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692465099981272757641693 634674412492977284115635)
                      ·
                        rfl

theorem cell23_1236024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_1236024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236024 prefixEnd_1236024 := by exact prefixLift 1236024
  have htrace : WordTrace (prefixWord ++ tailWord_1236024) baseStart_1236024 baseEnd_1236024 := by
    simpa [prefixWord, tailWord_1236024, baseEnd_1236024] using wordTrace_append hprefix tailTrace_1236024
  have hstable : (prefixWord ++ tailWord_1236024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236024).length < 2 ^ (prefixWord ++ tailWord_1236024).sum := by decide
  have hdescent : baseEnd_1236024 < baseStart_1236024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236028 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_1236028 : Nat := 118140960795 + 1236028 * 2 ^ 59
def prefixEnd_1236028 : Nat := 4983230072969 + 3 ^ 40 * 1236028 * 2
def baseEnd_1236028 : Nat := 634676466415595268465617

theorem tailTrace_1236028 : CollatzResearch.WordTrace tailWord_1236028 prefixEnd_1236028 634676466415595268465617 := by
  unfold tailWord_1236028
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540822383044563810618369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30054429844059418414157825 22540822383044563810618369)
  ·
    refine ⟨16905616787283422857963777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22540822383044563810618369 16905616787283422857963777)
    ·
      refine ⟨12679212590462567143472833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16905616787283422857963777 12679212590462567143472833)
      ·
        refine ⟨9509409442846925357604625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12679212590462567143472833 9509409442846925357604625)
        ·
          refine ⟨7132057082135194018203469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9509409442846925357604625 7132057082135194018203469)
          ·
            refine ⟨2674521405800697756826301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7132057082135194018203469 2674521405800697756826301)
            ·
              refine ⟨1002945527175261658809863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2674521405800697756826301 1002945527175261658809863)
              ·
                refine ⟨1504418290762892488214795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002945527175261658809863 1504418290762892488214795)
                ·
                  refine ⟨2256627436144338732322193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504418290762892488214795 2256627436144338732322193)
                  ·
                    refine ⟨1692470577108254049241645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256627436144338732322193 1692470577108254049241645)
                    ·
                      refine ⟨634676466415595268465617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692470577108254049241645 634676466415595268465617)
                      ·
                        rfl

theorem cell23_1236028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_1236028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236028 prefixEnd_1236028 := by exact prefixLift 1236028
  have htrace : WordTrace (prefixWord ++ tailWord_1236028) baseStart_1236028 baseEnd_1236028 := by
    simpa [prefixWord, tailWord_1236028, baseEnd_1236028] using wordTrace_append hprefix tailTrace_1236028
  have hstable : (prefixWord ++ tailWord_1236028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236028).length < 2 ^ (prefixWord ++ tailWord_1236028).sum := by decide
  have hdescent : baseEnd_1236028 < baseStart_1236028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236037 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_1236037 : Nat := 118140960795 + 1236037 * 2 ^ 59
def prefixEnd_1236037 : Nat := 4983230072969 + 3 ^ 40 * 1236037 * 2
def baseEnd_1236037 : Nat := 634681087741485733253075

theorem tailTrace_1236037 : CollatzResearch.WordTrace tailWord_1236037 prefixEnd_1236037 634681087741485733253075 := by
  unfold tailWord_1236037
  simp only [CollatzResearch.WordTrace]
  refine ⟨45081973023056522158314365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30054648682037681438876243 45081973023056522158314365)
  ·
    refine ⟨16905739883646195809367887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45081973023056522158314365 16905739883646195809367887)
    ·
      refine ⟨25358609825469293714051831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905739883646195809367887 25358609825469293714051831)
      ·
        refine ⟨38037914738203940571077747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25358609825469293714051831 38037914738203940571077747)
        ·
          refine ⟨57056872107305910856616621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38037914738203940571077747 57056872107305910856616621)
          ·
            refine ⟨21396327040239716571231233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57056872107305910856616621 21396327040239716571231233)
            ·
              refine ⟨16047245280179787428423425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21396327040239716571231233 16047245280179787428423425)
              ·
                refine ⟨12035433960134840571317569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16047245280179787428423425 12035433960134840571317569)
                ·
                  refine ⟨9026575470101130428488177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12035433960134840571317569 9026575470101130428488177)
                  ·
                    refine ⟨6769931602575847821366133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9026575470101130428488177 6769931602575847821366133)
                    ·
                      refine ⟨634681087741485733253075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6769931602575847821366133 634681087741485733253075)
                      ·
                        rfl

theorem cell23_1236037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_1236037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236037 prefixEnd_1236037 := by exact prefixLift 1236037
  have htrace : WordTrace (prefixWord ++ tailWord_1236037) baseStart_1236037 baseEnd_1236037 := by
    simpa [prefixWord, tailWord_1236037, baseEnd_1236037] using wordTrace_append hprefix tailTrace_1236037
  have hstable : (prefixWord ++ tailWord_1236037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236037).length < 2 ^ (prefixWord ++ tailWord_1236037).sum := by decide
  have hdescent : baseEnd_1236037 < baseStart_1236037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236087 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 9]
def baseStart_1236087 : Nat := 118140960795 + 1236087 * 2 ^ 59
def prefixEnd_1236087 : Nat := 4983230072969 + 3 ^ 40 * 1236087 * 2
def baseEnd_1236087 : Nat := 70522973530467837514205

theorem tailTrace_1236087 : CollatzResearch.WordTrace tailWord_1236087 prefixEnd_1236087 70522973530467837514205 := by
  unfold tailWord_1236087
  simp only [CollatzResearch.WordTrace]
  refine ⟨45083796672875380697634515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30055864448583587131756343 45083796672875380697634515)
  ·
    refine ⟨67625695009313071046451773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45083796672875380697634515 67625695009313071046451773)
    ·
      refine ⟨25359635628492401642419415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67625695009313071046451773 25359635628492401642419415)
      ·
        refine ⟨38039453442738602463629123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25359635628492401642419415 38039453442738602463629123)
        ·
          refine ⟨57059180164107903695443685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38039453442738602463629123 57059180164107903695443685)
          ·
            refine ⟨10698596280770231942895691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57059180164107903695443685 10698596280770231942895691)
            ·
              refine ⟨16047894421155347914343537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10698596280770231942895691 16047894421155347914343537)
              ·
                refine ⟨12035920815866510935757653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16047894421155347914343537 12035920815866510935757653)
                ·
                  refine ⟨70522973530467837514205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12035920815866510935757653 70522973530467837514205)
                  ·
                    rfl

theorem cell23_1236087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 9].length) (baseStart_1236087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236087 prefixEnd_1236087 := by exact prefixLift 1236087
  have htrace : WordTrace (prefixWord ++ tailWord_1236087) baseStart_1236087 baseEnd_1236087 := by
    simpa [prefixWord, tailWord_1236087, baseEnd_1236087] using wordTrace_append hprefix tailTrace_1236087
  have hstable : (prefixWord ++ tailWord_1236087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236087).length < 2 ^ (prefixWord ++ tailWord_1236087).sum := by decide
  have hdescent : baseEnd_1236087 < baseStart_1236087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236161 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1236161 : Nat := 118140960795 + 1236161 * 2 ^ 59
def prefixEnd_1236161 : Nat := 4983230072969 + 3 ^ 40 * 1236161 * 2
def baseEnd_1236161 : Nat := 634744759342643248102505

theorem tailTrace_1236161 : CollatzResearch.WordTrace tailWord_1236161 prefixEnd_1236161 634744759342643248102505 := by
  unfold tailWord_1236161
  simp only [CollatzResearch.WordTrace]
  refine ⟨45086495674607291335828337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30057663783071527557218891 45086495674607291335828337)
  ·
    refine ⟨33814871755955468501871253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45086495674607291335828337 33814871755955468501871253)
    ·
      refine ⟨1585072113560412586025215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33814871755955468501871253 1585072113560412586025215)
      ·
        refine ⟨2377608170340618879037823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585072113560412586025215 2377608170340618879037823)
        ·
          refine ⟨3566412255510928318556735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377608170340618879037823 3566412255510928318556735)
          ·
            refine ⟨5349618383266392477835103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566412255510928318556735 5349618383266392477835103)
            ·
              refine ⟨8024427574899588716752655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349618383266392477835103 8024427574899588716752655)
              ·
                refine ⟨12036641362349383075128983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024427574899588716752655 12036641362349383075128983)
                ·
                  refine ⟨18054962043524074612693475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12036641362349383075128983 18054962043524074612693475)
                  ·
                    refine ⟨27082443065286111919040213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18054962043524074612693475 27082443065286111919040213)
                    ·
                      refine ⟨634744759342643248102505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27082443065286111919040213 634744759342643248102505)
                      ·
                        rfl

theorem cell23_1236161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1236161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236161 prefixEnd_1236161 := by exact prefixLift 1236161
  have htrace : WordTrace (prefixWord ++ tailWord_1236161) baseStart_1236161 baseEnd_1236161 := by
    simpa [prefixWord, tailWord_1236161, baseEnd_1236161] using wordTrace_append hprefix tailTrace_1236161
  have hstable : (prefixWord ++ tailWord_1236161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236161).length < 2 ^ (prefixWord ++ tailWord_1236161).sum := by decide
  have hdescent : baseEnd_1236161 < baseStart_1236161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236166 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1236166 : Nat := 118140960795 + 1236166 * 2 ^ 59
def prefixEnd_1236166 : Nat := 4983230072969 + 3 ^ 40 * 1236166 * 2
def baseEnd_1236166 : Nat := 634747326745915728539983

theorem tailTrace_1236166 : CollatzResearch.WordTrace tailWord_1236166 prefixEnd_1236166 634747326745915728539983 := by
  unfold tailWord_1236166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408958688737161787180011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30057785359726118126506901 1408958688737161787180011)
  ·
    refine ⟨2113438033105742680770017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408958688737161787180011 2113438033105742680770017)
    ·
      refine ⟨1585078524829307010577513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2113438033105742680770017 1585078524829307010577513)
      ·
        refine ⟨1188808893621980257933135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585078524829307010577513 1188808893621980257933135)
        ·
          refine ⟨1783213340432970386899703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188808893621980257933135 1783213340432970386899703)
          ·
            refine ⟨2674820010649455580349555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783213340432970386899703 2674820010649455580349555)
            ·
              refine ⟨4012230015974183370524333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674820010649455580349555 4012230015974183370524333)
              ·
                refine ⟨1504586255990318763946625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4012230015974183370524333 1504586255990318763946625)
                ·
                  refine ⟨1128439691992739072959969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504586255990318763946625 1128439691992739072959969)
                  ·
                    refine ⟨846329768994554304719977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128439691992739072959969 846329768994554304719977)
                    ·
                      refine ⟨634747326745915728539983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846329768994554304719977 634747326745915728539983)
                      ·
                        rfl

theorem cell23_1236166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1236166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236166 prefixEnd_1236166 := by exact prefixLift 1236166
  have htrace : WordTrace (prefixWord ++ tailWord_1236166) baseStart_1236166 baseEnd_1236166 := by
    simpa [prefixWord, tailWord_1236166, baseEnd_1236166] using wordTrace_append hprefix tailTrace_1236166
  have hstable : (prefixWord ++ tailWord_1236166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236166).length < 2 ^ (prefixWord ++ tailWord_1236166).sum := by decide
  have hdescent : baseEnd_1236166 < baseStart_1236166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236191 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1236191 : Nat := 118140960795 + 1236191 * 2 ^ 59
def prefixEnd_1236191 : Nat := 4983230072969 + 3 ^ 40 * 1236191 * 2
def baseEnd_1236191 : Nat := 634760163762278130727367

theorem tailTrace_1236191 : CollatzResearch.WordTrace tailWord_1236191 prefixEnd_1236191 634760163762278130727367 := by
  unfold tailWord_1236191
  simp only [CollatzResearch.WordTrace]
  refine ⟨45087589864498606459420427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30058393242999070972946951 45087589864498606459420427)
  ·
    refine ⟨67631384796747909689130641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45087589864498606459420427 67631384796747909689130641)
    ·
      refine ⟨50723538597560932266847981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67631384796747909689130641 50723538597560932266847981)
      ·
        refine ⟨19021326974085349600067993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50723538597560932266847981 19021326974085349600067993)
        ·
          refine ⟨14265995230564012200050995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19021326974085349600067993 14265995230564012200050995)
          ·
            refine ⟨21398992845846018300076493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14265995230564012200050995 21398992845846018300076493)
            ·
              refine ⟨8024622317192256862528685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21398992845846018300076493 8024622317192256862528685)
              ·
                refine ⟨3009233368947096323448257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8024622317192256862528685 3009233368947096323448257)
                ·
                  refine ⟨2256925026710322242586193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009233368947096323448257 2256925026710322242586193)
                  ·
                    refine ⟨1692693770032741681939645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256925026710322242586193 1692693770032741681939645)
                    ·
                      refine ⟨634760163762278130727367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692693770032741681939645 634760163762278130727367)
                      ·
                        rfl

theorem cell23_1236191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1236191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236191 prefixEnd_1236191 := by exact prefixLift 1236191
  have htrace : WordTrace (prefixWord ++ tailWord_1236191) baseStart_1236191 baseEnd_1236191 := by
    simpa [prefixWord, tailWord_1236191, baseEnd_1236191] using wordTrace_append hprefix tailTrace_1236191
  have hstable : (prefixWord ++ tailWord_1236191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236191).length < 2 ^ (prefixWord ++ tailWord_1236191).sum := by decide
  have hdescent : baseEnd_1236191 < baseStart_1236191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236211 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 6]
def baseStart_1236211 : Nat := 118140960795 + 1236211 * 2 ^ 59
def prefixEnd_1236211 : Nat := 4983230072969 + 3 ^ 40 * 1236211 * 2
def baseEnd_1236211 : Nat := 70530048152818672497475

theorem tailTrace_1236211 : CollatzResearch.WordTrace tailWord_1236211 prefixEnd_1236211 70530048152818672497475 := by
  unfold tailWord_1236211
  simp only [CollatzResearch.WordTrace]
  refine ⟨45088319324426149875148487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30058879549617433250098991 45088319324426149875148487)
  ·
    refine ⟨67632478986639224812722731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45088319324426149875148487 67632478986639224812722731)
    ·
      refine ⟨101448718479958837219084097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67632478986639224812722731 101448718479958837219084097)
      ·
        refine ⟨76086538859969127914313073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101448718479958837219084097 76086538859969127914313073)
        ·
          refine ⟨57064904144976845935734805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76086538859969127914313073 57064904144976845935734805)
          ·
            refine ⟨2674917381795789653237569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57064904144976845935734805 2674917381795789653237569)
            ·
              refine ⟨2006188036346842239928177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674917381795789653237569 2006188036346842239928177)
              ·
                refine ⟨1504641027260131679946133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006188036346842239928177 1504641027260131679946133)
                ·
                  refine ⟨70530048152818672497475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1504641027260131679946133 70530048152818672497475)
                  ·
                    rfl

theorem cell23_1236211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 6].length) (baseStart_1236211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236211 prefixEnd_1236211 := by exact prefixLift 1236211
  have htrace : WordTrace (prefixWord ++ tailWord_1236211) baseStart_1236211 baseEnd_1236211 := by
    simpa [prefixWord, tailWord_1236211, baseEnd_1236211] using wordTrace_append hprefix tailTrace_1236211
  have hstable : (prefixWord ++ tailWord_1236211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236211).length < 2 ^ (prefixWord ++ tailWord_1236211).sum := by decide
  have hdescent : baseEnd_1236211 < baseStart_1236211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236234 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1236234 : Nat := 118140960795 + 1236234 * 2 ^ 59
def prefixEnd_1236234 : Nat := 4983230072969 + 3 ^ 40 * 1236234 * 2
def baseEnd_1236234 : Nat := 634782243430421462489669

theorem tailTrace_1236234 : CollatzResearch.WordTrace tailWord_1236234 prefixEnd_1236234 634782243430421462489669 := by
  unfold tailWord_1236234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272289550835706200808939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30059438802228549868823837 11272289550835706200808939)
  ·
    refine ⟨16908434326253559301213409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11272289550835706200808939 16908434326253559301213409)
    ·
      refine ⟨12681325744690169475910057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16908434326253559301213409 12681325744690169475910057)
      ·
        refine ⟨9510994308517627106932543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12681325744690169475910057 9510994308517627106932543)
        ·
          refine ⟨14266491462776440660398815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9510994308517627106932543 14266491462776440660398815)
          ·
            refine ⟨21399737194164660990598223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14266491462776440660398815 21399737194164660990598223)
            ·
              refine ⟨32099605791246991485897335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21399737194164660990598223 32099605791246991485897335)
              ·
                refine ⟨48149408686870487228846003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32099605791246991485897335 48149408686870487228846003)
                ·
                  refine ⟨72224113030305730843269005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48149408686870487228846003 72224113030305730843269005)
                  ·
                    refine ⟨27084042386364649066225877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72224113030305730843269005 27084042386364649066225877)
                    ·
                      refine ⟨634782243430421462489669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27084042386364649066225877 634782243430421462489669)
                      ·
                        rfl

theorem cell23_1236234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1236234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236234 prefixEnd_1236234 := by exact prefixLift 1236234
  have htrace : WordTrace (prefixWord ++ tailWord_1236234) baseStart_1236234 baseEnd_1236234 := by
    simpa [prefixWord, tailWord_1236234, baseEnd_1236234] using wordTrace_append hprefix tailTrace_1236234
  have hstable : (prefixWord ++ tailWord_1236234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236234).length < 2 ^ (prefixWord ++ tailWord_1236234).sum := by decide
  have hdescent : baseEnd_1236234 < baseStart_1236234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236238 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1236238 : Nat := 118140960795 + 1236238 * 2 ^ 59
def prefixEnd_1236238 : Nat := 4983230072969 + 3 ^ 40 * 1236238 * 2
def baseEnd_1236238 : Nat := 634784297353039446839651

theorem tailTrace_1236238 : CollatzResearch.WordTrace tailWord_1236238 prefixEnd_1236238 634784297353039446839651 := by
  unfold tailWord_1236238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5636163011916041685797671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30059536063552222324254245 5636163011916041685797671)
  ·
    refine ⟨8454244517874062528696507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5636163011916041685797671 8454244517874062528696507)
    ·
      refine ⟨12681366776811093793044761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8454244517874062528696507 12681366776811093793044761)
      ·
        refine ⟨9511025082608320344783571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12681366776811093793044761 9511025082608320344783571)
        ·
          refine ⟨14266537623912480517175357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9511025082608320344783571 14266537623912480517175357)
          ·
            refine ⟨5349951608967180193940759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14266537623912480517175357 5349951608967180193940759)
            ·
              refine ⟨8024927413450770290911139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349951608967180193940759 8024927413450770290911139)
              ·
                refine ⟨12037391120176155436366709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024927413450770290911139 12037391120176155436366709)
                ·
                  refine ⟨1128505417516514572159379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12037391120176155436366709 1128505417516514572159379)
                  ·
                    refine ⟨1692758126274771858239069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1128505417516514572159379 1692758126274771858239069)
                    ·
                      refine ⟨634784297353039446839651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692758126274771858239069 634784297353039446839651)
                      ·
                        rfl

theorem cell23_1236238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1236238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236238 prefixEnd_1236238 := by exact prefixLift 1236238
  have htrace : WordTrace (prefixWord ++ tailWord_1236238) baseStart_1236238 baseEnd_1236238 := by
    simpa [prefixWord, tailWord_1236238, baseEnd_1236238] using wordTrace_append hprefix tailTrace_1236238
  have hstable : (prefixWord ++ tailWord_1236238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236238).length < 2 ^ (prefixWord ++ tailWord_1236238).sum := by decide
  have hdescent : baseEnd_1236238 < baseStart_1236238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236241 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_1236241 : Nat := 118140960795 + 1236241 * 2 ^ 59
def prefixEnd_1236241 : Nat := 4983230072969 + 3 ^ 40 * 1236241 * 2
def baseEnd_1236241 : Nat := 211595279265000978367379

theorem tailTrace_1236241 : CollatzResearch.WordTrace tailWord_1236241 prefixEnd_1236241 211595279265000978367379 := by
  unfold tailWord_1236241
  simp only [CollatzResearch.WordTrace]
  refine ⟨45089413514317464998740577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30059609009544976665827051 45089413514317464998740577)
  ·
    refine ⟨33817060135738098749055433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45089413514317464998740577 33817060135738098749055433)
    ·
      refine ⟨25362795101803574061791575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33817060135738098749055433 25362795101803574061791575)
      ·
        refine ⟨38044192652705361092687363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25362795101803574061791575 38044192652705361092687363)
        ·
          refine ⟨57066288979058041639031045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38044192652705361092687363 57066288979058041639031045)
          ·
            refine ⟨10699929183573382807318321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57066288979058041639031045 10699929183573382807318321)
            ·
              refine ⟨8024946887680037105488741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10699929183573382807318321 8024946887680037105488741)
              ·
                refine ⟨1504677541440006957279139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8024946887680037105488741 1504677541440006957279139)
                ·
                  refine ⟨2257016312160010435918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504677541440006957279139 2257016312160010435918709)
                  ·
                    refine ⟨211595279265000978367379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2257016312160010435918709 211595279265000978367379)
                    ·
                      rfl

theorem cell23_1236241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_1236241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236241 prefixEnd_1236241 := by exact prefixLift 1236241
  have htrace : WordTrace (prefixWord ++ tailWord_1236241) baseStart_1236241 baseEnd_1236241 := by
    simpa [prefixWord, tailWord_1236241, baseEnd_1236241] using wordTrace_append hprefix tailTrace_1236241
  have hstable : (prefixWord ++ tailWord_1236241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236241).length < 2 ^ (prefixWord ++ tailWord_1236241).sum := by decide
  have hdescent : baseEnd_1236241 < baseStart_1236241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236248 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1236248 : Nat := 118140960795 + 1236248 * 2 ^ 59
def prefixEnd_1236248 : Nat := 4983230072969 + 3 ^ 40 * 1236248 * 2
def baseEnd_1236248 : Nat := 634789432159584407714605

theorem tailTrace_1236248 : CollatzResearch.WordTrace tailWord_1236248 prefixEnd_1236248 634789432159584407714605 := by
  unfold tailWord_1236248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22544834412646052597122699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30059779216861403462830265 22544834412646052597122699)
  ·
    refine ⟨33817251618969078895684049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22544834412646052597122699 33817251618969078895684049)
    ·
      refine ⟨25362938714226809171763037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33817251618969078895684049 25362938714226809171763037)
      ·
        refine ⟨9511102017835053439411139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25362938714226809171763037 9511102017835053439411139)
        ·
          refine ⟨14266653026752580159116709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9511102017835053439411139 14266653026752580159116709)
          ·
            refine ⟨2674997442516108779834383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14266653026752580159116709 2674997442516108779834383)
            ·
              refine ⟨4012496163774163169751575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674997442516108779834383 4012496163774163169751575)
              ·
                refine ⟨6018744245661244754627363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012496163774163169751575 6018744245661244754627363)
                ·
                  refine ⟨9028116368491867131941045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6018744245661244754627363 9028116368491867131941045)
                  ·
                    refine ⟨846385909546112543619473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9028116368491867131941045 846385909546112543619473)
                    ·
                      refine ⟨634789432159584407714605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846385909546112543619473 634789432159584407714605)
                      ·
                        rfl

theorem cell23_1236248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1236248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236248 prefixEnd_1236248 := by exact prefixLift 1236248
  have htrace : WordTrace (prefixWord ++ tailWord_1236248) baseStart_1236248 baseEnd_1236248 := by
    simpa [prefixWord, tailWord_1236248, baseEnd_1236248] using wordTrace_append hprefix tailTrace_1236248
  have hstable : (prefixWord ++ tailWord_1236248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236248).length < 2 ^ (prefixWord ++ tailWord_1236248).sum := by decide
  have hdescent : baseEnd_1236248 < baseStart_1236248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236295 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_1236295 : Nat := 118140960795 + 1236295 * 2 ^ 59
def prefixEnd_1236295 : Nat := 4983230072969 + 3 ^ 40 * 1236295 * 2
def baseEnd_1236295 : Nat := 634813565750345723826889

theorem tailTrace_1236295 : CollatzResearch.WordTrace tailWord_1236295 prefixEnd_1236295 634813565750345723826889 := by
  unfold tailWord_1236295
  simp only [CollatzResearch.WordTrace]
  refine ⟨45091383056121832221206339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30060922037414554814137559 45091383056121832221206339)
  ·
    refine ⟨67637074584182748331809509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45091383056121832221206339 67637074584182748331809509)
    ·
      refine ⟨12681951484534265312214283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67637074584182748331809509 12681951484534265312214283)
      ·
        refine ⟨19022927226801397968321425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12681951484534265312214283 19022927226801397968321425)
        ·
          refine ⟨14267195420101048476241069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19022927226801397968321425 14267195420101048476241069)
          ·
            refine ⟨5350198282537893178590401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14267195420101048476241069 5350198282537893178590401)
            ·
              refine ⟨4012648711903419883942801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350198282537893178590401 4012648711903419883942801)
              ·
                refine ⟨3009486533927564912957101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4012648711903419883942801 3009486533927564912957101)
                ·
                  refine ⟨1128557450222836842358913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3009486533927564912957101 1128557450222836842358913)
                  ·
                    refine ⟨846418087667127631769185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128557450222836842358913 846418087667127631769185)
                    ·
                      refine ⟨634813565750345723826889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846418087667127631769185 634813565750345723826889)
                      ·
                        rfl

theorem cell23_1236295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_1236295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236295 prefixEnd_1236295 := by exact prefixLift 1236295
  have htrace : WordTrace (prefixWord ++ tailWord_1236295) baseStart_1236295 baseEnd_1236295 := by
    simpa [prefixWord, tailWord_1236295, baseEnd_1236295] using wordTrace_append hprefix tailTrace_1236295
  have hstable : (prefixWord ++ tailWord_1236295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236295).length < 2 ^ (prefixWord ++ tailWord_1236295).sum := by decide
  have hdescent : baseEnd_1236295 < baseStart_1236295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236355 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 3, 3, 2]
def baseStart_1236355 : Nat := 118140960795 + 1236355 * 2 ^ 59
def prefixEnd_1236355 : Nat := 4983230072969 + 3 ^ 40 * 1236355 * 2
def baseEnd_1236355 : Nat := 634844374589615489076613

theorem tailTrace_1236355 : CollatzResearch.WordTrace tailWord_1236355 prefixEnd_1236355 634844374589615489076613 := by
  unfold tailWord_1236355
  simp only [CollatzResearch.WordTrace]
  refine ⟨45093571435904462468390519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30062380957269641645593679 45093571435904462468390519)
  ·
    refine ⟨67640357153856693702585779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45093571435904462468390519 67640357153856693702585779)
    ·
      refine ⟨101460535730785040553878669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67640357153856693702585779 101460535730785040553878669)
      ·
        refine ⟨38047700899044390207704501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101460535730785040553878669 38047700899044390207704501)
        ·
          refine ⟨3566971959285411581972297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38047700899044390207704501 3566971959285411581972297)
          ·
            refine ⟨2675228969464058686479223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566971959285411581972297 2675228969464058686479223)
            ·
              refine ⟨4012843454196088029718835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675228969464058686479223 4012843454196088029718835)
              ·
                refine ⟨6019265181294132044578253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012843454196088029718835 6019265181294132044578253)
                ·
                  refine ⟨2257224442985299516716845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6019265181294132044578253 2257224442985299516716845)
                  ·
                    refine ⟨846459166119487318768817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257224442985299516716845 846459166119487318768817)
                    ·
                      refine ⟨634844374589615489076613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846459166119487318768817 634844374589615489076613)
                      ·
                        rfl

theorem cell23_1236355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_1236355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236355 prefixEnd_1236355 := by exact prefixLift 1236355
  have htrace : WordTrace (prefixWord ++ tailWord_1236355) baseStart_1236355 baseEnd_1236355 := by
    simpa [prefixWord, tailWord_1236355, baseEnd_1236355] using wordTrace_append hprefix tailTrace_1236355
  have hstable : (prefixWord ++ tailWord_1236355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236355).length < 2 ^ (prefixWord ++ tailWord_1236355).sum := by decide
  have hdescent : baseEnd_1236355 < baseStart_1236355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236371 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3]
def baseStart_1236371 : Nat := 118140960795 + 1236371 * 2 ^ 59
def prefixEnd_1236371 : Nat := 4983230072969 + 3 ^ 40 * 1236371 * 2
def baseEnd_1236371 : Nat := 634852590280087426476539

theorem tailTrace_1236371 : CollatzResearch.WordTrace tailWord_1236371 prefixEnd_1236371 634852590280087426476539 := by
  unfold tailWord_1236371
  simp only [CollatzResearch.WordTrace]
  refine ⟨45094155003846497200972967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30062770002564331467315311 45094155003846497200972967)
  ·
    refine ⟨67641232505769745801459451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45094155003846497200972967 67641232505769745801459451)
    ·
      refine ⟨101461848758654618702189177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67641232505769745801459451 101461848758654618702189177)
      ·
        refine ⟨76096386568990964026641883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101461848758654618702189177 76096386568990964026641883)
        ·
          refine ⟨114144579853486446039962825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76096386568990964026641883 114144579853486446039962825)
          ·
            refine ⟨85608434890114834529972119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114144579853486446039962825 85608434890114834529972119)
            ·
              refine ⟨128412652335172251794958179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85608434890114834529972119 128412652335172251794958179)
              ·
                refine ⟨192618978502758377692437269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128412652335172251794958179 192618978502758377692437269)
                ·
                  refine ⟨9029014617316798954332997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192618978502758377692437269 9029014617316798954332997)
                  ·
                    refine ⟨1692940240746899803937437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9029014617316798954332997 1692940240746899803937437)
                    ·
                      refine ⟨634852590280087426476539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1692940240746899803937437 634852590280087426476539)
                      ·
                        rfl

theorem cell23_1236371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_1236371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236371 prefixEnd_1236371 := by exact prefixLift 1236371
  have htrace : WordTrace (prefixWord ++ tailWord_1236371) baseStart_1236371 baseEnd_1236371 := by
    simpa [prefixWord, tailWord_1236371, baseEnd_1236371] using wordTrace_append hprefix tailTrace_1236371
  have hstable : (prefixWord ++ tailWord_1236371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236371).length < 2 ^ (prefixWord ++ tailWord_1236371).sum := by decide
  have hdescent : baseEnd_1236371 < baseStart_1236371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236380 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1236380 : Nat := 118140960795 + 1236380 * 2 ^ 59
def prefixEnd_1236380 : Nat := 4983230072969 + 3 ^ 40 * 1236380 * 2
def baseEnd_1236380 : Nat := 634857211605977891263999

theorem tailTrace_1236380 : CollatzResearch.WordTrace tailWord_1236380 prefixEnd_1236380 634857211605977891263999 := by
  unfold tailWord_1236380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22547241630406945869025297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30062988840542594492033729 22547241630406945869025297)
  ·
    refine ⟨16910431222805209401768973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22547241630406945869025297 16910431222805209401768973)
    ·
      refine ⟨6341411708551953525663365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16910431222805209401768973 6341411708551953525663365)
      ·
        refine ⟨1189014695353491286061881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6341411708551953525663365 1189014695353491286061881)
        ·
          refine ⟨891761021515118464546411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189014695353491286061881 891761021515118464546411)
          ·
            refine ⟨1337641532272677696819617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891761021515118464546411 1337641532272677696819617)
            ·
              refine ⟨1003231149204508272614713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337641532272677696819617 1003231149204508272614713)
              ·
                refine ⟨752423361903381204461035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003231149204508272614713 752423361903381204461035)
                ·
                  refine ⟨1128635042855071806691553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752423361903381204461035 1128635042855071806691553)
                  ·
                    refine ⟨846476282141303855018665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128635042855071806691553 846476282141303855018665)
                    ·
                      refine ⟨634857211605977891263999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846476282141303855018665 634857211605977891263999)
                      ·
                        rfl

theorem cell23_1236380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1236380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236380 prefixEnd_1236380 := by exact prefixLift 1236380
  have htrace : WordTrace (prefixWord ++ tailWord_1236380) baseStart_1236380 baseEnd_1236380 := by
    simpa [prefixWord, tailWord_1236380, baseEnd_1236380] using wordTrace_append hprefix tailTrace_1236380
  have hstable : (prefixWord ++ tailWord_1236380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236380).length < 2 ^ (prefixWord ++ tailWord_1236380).sum := by decide
  have hdescent : baseEnd_1236380 < baseStart_1236380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236431 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_1236431 : Nat := 118140960795 + 1236431 * 2 ^ 59
def prefixEnd_1236431 : Nat := 4983230072969 + 3 ^ 40 * 1236431 * 2
def baseEnd_1236431 : Nat := 634883399119357191726263

theorem tailTrace_1236431 : CollatzResearch.WordTrace tailWord_1236431 prefixEnd_1236431 634883399119357191726263 := by
  unfold tailWord_1236431
  simp only [CollatzResearch.WordTrace]
  refine ⟨45096343383629127448157147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30064228922419418298771431 45096343383629127448157147)
  ·
    refine ⟨67644515075443691172235721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45096343383629127448157147 67644515075443691172235721)
    ·
      refine ⟨50733386306582768379176791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67644515075443691172235721 50733386306582768379176791)
      ·
        refine ⟨76100079459874152568765187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50733386306582768379176791 76100079459874152568765187)
        ·
          refine ⟨114150119189811228853147781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76100079459874152568765187 114150119189811228853147781)
          ·
            refine ⟨21403147348089605409965209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114150119189811228853147781 21403147348089605409965209)
            ·
              refine ⟨16052360511067204057473907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21403147348089605409965209 16052360511067204057473907)
              ·
                refine ⟨24078540766600806086210861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16052360511067204057473907 24078540766600806086210861)
                ·
                  refine ⟨9029452787475302282329073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24078540766600806086210861 9029452787475302282329073)
                  ·
                    refine ⟨6772089590606476711746805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9029452787475302282329073 6772089590606476711746805)
                    ·
                      refine ⟨634883399119357191726263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6772089590606476711746805 634883399119357191726263)
                      ·
                        rfl

theorem cell23_1236431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_1236431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236431 prefixEnd_1236431 := by exact prefixLift 1236431
  have htrace : WordTrace (prefixWord ++ tailWord_1236431) baseStart_1236431 baseEnd_1236431 := by
    simpa [prefixWord, tailWord_1236431, baseEnd_1236431] using wordTrace_append hprefix tailTrace_1236431
  have hstable : (prefixWord ++ tailWord_1236431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236431).length < 2 ^ (prefixWord ++ tailWord_1236431).sum := by decide
  have hdescent : baseEnd_1236431 < baseStart_1236431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236436 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1236436 : Nat := 118140960795 + 1236436 * 2 ^ 59
def prefixEnd_1236436 : Nat := 4983230072969 + 3 ^ 40 * 1236436 * 2
def baseEnd_1236436 : Nat := 634885966522629672163741

theorem tailTrace_1236436 : CollatzResearch.WordTrace tailWord_1236436 prefixEnd_1236436 634885966522629672163741 := by
  unfold tailWord_1236436
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548262874305506651044581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30064350499074008868059441 22548262874305506651044581)
  ·
    refine ⟨4227799288932282497070859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22548262874305506651044581 4227799288932282497070859)
    ·
      refine ⟨6341698933398423745606289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4227799288932282497070859 6341698933398423745606289)
      ·
        refine ⟨4756274200048817809204717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6341698933398423745606289 4756274200048817809204717)
        ·
          refine ⟨1783602825018306678451769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4756274200048817809204717 1783602825018306678451769)
          ·
            refine ⟨1337702118763730008838827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783602825018306678451769 1337702118763730008838827)
            ·
              refine ⟨2006553178145595013258241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337702118763730008838827 2006553178145595013258241)
              ·
                refine ⟨1504914883609196259943681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006553178145595013258241 1504914883609196259943681)
                ·
                  refine ⟨1128686162706897194957761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504914883609196259943681 1128686162706897194957761)
                  ·
                    refine ⟨846514622030172896218321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128686162706897194957761 846514622030172896218321)
                    ·
                      refine ⟨634885966522629672163741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846514622030172896218321 634885966522629672163741)
                      ·
                        rfl

theorem cell23_1236436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1236436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236436 prefixEnd_1236436 := by exact prefixLift 1236436
  have htrace : WordTrace (prefixWord ++ tailWord_1236436) baseStart_1236436 baseEnd_1236436 := by
    simpa [prefixWord, tailWord_1236436, baseEnd_1236436] using wordTrace_append hprefix tailTrace_1236436
  have hstable : (prefixWord ++ tailWord_1236436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236436).length < 2 ^ (prefixWord ++ tailWord_1236436).sum := by decide
  have hdescent : baseEnd_1236436 < baseStart_1236436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236471 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1236471 : Nat := 118140960795 + 1236471 * 2 ^ 59
def prefixEnd_1236471 : Nat := 4983230072969 + 3 ^ 40 * 1236471 * 2
def baseEnd_1236471 : Nat := 634903938345537035226079

theorem tailTrace_1236471 : CollatzResearch.WordTrace tailWord_1236471 prefixEnd_1236471 634903938345537035226079 := by
  unfold tailWord_1236471
  simp only [CollatzResearch.WordTrace]
  refine ⟨45097802303484214279613267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30065201535656142853075511 45097802303484214279613267)
  ·
    refine ⟨67646703455226321419419901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45097802303484214279613267 67646703455226321419419901)
    ·
      refine ⟨25367513795709870532282463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67646703455226321419419901 25367513795709870532282463)
      ·
        refine ⟨38051270693564805798423695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25367513795709870532282463 38051270693564805798423695)
        ·
          refine ⟨57076906040347208697635543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38051270693564805798423695 57076906040347208697635543)
          ·
            refine ⟨85615359060520813046453315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57076906040347208697635543 85615359060520813046453315)
            ·
              refine ⟨128423038590781219569679973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85615359060520813046453315 128423038590781219569679973)
              ·
                refine ⟨24079319735771478669314995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128423038590781219569679973 24079319735771478669314995)
                ·
                  refine ⟨36118979603657218003972493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24079319735771478669314995 36118979603657218003972493)
                  ·
                    refine ⟨13544617351371456751489685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36118979603657218003972493 13544617351371456751489685)
                    ·
                      refine ⟨634903938345537035226079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13544617351371456751489685 634903938345537035226079)
                      ·
                        rfl

theorem cell23_1236471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1236471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236471 prefixEnd_1236471 := by exact prefixLift 1236471
  have htrace : WordTrace (prefixWord ++ tailWord_1236471) baseStart_1236471 baseEnd_1236471 := by
    simpa [prefixWord, tailWord_1236471, baseEnd_1236471] using wordTrace_append hprefix tailTrace_1236471
  have hstable : (prefixWord ++ tailWord_1236471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236471).length < 2 ^ (prefixWord ++ tailWord_1236471).sum := by decide
  have hdescent : baseEnd_1236471 < baseStart_1236471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236515 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 6]
def baseStart_1236515 : Nat := 118140960795 + 1236515 * 2 ^ 59
def prefixEnd_1236515 : Nat := 4983230072969 + 3 ^ 40 * 1236515 * 2
def baseEnd_1236515 : Nat := 70547392388259429230653

theorem tailTrace_1236515 : CollatzResearch.WordTrace tailWord_1236515 prefixEnd_1236515 70547392388259429230653 := by
  unfold tailWord_1236515
  simp only [CollatzResearch.WordTrace]
  refine ⟨45099407115324809794214999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30066271410216539862809999 45099407115324809794214999)
  ·
    refine ⟨67649110672987214691322499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45099407115324809794214999 67649110672987214691322499)
    ·
      refine ⟨101473666009480822036983749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67649110672987214691322499 101473666009480822036983749)
      ·
        refine ⟨19026312376777654131934453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101473666009480822036983749 19026312376777654131934453)
        ·
          refine ⟨1783716785322905074868855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19026312376777654131934453 1783716785322905074868855)
          ·
            refine ⟨2675575177984357612303283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783716785322905074868855 2675575177984357612303283)
            ·
              refine ⟨4013362766976536418454925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675575177984357612303283 4013362766976536418454925)
              ·
                refine ⟨1505011037616201156920597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4013362766976536418454925 1505011037616201156920597)
                ·
                  refine ⟨70547392388259429230653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1505011037616201156920597 70547392388259429230653)
                  ·
                    rfl

theorem cell23_1236515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 6].length) (baseStart_1236515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236515 prefixEnd_1236515 := by exact prefixLift 1236515
  have htrace : WordTrace (prefixWord ++ tailWord_1236515) baseStart_1236515 baseEnd_1236515 := by
    simpa [prefixWord, tailWord_1236515, baseEnd_1236515] using wordTrace_append hprefix tailTrace_1236515
  have hstable : (prefixWord ++ tailWord_1236515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236515).length < 2 ^ (prefixWord ++ tailWord_1236515).sum := by decide
  have hdescent : baseEnd_1236515 < baseStart_1236515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236558 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_1236558 : Nat := 118140960795 + 1236558 * 2 ^ 59
def prefixEnd_1236558 : Nat := 4983230072969 + 3 ^ 40 * 1236558 * 2
def baseEnd_1236558 : Nat := 211649537054159398279393

theorem tailTrace_1236558 : CollatzResearch.WordTrace tailWord_1236558 prefixEnd_1236558 211649537054159398279393 := by
  unfold tailWord_1236558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637621931771128517253791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30067316969446018758686885 5637621931771128517253791)
  ·
    refine ⟨8456432897656692775880687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5637621931771128517253791 8456432897656692775880687)
    ·
      refine ⟨12684649346485039163821031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8456432897656692775880687 12684649346485039163821031)
      ·
        refine ⟨19026974019727558745731547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12684649346485039163821031 19026974019727558745731547)
        ·
          refine ⟨28540461029591338118597321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19026974019727558745731547 28540461029591338118597321)
          ·
            refine ⟨21405345772193503588947991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28540461029591338118597321 21405345772193503588947991)
            ·
              refine ⟨32108018658290255383421987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21405345772193503588947991 32108018658290255383421987)
              ·
                refine ⟨48162027987435383075132981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32108018658290255383421987 48162027987435383075132981)
                ·
                  refine ⟨4515190123822067163293717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48162027987435383075132981 4515190123822067163293717)
                  ·
                    refine ⟨211649537054159398279393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4515190123822067163293717 211649537054159398279393)
                    ·
                      rfl

theorem cell23_1236558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_1236558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236558 prefixEnd_1236558 := by exact prefixLift 1236558
  have htrace : WordTrace (prefixWord ++ tailWord_1236558) baseStart_1236558 baseEnd_1236558 := by
    simpa [prefixWord, tailWord_1236558, baseEnd_1236558] using wordTrace_append hprefix tailTrace_1236558
  have hstable : (prefixWord ++ tailWord_1236558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236558).length < 2 ^ (prefixWord ++ tailWord_1236558).sum := by decide
  have hdescent : baseEnd_1236558 < baseStart_1236558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236565 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1236565 : Nat := 118140960795 + 1236565 * 2 ^ 59
def prefixEnd_1236565 : Nat := 4983230072969 + 3 ^ 40 * 1236565 * 2
def baseEnd_1236565 : Nat := 634952205527059667450647

theorem tailTrace_1236565 : CollatzResearch.WordTrace tailWord_1236565 prefixEnd_1236565 634952205527059667450647 := by
  unfold tailWord_1236565
  simp only [CollatzResearch.WordTrace]
  refine ⟨45101230765143668333535149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30067487176762445555690099 45101230765143668333535149)
  ·
    refine ⟨16912961536928875625075681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45101230765143668333535149 16912961536928875625075681)
    ·
      refine ⟨12684721152696656718806761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16912961536928875625075681 12684721152696656718806761)
      ·
        refine ⟨9513540864522492539105071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12684721152696656718806761 9513540864522492539105071)
        ·
          refine ⟨14270311296783738808657607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513540864522492539105071 14270311296783738808657607)
          ·
            refine ⟨21405466945175608212986411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270311296783738808657607 21405466945175608212986411)
            ·
              refine ⟨32108200417763412319479617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21405466945175608212986411 32108200417763412319479617)
              ·
                refine ⟨24081150313322559239609713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32108200417763412319479617 24081150313322559239609713)
                ·
                  refine ⟨18060862734991919429707285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24081150313322559239609713 18060862734991919429707285)
                  ·
                    refine ⟨846602940702746223267529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18060862734991919429707285 846602940702746223267529)
                    ·
                      refine ⟨634952205527059667450647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846602940702746223267529 634952205527059667450647)
                      ·
                        rfl

theorem cell23_1236565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1236565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236565 prefixEnd_1236565 := by exact prefixLift 1236565
  have htrace : WordTrace (prefixWord ++ tailWord_1236565) baseStart_1236565 baseEnd_1236565 := by
    simpa [prefixWord, tailWord_1236565, baseEnd_1236565] using wordTrace_append hprefix tailTrace_1236565
  have hstable : (prefixWord ++ tailWord_1236565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236565).length < 2 ^ (prefixWord ++ tailWord_1236565).sum := by decide
  have hdescent : baseEnd_1236565 < baseStart_1236565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236568 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1236568 : Nat := 118140960795 + 1236568 * 2 ^ 59
def prefixEnd_1236568 : Nat := 4983230072969 + 3 ^ 40 * 1236568 * 2
def baseEnd_1236568 : Nat := 634953745969023155713133

theorem tailTrace_1236568 : CollatzResearch.WordTrace tailWord_1236568 prefixEnd_1236568 634953745969023155713133 := by
  unfold tailWord_1236568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550670092066399922947179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30067560122755199897262905 22550670092066399922947179)
  ·
    refine ⟨33826005138099599884420769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22550670092066399922947179 33826005138099599884420769)
    ·
      refine ⟨25369503853574699913315577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33826005138099599884420769 25369503853574699913315577)
      ·
        refine ⟨19027127890181024934986683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25369503853574699913315577 19027127890181024934986683)
        ·
          refine ⟨28540691835271537402480025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19027127890181024934986683 28540691835271537402480025)
          ·
            refine ⟨21405518876453653051860019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28540691835271537402480025 21405518876453653051860019)
            ·
              refine ⟨32108278314680479577790029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21405518876453653051860019 32108278314680479577790029)
              ·
                refine ⟨12040604368005179841671261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32108278314680479577790029 12040604368005179841671261)
                ·
                  refine ⟨4515226638001942440626723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12040604368005179841671261 4515226638001942440626723)
                  ·
                    refine ⟨6772839957002913660940085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4515226638001942440626723 6772839957002913660940085)
                    ·
                      refine ⟨634953745969023155713133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6772839957002913660940085 634953745969023155713133)
                      ·
                        rfl

theorem cell23_1236568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1236568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236568 prefixEnd_1236568 := by exact prefixLift 1236568
  have htrace : WordTrace (prefixWord ++ tailWord_1236568) baseStart_1236568 baseEnd_1236568 := by
    simpa [prefixWord, tailWord_1236568, baseEnd_1236568] using wordTrace_append hprefix tailTrace_1236568
  have hstable : (prefixWord ++ tailWord_1236568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236568).length < 2 ^ (prefixWord ++ tailWord_1236568).sum := by decide
  have hdescent : baseEnd_1236568 < baseStart_1236568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236585 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_1236585 : Nat := 118140960795 + 1236585 * 2 ^ 59
def prefixEnd_1236585 : Nat := 4983230072969 + 3 ^ 40 * 1236585 * 2
def baseEnd_1236585 : Nat := 634962475140149589200555

theorem tailTrace_1236585 : CollatzResearch.WordTrace tailWord_1236585 prefixEnd_1236585 634962475140149589200555 := by
  unfold tailWord_1236585
  simp only [CollatzResearch.WordTrace]
  refine ⟨45101960225071211749263209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30067973483380807832842139 45101960225071211749263209)
  ·
    refine ⟨33826470168803408811947407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45101960225071211749263209 33826470168803408811947407)
    ·
      refine ⟨50739705253205113217921111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33826470168803408811947407 50739705253205113217921111)
      ·
        refine ⟨76109557879807669826881667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50739705253205113217921111 76109557879807669826881667)
        ·
          refine ⟨114164336819711504740322501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76109557879807669826881667 114164336819711504740322501)
          ·
            refine ⟨21405813153695907138810469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114164336819711504740322501 21405813153695907138810469)
            ·
              refine ⟨4013589966317982588526963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21405813153695907138810469 4013589966317982588526963)
              ·
                refine ⟨6020384949476973882790445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013589966317982588526963 6020384949476973882790445)
                ·
                  refine ⟨2257644356053865206046417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6020384949476973882790445 2257644356053865206046417)
                  ·
                    refine ⟨1693233267040398904534813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2257644356053865206046417 1693233267040398904534813)
                    ·
                      refine ⟨634962475140149589200555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693233267040398904534813 634962475140149589200555)
                      ·
                        rfl

theorem cell23_1236585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_1236585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236585 prefixEnd_1236585 := by exact prefixLift 1236585
  have htrace : WordTrace (prefixWord ++ tailWord_1236585) baseStart_1236585 baseEnd_1236585 := by
    simpa [prefixWord, tailWord_1236585, baseEnd_1236585] using wordTrace_append hprefix tailTrace_1236585
  have hstable : (prefixWord ++ tailWord_1236585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236585).length < 2 ^ (prefixWord ++ tailWord_1236585).sum := by decide
  have hdescent : baseEnd_1236585 < baseStart_1236585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236609 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1236609 : Nat := 118140960795 + 1236609 * 2 ^ 59
def prefixEnd_1236609 : Nat := 4983230072969 + 3 ^ 40 * 1236609 * 2
def baseEnd_1236609 : Nat := 211658266225285831766815

theorem tailTrace_1236609 : CollatzResearch.WordTrace tailWord_1236609 prefixEnd_1236609 211658266225285831766815 := by
  unfold tailWord_1236609
  simp only [CollatzResearch.WordTrace]
  refine ⟨45102835576984263848136881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30068557051322842565424587 45102835576984263848136881)
  ·
    refine ⟨33827126682738197886102661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45102835576984263848136881 33827126682738197886102661)
    ·
      refine ⟨6342586253013412103644249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33827126682738197886102661 6342586253013412103644249)
      ·
        refine ⟨4756939689760059077733187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6342586253013412103644249 4756939689760059077733187)
        ·
          refine ⟨7135409534640088616599781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756939689760059077733187 7135409534640088616599781)
          ·
            refine ⟨1337889287745016615612459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7135409534640088616599781 1337889287745016615612459)
            ·
              refine ⟨2006833931617524923418689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337889287745016615612459 2006833931617524923418689)
              ·
                refine ⟨1505125448713143692564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006833931617524923418689 1505125448713143692564017)
                ·
                  refine ⟨1128844086534857769423013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1505125448713143692564017 1128844086534857769423013)
                  ·
                    refine ⟨211658266225285831766815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1128844086534857769423013 211658266225285831766815)
                    ·
                      rfl

theorem cell23_1236609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1236609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236609 prefixEnd_1236609 := by exact prefixLift 1236609
  have htrace : WordTrace (prefixWord ++ tailWord_1236609) baseStart_1236609 baseEnd_1236609 := by
    simpa [prefixWord, tailWord_1236609, baseEnd_1236609] using wordTrace_append hprefix tailTrace_1236609
  have hstable : (prefixWord ++ tailWord_1236609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236609).length < 2 ^ (prefixWord ++ tailWord_1236609).sum := by decide
  have hdescent : baseEnd_1236609 < baseStart_1236609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236625 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_1236625 : Nat := 118140960795 + 1236625 * 2 ^ 59
def prefixEnd_1236625 : Nat := 4983230072969 + 3 ^ 40 * 1236625 * 2
def baseEnd_1236625 : Nat := 634983014366329432700371

theorem tailTrace_1236625 : CollatzResearch.WordTrace tailWord_1236625 prefixEnd_1236625 634983014366329432700371 := by
  unfold tailWord_1236625
  simp only [CollatzResearch.WordTrace]
  refine ⟨45103419144926298580719329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30068946096617532387146219 45103419144926298580719329)
  ·
    refine ⟨33827564358694723935539497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45103419144926298580719329 33827564358694723935539497)
    ·
      refine ⟨25370673269021042951654623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33827564358694723935539497 25370673269021042951654623)
      ·
        refine ⟨38056009903531564427481935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25370673269021042951654623 38056009903531564427481935)
        ·
          refine ⟨57084014855297346641222903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38056009903531564427481935 57084014855297346641222903)
          ·
            refine ⟨85626022282946019961834355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57084014855297346641222903 85626022282946019961834355)
            ·
              refine ⟨128439033424419029942751533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85626022282946019961834355 128439033424419029942751533)
              ·
                refine ⟨48164637534157136228531825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128439033424419029942751533 48164637534157136228531825)
                ·
                  refine ⟨36123478150617852171398869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48164637534157136228531825 36123478150617852171398869)
                  ·
                    refine ⟨846644019155105910267161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36123478150617852171398869 846644019155105910267161)
                    ·
                      refine ⟨634983014366329432700371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846644019155105910267161 634983014366329432700371)
                      ·
                        rfl

theorem cell23_1236625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_1236625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236625 prefixEnd_1236625 := by exact prefixLift 1236625
  have htrace : WordTrace (prefixWord ++ tailWord_1236625) baseStart_1236625 baseEnd_1236625 := by
    simpa [prefixWord, tailWord_1236625, baseEnd_1236625] using wordTrace_append hprefix tailTrace_1236625
  have hstable : (prefixWord ++ tailWord_1236625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236625).length < 2 ^ (prefixWord ++ tailWord_1236625).sum := by decide
  have hdescent : baseEnd_1236625 < baseStart_1236625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236626 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1236626 : Nat := 118140960795 + 1236626 * 2 ^ 59
def prefixEnd_1236626 : Nat := 4983230072969 + 3 ^ 40 * 1236626 * 2
def baseEnd_1236626 : Nat := 211661175948994642929289

theorem tailTrace_1236626 : CollatzResearch.WordTrace tailWord_1236626 prefixEnd_1236626 211661175948994642929289 := by
  unfold tailWord_1236626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11275863904480668937876433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30068970411948450501003821 11275863904480668937876433)
  ·
    refine ⟨8456897928360501703407325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11275863904480668937876433 8456897928360501703407325)
    ·
      refine ⟨3171336723135188138777747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8456897928360501703407325 3171336723135188138777747)
      ·
        refine ⟨4757005084702782208166621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171336723135188138777747 4757005084702782208166621)
        ·
          refine ⟨1783876906763543328062483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4757005084702782208166621 1783876906763543328062483)
          ·
            refine ⟨2675815360145314992093725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783876906763543328062483 2675815360145314992093725)
            ·
              refine ⟨1003430760054493122035147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2675815360145314992093725 1003430760054493122035147)
              ·
                refine ⟨1505146140081739683052721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003430760054493122035147 1505146140081739683052721)
                ·
                  refine ⟨1128859605061304762289541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1505146140081739683052721 1128859605061304762289541)
                  ·
                    refine ⟨211661175948994642929289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1128859605061304762289541 211661175948994642929289)
                    ·
                      rfl

theorem cell23_1236626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1236626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236626 prefixEnd_1236626 := by exact prefixLift 1236626
  have htrace : WordTrace (prefixWord ++ tailWord_1236626) baseStart_1236626 baseEnd_1236626 := by
    simpa [prefixWord, tailWord_1236626, baseEnd_1236626] using wordTrace_append hprefix tailTrace_1236626
  have hstable : (prefixWord ++ tailWord_1236626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236626).length < 2 ^ (prefixWord ++ tailWord_1236626).sum := by decide
  have hdescent : baseEnd_1236626 < baseStart_1236626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236632 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1236632 : Nat := 118140960795 + 1236632 * 2 ^ 59
def prefixEnd_1236632 : Nat := 4983230072969 + 3 ^ 40 * 1236632 * 2
def baseEnd_1236632 : Nat := 634986608730910905312839

theorem tailTrace_1236632 : CollatzResearch.WordTrace tailWord_1236632 prefixEnd_1236632 634986608730910905312839 := by
  unfold tailWord_1236632
  simp only [CollatzResearch.WordTrace]
  refine ⟨22551837227950469388112075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30069116303933959184149433 22551837227950469388112075)
  ·
    refine ⟨33827755841925704082168113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22551837227950469388112075 33827755841925704082168113)
    ·
      refine ⟨25370816881444278061626085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33827755841925704082168113 25370816881444278061626085)
      ·
        refine ⟨4757028165270802136554891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25370816881444278061626085 4757028165270802136554891)
        ·
          refine ⟨7135542247906203204832337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757028165270802136554891 7135542247906203204832337)
          ·
            refine ⟨5351656685929652403624253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7135542247906203204832337 5351656685929652403624253)
            ·
              refine ⟨2006871257223619651359095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5351656685929652403624253 2006871257223619651359095)
              ·
                refine ⟨3010306885835429477038643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006871257223619651359095 3010306885835429477038643)
                ·
                  refine ⟨4515460328753144215557965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010306885835429477038643 4515460328753144215557965)
                  ·
                    refine ⟨1693297623282429080834237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4515460328753144215557965 1693297623282429080834237)
                    ·
                      refine ⟨634986608730910905312839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693297623282429080834237 634986608730910905312839)
                      ·
                        rfl

theorem cell23_1236632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1236632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236632 prefixEnd_1236632 := by exact prefixLift 1236632
  have htrace : WordTrace (prefixWord ++ tailWord_1236632) baseStart_1236632 baseEnd_1236632 := by
    simpa [prefixWord, tailWord_1236632, baseEnd_1236632] using wordTrace_append hprefix tailTrace_1236632
  have hstable : (prefixWord ++ tailWord_1236632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236632).length < 2 ^ (prefixWord ++ tailWord_1236632).sum := by decide
  have hdescent : baseEnd_1236632 < baseStart_1236632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236639 : List Nat := [1, 1, 2, 7, 1, 2, 2, 7]
def baseStart_1236639 : Nat := 118140960795 + 1236639 * 2 ^ 59
def prefixEnd_1236639 : Nat := 4983230072969 + 3 ^ 40 * 1236639 * 2
def baseEnd_1236639 : Nat := 23518155670203421404641

theorem tailTrace_1236639 : CollatzResearch.WordTrace tailWord_1236639 prefixEnd_1236639 23518155670203421404641 := by
  unfold tailWord_1236639
  simp only [CollatzResearch.WordTrace]
  refine ⟨45103929766875578971728971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30069286511250385981152647 45103929766875578971728971)
  ·
    refine ⟨67655894650313368457593457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45103929766875578971728971 67655894650313368457593457)
    ·
      refine ⟨50741920987735026343195093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67655894650313368457593457 50741920987735026343195093)
      ·
        refine ⟨1189263773150039679918635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 50741920987735026343195093 1189263773150039679918635)
        ·
          refine ⟨1783895659725059519877953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189263773150039679918635 1783895659725059519877953)
          ·
            refine ⟨1337921744793794639908465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783895659725059519877953 1337921744793794639908465)
            ·
              refine ⟨1003441308595345979931349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337921744793794639908465 1003441308595345979931349)
              ·
                refine ⟨23518155670203421404641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1003441308595345979931349 23518155670203421404641)
                ·
                  rfl

theorem cell23_1236639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 7].length) (baseStart_1236639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236639 prefixEnd_1236639 := by exact prefixLift 1236639
  have htrace : WordTrace (prefixWord ++ tailWord_1236639) baseStart_1236639 baseEnd_1236639 := by
    simpa [prefixWord, tailWord_1236639, baseEnd_1236639] using wordTrace_append hprefix tailTrace_1236639
  have hstable : (prefixWord ++ tailWord_1236639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236639).length < 2 ^ (prefixWord ++ tailWord_1236639).sum := by decide
  have hdescent : baseEnd_1236639 < baseStart_1236639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236692 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1236692 : Nat := 118140960795 + 1236692 * 2 ^ 59
def prefixEnd_1236692 : Nat := 4983230072969 + 3 ^ 40 * 1236692 * 2
def baseEnd_1236692 : Nat := 635017417570180670562563

theorem tailTrace_1236692 : CollatzResearch.WordTrace tailWord_1236692 prefixEnd_1236692 635017417570180670562563 := by
  unfold tailWord_1236692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22552931417841784511704165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30070575223789046015605553 22552931417841784511704165)
  ·
    refine ⟨4228674640845334595944531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22552931417841784511704165 4228674640845334595944531)
    ·
      refine ⟨6343011961268001893916797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4228674640845334595944531 6343011961268001893916797)
      ·
        refine ⟨2378629485475500710218799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6343011961268001893916797 2378629485475500710218799)
        ·
          refine ⟨3567944228213251065328199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378629485475500710218799 3567944228213251065328199)
          ·
            refine ⟨5351916342319876597992299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567944228213251065328199 5351916342319876597992299)
            ·
              refine ⟨8027874513479814896988449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351916342319876597992299 8027874513479814896988449)
              ·
                refine ⟨6020905885109861172741337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8027874513479814896988449 6020905885109861172741337)
                ·
                  refine ⟨4515679413832395879556003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6020905885109861172741337 4515679413832395879556003)
                  ·
                    refine ⟨6773519120748593819334005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4515679413832395879556003 6773519120748593819334005)
                    ·
                      refine ⟨635017417570180670562563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6773519120748593819334005 635017417570180670562563)
                      ·
                        rfl

theorem cell23_1236692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1236692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236692 prefixEnd_1236692 := by exact prefixLift 1236692
  have htrace : WordTrace (prefixWord ++ tailWord_1236692) baseStart_1236692 baseEnd_1236692 := by
    simpa [prefixWord, tailWord_1236692, baseEnd_1236692] using wordTrace_append hprefix tailTrace_1236692
  have hstable : (prefixWord ++ tailWord_1236692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236692).length < 2 ^ (prefixWord ++ tailWord_1236692).sum := by decide
  have hdescent : baseEnd_1236692 < baseStart_1236692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236722 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1236722 : Nat := 118140960795 + 1236722 * 2 ^ 59
def prefixEnd_1236722 : Nat := 4983230072969 + 3 ^ 40 * 1236722 * 2
def baseEnd_1236722 : Nat := 635032821989815553187425

theorem tailTrace_1236722 : CollatzResearch.WordTrace tailWord_1236722 prefixEnd_1236722 635032821989815553187425 := by
  unfold tailWord_1236722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11276739256393721036750105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30071304683716589431333613 11276739256393721036750105)
  ·
    refine ⟨8457554442295290777562579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11276739256393721036750105 8457554442295290777562579)
    ·
      refine ⟨12686331663442936166343869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8457554442295290777562579 12686331663442936166343869)
      ·
        refine ⟨4757374373791101062378951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12686331663442936166343869 4757374373791101062378951)
        ·
          refine ⟨7136061560686651593568427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757374373791101062378951 7136061560686651593568427)
          ·
            refine ⟨10704092341029977390352641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7136061560686651593568427 10704092341029977390352641)
            ·
              refine ⟨8028069255772483042764481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10704092341029977390352641 8028069255772483042764481)
              ·
                refine ⟨6021051941829362282073361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8028069255772483042764481 6021051941829362282073361)
                ·
                  refine ⟨4515788956372021711555021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021051941829362282073361 4515788956372021711555021)
                  ·
                    refine ⟨1693420858639508141833133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4515788956372021711555021 1693420858639508141833133)
                    ·
                      refine ⟨635032821989815553187425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693420858639508141833133 635032821989815553187425)
                      ·
                        rfl

theorem cell23_1236722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1236722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236722 prefixEnd_1236722 := by exact prefixLift 1236722
  have htrace : WordTrace (prefixWord ++ tailWord_1236722) baseStart_1236722 baseEnd_1236722 := by
    simpa [prefixWord, tailWord_1236722, baseEnd_1236722] using wordTrace_append hprefix tailTrace_1236722
  have hstable : (prefixWord ++ tailWord_1236722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236722).length < 2 ^ (prefixWord ++ tailWord_1236722).sum := by decide
  have hdescent : baseEnd_1236722 < baseStart_1236722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236732 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_1236732 : Nat := 118140960795 + 1236732 * 2 ^ 59
def prefixEnd_1236732 : Nat := 4983230072969 + 3 ^ 40 * 1236732 * 2
def baseEnd_1236732 : Nat := 635037956796360514062379

theorem tailTrace_1236732 : CollatzResearch.WordTrace tailWord_1236732 prefixEnd_1236732 635037956796360514062379 := by
  unfold tailWord_1236732
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553660877769327927432225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30071547837025770569909633 22553660877769327927432225)
  ·
    refine ⟨16915245658326995945574169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22553660877769327927432225 16915245658326995945574169)
    ·
      refine ⟨12686434243745246959180627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16915245658326995945574169 12686434243745246959180627)
      ·
        refine ⟨19029651365617870438770941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12686434243745246959180627 19029651365617870438770941)
        ·
          refine ⟨7136119262106701414539103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19029651365617870438770941 7136119262106701414539103)
          ·
            refine ⟨10704178893160052121808655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7136119262106701414539103 10704178893160052121808655)
            ·
              refine ⟨16056268339740078182712983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10704178893160052121808655 16056268339740078182712983)
              ·
                refine ⟨24084402509610117274069475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16056268339740078182712983 24084402509610117274069475)
                ·
                  refine ⟨36126603764415175911104213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24084402509610117274069475 36126603764415175911104213)
                  ·
                    refine ⟨846717275728480685416505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36126603764415175911104213 846717275728480685416505)
                    ·
                      refine ⟨635037956796360514062379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846717275728480685416505 635037956796360514062379)
                      ·
                        rfl

theorem cell23_1236732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_1236732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236732 prefixEnd_1236732 := by exact prefixLift 1236732
  have htrace : WordTrace (prefixWord ++ tailWord_1236732) baseStart_1236732 baseEnd_1236732 := by
    simpa [prefixWord, tailWord_1236732, baseEnd_1236732] using wordTrace_append hprefix tailTrace_1236732
  have hstable : (prefixWord ++ tailWord_1236732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236732).length < 2 ^ (prefixWord ++ tailWord_1236732).sum := by decide
  have hdescent : baseEnd_1236732 < baseStart_1236732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236735 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_1236735 : Nat := 118140960795 + 1236735 * 2 ^ 59
def prefixEnd_1236735 : Nat := 4983230072969 + 3 ^ 40 * 1236735 * 2
def baseEnd_1236735 : Nat := 635039497238324002324865

theorem tailTrace_1236735 : CollatzResearch.WordTrace tailWord_1236735 prefixEnd_1236735 635039497238324002324865 := by
  unfold tailWord_1236735
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107431174527787367223659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30071620783018524911482439 45107431174527787367223659)
  ·
    refine ⟨67661146761791681050835489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45107431174527787367223659 67661146761791681050835489)
    ·
      refine ⟨50745860071343760788126617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67661146761791681050835489 50745860071343760788126617)
      ·
        refine ⟨38059395053507820591094963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50745860071343760788126617 38059395053507820591094963)
        ·
          refine ⟨57089092580261730886642445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38059395053507820591094963 57089092580261730886642445)
          ·
            refine ⟨21408409717598149082490917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57089092580261730886642445 21408409717598149082490917)
            ·
              refine ⟨4014076822049652952967047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21408409717598149082490917 4014076822049652952967047)
              ·
                refine ⟨6021115233074479429450571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014076822049652952967047 6021115233074479429450571)
                ·
                  refine ⟨9031672849611719144175857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021115233074479429450571 9031672849611719144175857)
                  ·
                    refine ⟨6773754637208789358131893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9031672849611719144175857 6773754637208789358131893)
                    ·
                      refine ⟨635039497238324002324865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6773754637208789358131893 635039497238324002324865)
                      ·
                        rfl

theorem cell23_1236735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_1236735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236735 prefixEnd_1236735 := by exact prefixLift 1236735
  have htrace : WordTrace (prefixWord ++ tailWord_1236735) baseStart_1236735 baseEnd_1236735 := by
    simpa [prefixWord, tailWord_1236735, baseEnd_1236735] using wordTrace_append hprefix tailTrace_1236735
  have hstable : (prefixWord ++ tailWord_1236735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236735).length < 2 ^ (prefixWord ++ tailWord_1236735).sum := by decide
  have hdescent : baseEnd_1236735 < baseStart_1236735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236745 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_1236745 : Nat := 118140960795 + 1236745 * 2 ^ 59
def prefixEnd_1236745 : Nat := 4983230072969 + 3 ^ 40 * 1236745 * 2
def baseEnd_1236745 : Nat := 635044632044868963199819

theorem tailTrace_1236745 : CollatzResearch.WordTrace tailWord_1236745 prefixEnd_1236745 635044632044868963199819 := by
  unfold tailWord_1236745
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107795904491559075087689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30071863936327706050058459 45107795904491559075087689)
  ·
    refine ⟨33830846928368669306315767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45107795904491559075087689 33830846928368669306315767)
    ·
      refine ⟨50746270392553003959473651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33830846928368669306315767 50746270392553003959473651)
      ·
        refine ⟨76119405588829505939210477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50746270392553003959473651 76119405588829505939210477)
        ·
          refine ⟨28544777095811064727203929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76119405588829505939210477 28544777095811064727203929)
          ·
            refine ⟨21408582821858298545402947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28544777095811064727203929 21408582821858298545402947)
            ·
              refine ⟨32112874232787447818104421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21408582821858298545402947 32112874232787447818104421)
              ·
                refine ⟨6021163918647646465894579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32112874232787447818104421 6021163918647646465894579)
                ·
                  refine ⟨9031745877971469698841869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021163918647646465894579 9031745877971469698841869)
                  ·
                    refine ⟨3386904704239301137065701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9031745877971469698841869 3386904704239301137065701)
                    ·
                      refine ⟨635044632044868963199819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3386904704239301137065701 635044632044868963199819)
                      ·
                        rfl

theorem cell23_1236745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_1236745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236745 prefixEnd_1236745 := by exact prefixLift 1236745
  have htrace : WordTrace (prefixWord ++ tailWord_1236745) baseStart_1236745 baseEnd_1236745 := by
    simpa [prefixWord, tailWord_1236745, baseEnd_1236745] using wordTrace_append hprefix tailTrace_1236745
  have hstable : (prefixWord ++ tailWord_1236745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236745).length < 2 ^ (prefixWord ++ tailWord_1236745).sum := by decide
  have hdescent : baseEnd_1236745 < baseStart_1236745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236759 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 2, 5]
def baseStart_1236759 : Nat := 118140960795 + 1236759 * 2 ^ 59
def prefixEnd_1236759 : Nat := 4983230072969 + 3 ^ 40 * 1236759 * 2
def baseEnd_1236759 : Nat := 211683940258010636141585

theorem tailTrace_1236759 : CollatzResearch.WordTrace tailWord_1236759 prefixEnd_1236759 211683940258010636141585 := by
  unfold tailWord_1236759
  simp only [CollatzResearch.WordTrace]
  refine ⟨45108306526440839466097331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30072204350960559644064887 45108306526440839466097331)
  ·
    refine ⟨67662459789661259199145997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45108306526440839466097331 67662459789661259199145997)
    ·
      refine ⟨25373422421122972199679749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67662459789661259199145997 25373422421122972199679749)
      ·
        refine ⟨4757516703960557287439953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25373422421122972199679749 4757516703960557287439953)
        ·
          refine ⟨3568137527970417965579965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757516703960557287439953 3568137527970417965579965)
          ·
            refine ⟨1338051572988906737092487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3568137527970417965579965 1338051572988906737092487)
            ·
              refine ⟨2007077359483360105638731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338051572988906737092487 2007077359483360105638731)
              ·
                refine ⟨3010616039225040158458097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007077359483360105638731 3010616039225040158458097)
                ·
                  refine ⟨2257962029418780118843573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3010616039225040158458097 2257962029418780118843573)
                  ·
                    refine ⟨211683940258010636141585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2257962029418780118843573 211683940258010636141585)
                    ·
                      rfl

theorem cell23_1236759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_1236759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236759 prefixEnd_1236759 := by exact prefixLift 1236759
  have htrace : WordTrace (prefixWord ++ tailWord_1236759) baseStart_1236759 baseEnd_1236759 := by
    simpa [prefixWord, tailWord_1236759, baseEnd_1236759] using wordTrace_append hprefix tailTrace_1236759
  have hstable : (prefixWord ++ tailWord_1236759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236759).length < 2 ^ (prefixWord ++ tailWord_1236759).sum := by decide
  have hdescent : baseEnd_1236759 < baseStart_1236759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236762 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1236762 : Nat := 118140960795 + 1236762 * 2 ^ 59
def prefixEnd_1236762 : Nat := 4983230072969 + 3 ^ 40 * 1236762 * 2
def baseEnd_1236762 : Nat := 635053361215995396687241

theorem tailTrace_1236762 : CollatzResearch.WordTrace tailWord_1236762 prefixEnd_1236762 635053361215995396687241 := by
  unfold tailWord_1236762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277103986357492744614135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30072277296953313985637693 11277103986357492744614135)
  ·
    refine ⟨16915655979536239116921203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11277103986357492744614135 16915655979536239116921203)
    ·
      refine ⟨25373483969304358675381805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915655979536239116921203 25373483969304358675381805)
      ·
        refine ⟨9515056488489134503268177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25373483969304358675381805 9515056488489134503268177)
        ·
          refine ⟨7136292366366850877451133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9515056488489134503268177 7136292366366850877451133)
          ·
            refine ⟨2676109637387569079044175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7136292366366850877451133 2676109637387569079044175)
            ·
              refine ⟨4014164456081353618566263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676109637387569079044175 4014164456081353618566263)
              ·
                refine ⟨6021246684122030427849395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014164456081353618566263 6021246684122030427849395)
                ·
                  refine ⟨9031870026183045641774093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021246684122030427849395 9031870026183045641774093)
                  ·
                    refine ⟨3386951259818642115665285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9031870026183045641774093 3386951259818642115665285)
                    ·
                      refine ⟨635053361215995396687241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3386951259818642115665285 635053361215995396687241)
                      ·
                        rfl

theorem cell23_1236762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1236762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236762 prefixEnd_1236762 := by exact prefixLift 1236762
  have htrace : WordTrace (prefixWord ++ tailWord_1236762) baseStart_1236762 baseEnd_1236762 := by
    simpa [prefixWord, tailWord_1236762, baseEnd_1236762] using wordTrace_append hprefix tailTrace_1236762
  have hstable : (prefixWord ++ tailWord_1236762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236762).length < 2 ^ (prefixWord ++ tailWord_1236762).sum := by decide
  have hdescent : baseEnd_1236762 < baseStart_1236762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236805 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_1236805 : Nat := 118140960795 + 1236805 * 2 ^ 59
def prefixEnd_1236805 : Nat := 4983230072969 + 3 ^ 40 * 1236805 * 2
def baseEnd_1236805 : Nat := 635075440884138728449543

theorem tailTrace_1236805 : CollatzResearch.WordTrace tailWord_1236805 prefixEnd_1236805 635075440884138728449543 := by
  unfold tailWord_1236805
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109984284274189322271869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30073322856182792881514579 45109984284274189322271869)
  ·
    refine ⟨16916244106602820995851951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45109984284274189322271869 16916244106602820995851951)
    ·
      refine ⟨25374366159904231493777927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16916244106602820995851951 25374366159904231493777927)
      ·
        refine ⟨38061549239856347240666891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25374366159904231493777927 38061549239856347240666891)
        ·
          refine ⟨57092323859784520861000337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38061549239856347240666891 57092323859784520861000337)
          ·
            refine ⟨42819242894838390645750253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57092323859784520861000337 42819242894838390645750253)
            ·
              refine ⟨16057216085564396492156345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42819242894838390645750253 16057216085564396492156345)
              ·
                refine ⟨12042912064173297369117259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16057216085564396492156345 12042912064173297369117259)
                ·
                  refine ⟨18064368096259946053675889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12042912064173297369117259 18064368096259946053675889)
                  ·
                    refine ⟨13548276072194959540256917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18064368096259946053675889 13548276072194959540256917)
                    ·
                      refine ⟨635075440884138728449543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13548276072194959540256917 635075440884138728449543)
                      ·
                        rfl

theorem cell23_1236805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_1236805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236805 prefixEnd_1236805 := by exact prefixLift 1236805
  have htrace : WordTrace (prefixWord ++ tailWord_1236805) baseStart_1236805 baseEnd_1236805 := by
    simpa [prefixWord, tailWord_1236805, baseEnd_1236805] using wordTrace_append hprefix tailTrace_1236805
  have hstable : (prefixWord ++ tailWord_1236805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236805).length < 2 ^ (prefixWord ++ tailWord_1236805).sum := by decide
  have hdescent : baseEnd_1236805 < baseStart_1236805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236823 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 1, 4]
def baseStart_1236823 : Nat := 118140960795 + 1236823 * 2 ^ 59
def prefixEnd_1236823 : Nat := 4983230072969 + 3 ^ 40 * 1236823 * 2
def baseEnd_1236823 : Nat := 211694894511973219341487

theorem tailTrace_1236823 : CollatzResearch.WordTrace tailWord_1236823 prefixEnd_1236823 211694894511973219341487 := by
  unfold tailWord_1236823
  simp only [CollatzResearch.WordTrace]
  refine ⟨45110640798208978396427123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30073760532139318930951415 45110640798208978396427123)
  ·
    refine ⟨67665961197313467594640685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45110640798208978396427123 67665961197313467594640685)
    ·
      refine ⟨25374735448992550347990257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67665961197313467594640685 25374735448992550347990257)
      ·
        refine ⟨19031051586744412760992693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25374735448992550347990257 19031051586744412760992693)
        ·
          refine ⟨1784161086257288696343065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19031051586744412760992693 1784161086257288696343065)
          ·
            refine ⟨1338120814692966522257299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784161086257288696343065 1338120814692966522257299)
            ·
              refine ⟨2007181222039449783385949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338120814692966522257299 2007181222039449783385949)
              ·
                refine ⟨752692958264793668769731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2007181222039449783385949 752692958264793668769731)
                ·
                  refine ⟨1129039437397190503154597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752692958264793668769731 1129039437397190503154597)
                  ·
                    refine ⟨211694894511973219341487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129039437397190503154597 211694894511973219341487)
                    ·
                      rfl

theorem cell23_1236823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_1236823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236823 prefixEnd_1236823 := by exact prefixLift 1236823
  have htrace : WordTrace (prefixWord ++ tailWord_1236823) baseStart_1236823 baseEnd_1236823 := by
    simpa [prefixWord, tailWord_1236823, baseEnd_1236823] using wordTrace_append hprefix tailTrace_1236823
  have hstable : (prefixWord ++ tailWord_1236823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236823).length < 2 ^ (prefixWord ++ tailWord_1236823).sum := by decide
  have hdescent : baseEnd_1236823 < baseStart_1236823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236889 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_1236889 : Nat := 118140960795 + 1236889 * 2 ^ 59
def prefixEnd_1236889 : Nat := 4983230072969 + 3 ^ 40 * 1236889 * 2
def baseEnd_1236889 : Nat := 635118573259116399799157

theorem tailTrace_1236889 : CollatzResearch.WordTrace tailWord_1236889 prefixEnd_1236889 635118573259116399799157 := by
  unfold tailWord_1236889
  simp only [CollatzResearch.WordTrace]
  refine ⟨45113048015969871668329721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30075365343979914445553147 45113048015969871668329721)
  ·
    refine ⟨33834786011977403751247291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45113048015969871668329721 33834786011977403751247291)
    ·
      refine ⟨50752179017966105626870937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33834786011977403751247291 50752179017966105626870937)
      ·
        refine ⟨38064134263474579220153203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50752179017966105626870937 38064134263474579220153203)
        ·
          refine ⟨57096201395211868830229805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38064134263474579220153203 57096201395211868830229805)
          ·
            refine ⟨21411075523204450811336177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57096201395211868830229805 21411075523204450811336177)
            ·
              refine ⟨16058306642403338108502133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21411075523204450811336177 16058306642403338108502133)
              ·
                refine ⟨1505466247725312947672075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16058306642403338108502133 1505466247725312947672075)
                ·
                  refine ⟨2258199371587969421508113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505466247725312947672075 2258199371587969421508113)
                  ·
                    refine ⟨1693649528690977066131085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2258199371587969421508113 1693649528690977066131085)
                    ·
                      refine ⟨635118573259116399799157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693649528690977066131085 635118573259116399799157)
                      ·
                        rfl

theorem cell23_1236889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_1236889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236889 prefixEnd_1236889 := by exact prefixLift 1236889
  have htrace : WordTrace (prefixWord ++ tailWord_1236889) baseStart_1236889 baseEnd_1236889 := by
    simpa [prefixWord, tailWord_1236889, baseEnd_1236889] using wordTrace_append hprefix tailTrace_1236889
  have hstable : (prefixWord ++ tailWord_1236889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236889).length < 2 ^ (prefixWord ++ tailWord_1236889).sum := by decide
  have hdescent : baseEnd_1236889 < baseStart_1236889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236892 : List Nat := [2, 2, 3, 3, 1, 12]
def baseStart_1236892 : Nat := 118140960795 + 1236892 * 2 ^ 59
def prefixEnd_1236892 : Nat := 4983230072969 + 3 ^ 40 * 1236892 * 2
def baseEnd_1236892 : Nat := 2613663019346007769801

theorem tailTrace_1236892 : CollatzResearch.WordTrace tailWord_1236892 prefixEnd_1236892 2613663019346007769801 := by
  unfold tailWord_1236892
  simp only [CollatzResearch.WordTrace]
  refine ⟨22556578717479501590344465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30075438289972668787125953 22556578717479501590344465)
  ·
    refine ⟨16917434038109626192758349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22556578717479501590344465 16917434038109626192758349)
    ·
      refine ⟨6344037764291109822284381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16917434038109626192758349 6344037764291109822284381)
      ·
        refine ⟨2379014161609166183356643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6344037764291109822284381 2379014161609166183356643)
        ·
          refine ⟨3568521242413749275034965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379014161609166183356643 3568521242413749275034965)
          ·
            refine ⟨2613663019346007769801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3568521242413749275034965 2613663019346007769801)
            ·
              rfl

theorem cell23_1236892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 12].length) (baseStart_1236892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236892 prefixEnd_1236892 := by exact prefixLift 1236892
  have htrace : WordTrace (prefixWord ++ tailWord_1236892) baseStart_1236892 baseEnd_1236892 := by
    simpa [prefixWord, tailWord_1236892, baseEnd_1236892] using wordTrace_append hprefix tailTrace_1236892
  have hstable : (prefixWord ++ tailWord_1236892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236892).length < 2 ^ (prefixWord ++ tailWord_1236892).sum := by decide
  have hdescent : baseEnd_1236892 < baseStart_1236892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236897 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1236897 : Nat := 118140960795 + 1236897 * 2 ^ 59
def prefixEnd_1236897 : Nat := 4983230072969 + 3 ^ 40 * 1236897 * 2
def baseEnd_1236897 : Nat := 635122681104352368499121

theorem tailTrace_1236897 : CollatzResearch.WordTrace tailWord_1236897 prefixEnd_1236897 635122681104352368499121 := by
  unfold tailWord_1236897
  simp only [CollatzResearch.WordTrace]
  refine ⟨45113339799940889034620945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30075559866627259356413963 45113339799940889034620945)
  ·
    refine ⟨33835004849955666775965709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45113339799940889034620945 33835004849955666775965709)
    ·
      refine ⟨12688126818733375040987141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33835004849955666775965709 12688126818733375040987141)
      ·
        refine ⟨2379023778512507820185089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12688126818733375040987141 2379023778512507820185089)
        ·
          refine ⟨1784267833884380865138817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2379023778512507820185089 1784267833884380865138817)
          ·
            refine ⟨1338200875413285648854113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784267833884380865138817 1338200875413285648854113)
            ·
              refine ⟨1003650656559964236640585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338200875413285648854113 1003650656559964236640585)
              ·
                refine ⟨752737992419973177480439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003650656559964236640585 752737992419973177480439)
                ·
                  refine ⟨1129106988629959766220659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752737992419973177480439 1129106988629959766220659)
                  ·
                    refine ⟨1693660482944939649330989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129106988629959766220659 1693660482944939649330989)
                    ·
                      refine ⟨635122681104352368499121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693660482944939649330989 635122681104352368499121)
                      ·
                        rfl

theorem cell23_1236897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1236897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236897 prefixEnd_1236897 := by exact prefixLift 1236897
  have htrace : WordTrace (prefixWord ++ tailWord_1236897) baseStart_1236897 baseEnd_1236897 := by
    simpa [prefixWord, tailWord_1236897, baseEnd_1236897] using wordTrace_append hprefix tailTrace_1236897
  have hstable : (prefixWord ++ tailWord_1236897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236897).length < 2 ^ (prefixWord ++ tailWord_1236897).sum := by decide
  have hdescent : baseEnd_1236897 < baseStart_1236897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236919 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_1236919 : Nat := 118140960795 + 1236919 * 2 ^ 59
def prefixEnd_1236919 : Nat := 4983230072969 + 3 ^ 40 * 1236919 * 2
def baseEnd_1236919 : Nat := 635133977678751282424019

theorem tailTrace_1236919 : CollatzResearch.WordTrace tailWord_1236919 prefixEnd_1236919 635133977678751282424019 := by
  unfold tailWord_1236919
  simp only [CollatzResearch.WordTrace]
  refine ⟨45114142205861186791921811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30076094803907457861281207 45114142205861186791921811)
  ·
    refine ⟨67671213308791780187882717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45114142205861186791921811 67671213308791780187882717)
    ·
      refine ⟨25376704990796917570456019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67671213308791780187882717 25376704990796917570456019)
      ·
        refine ⟨38065057486195376355684029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25376704990796917570456019 38065057486195376355684029)
        ·
          refine ⟨14274396557323266133381511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38065057486195376355684029 14274396557323266133381511)
          ·
            refine ⟨21411594835984899200072267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274396557323266133381511 21411594835984899200072267)
            ·
              refine ⟨32117392253977348800108401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21411594835984899200072267 32117392253977348800108401)
              ·
                refine ⟨24088044190483011600081301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32117392253977348800108401 24088044190483011600081301)
                ·
                  refine ⟨1129127071428891168753811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24088044190483011600081301 1129127071428891168753811)
                  ·
                    refine ⟨1693690607143336753130717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129127071428891168753811 1693690607143336753130717)
                    ·
                      refine ⟨635133977678751282424019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693690607143336753130717 635133977678751282424019)
                      ·
                        rfl

theorem cell23_1236919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_1236919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236919 prefixEnd_1236919 := by exact prefixLift 1236919
  have htrace : WordTrace (prefixWord ++ tailWord_1236919) baseStart_1236919 baseEnd_1236919 := by
    simpa [prefixWord, tailWord_1236919, baseEnd_1236919] using wordTrace_append hprefix tailTrace_1236919
  have hstable : (prefixWord ++ tailWord_1236919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236919).length < 2 ^ (prefixWord ++ tailWord_1236919).sum := by decide
  have hdescent : baseEnd_1236919 < baseStart_1236919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236952 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1236952 : Nat := 118140960795 + 1236952 * 2 ^ 59
def prefixEnd_1236952 : Nat := 4983230072969 + 3 ^ 40 * 1236952 * 2
def baseEnd_1236952 : Nat := 211716974180116551103789

theorem tailTrace_1236952 : CollatzResearch.WordTrace tailWord_1236952 prefixEnd_1236952 211716974180116551103789 := by
  unfold tailWord_1236952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22557672907370816713936555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30076897209827755618582073 22557672907370816713936555)
  ·
    refine ⟨33836509361056225070904833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22557672907370816713936555 33836509361056225070904833)
    ·
      refine ⟨25377382020792168803178625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33836509361056225070904833 25377382020792168803178625)
      ·
        refine ⟨19033036515594126602383969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25377382020792168803178625 19033036515594126602383969)
        ·
          refine ⟨14274777386695594951787977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19033036515594126602383969 14274777386695594951787977)
          ·
            refine ⟨10706083040021696213840983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14274777386695594951787977 10706083040021696213840983)
            ·
              refine ⟨16059124560032544320761475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10706083040021696213840983 16059124560032544320761475)
              ·
                refine ⟨24088686840048816481142213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16059124560032544320761475 24088686840048816481142213)
                ·
                  refine ⟨4516628782509153090214165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24088686840048816481142213 4516628782509153090214165)
                  ·
                    refine ⟨211716974180116551103789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4516628782509153090214165 211716974180116551103789)
                    ·
                      rfl

theorem cell23_1236952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1236952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236952 prefixEnd_1236952 := by exact prefixLift 1236952
  have htrace : WordTrace (prefixWord ++ tailWord_1236952) baseStart_1236952 baseEnd_1236952 := by
    simpa [prefixWord, tailWord_1236952, baseEnd_1236952] using wordTrace_append hprefix tailTrace_1236952
  have hstable : (prefixWord ++ tailWord_1236952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236952).length < 2 ^ (prefixWord ++ tailWord_1236952).sum := by decide
  have hdescent : baseEnd_1236952 < baseStart_1236952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236976 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2]
def baseStart_1236976 : Nat := 118140960795 + 1236976 * 2 ^ 59
def prefixEnd_1236976 : Nat := 4983230072969 + 3 ^ 40 * 1236976 * 2
def baseEnd_1236976 : Nat := 635163246076057559411257

theorem tailTrace_1236976 : CollatzResearch.WordTrace tailWord_1236976 prefixEnd_1236976 635163246076057559411257 := by
  unfold tailWord_1236976
  simp only [CollatzResearch.WordTrace]
  refine ⟨22558110583327342763373391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30077480777769790351164521 22558110583327342763373391)
  ·
    refine ⟨33837165874991014145060087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22558110583327342763373391 33837165874991014145060087)
    ·
      refine ⟨50755748812486521217590131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33837165874991014145060087 50755748812486521217590131)
      ·
        refine ⟨76133623218729781826385197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50755748812486521217590131 76133623218729781826385197)
        ·
          refine ⟨28550108707023668184894449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76133623218729781826385197 28550108707023668184894449)
          ·
            refine ⟨21412581530267751138670837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28550108707023668184894449 21412581530267751138670837)
            ·
              refine ⟨2007429518462601669250391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21412581530267751138670837 2007429518462601669250391)
              ·
                refine ⟨3011144277693902503875587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007429518462601669250391 3011144277693902503875587)
                ·
                  refine ⟨4516716416540853755813381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011144277693902503875587 4516716416540853755813381)
                  ·
                    refine ⟨846884328101410079215009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516716416540853755813381 846884328101410079215009)
                    ·
                      refine ⟨635163246076057559411257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846884328101410079215009 635163246076057559411257)
                      ·
                        rfl

theorem cell23_1236976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 4, 2].length) (baseStart_1236976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1236976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1236976 prefixEnd_1236976 := by exact prefixLift 1236976
  have htrace : WordTrace (prefixWord ++ tailWord_1236976) baseStart_1236976 baseEnd_1236976 := by
    simpa [prefixWord, tailWord_1236976, baseEnd_1236976] using wordTrace_append hprefix tailTrace_1236976
  have hstable : (prefixWord ++ tailWord_1236976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236976).length < 2 ^ (prefixWord ++ tailWord_1236976).sum := by decide
  have hdescent : baseEnd_1236976 < baseStart_1236976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237059 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 7, 4]
def baseStart_1237059 : Nat := 118140960795 + 1237059 * 2 ^ 59
def prefixEnd_1237059 : Nat := 4983230072969 + 3 ^ 40 * 1237059 * 2
def baseEnd_1237059 : Nat := 211735288323460244891125

theorem tailTrace_1237059 : CollatzResearch.WordTrace tailWord_1237059 prefixEnd_1237059 211735288323460244891125 := by
  unfold tailWord_1237059
  simp only [CollatzResearch.WordTrace]
  refine ⟨45119248425353990702018231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30079498950235993801345487 45119248425353990702018231)
  ·
    refine ⟨67678872638030986053027347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45119248425353990702018231 67678872638030986053027347)
    ·
      refine ⟨101518308957046479079541021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67678872638030986053027347 101518308957046479079541021)
      ·
        refine ⟨38069365858892429654827883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101518308957046479079541021 38069365858892429654827883)
        ·
          refine ⟨57104048788338644482241825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38069365858892429654827883 57104048788338644482241825)
          ·
            refine ⟨42828036591253983361681369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57104048788338644482241825 42828036591253983361681369)
            ·
              refine ⟨32121027443440487521261027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42828036591253983361681369 32121027443440487521261027)
              ·
                refine ⟨48181541165160731281891541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32121027443440487521261027 48181541165160731281891541)
                ·
                  refine ⟨1129254871058454639419333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48181541165160731281891541 1129254871058454639419333)
                  ·
                    refine ⟨211735288323460244891125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129254871058454639419333 211735288323460244891125)
                    ·
                      rfl

theorem cell23_1237059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 4].length) (baseStart_1237059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237059 prefixEnd_1237059 := by exact prefixLift 1237059
  have htrace : WordTrace (prefixWord ++ tailWord_1237059) baseStart_1237059 baseEnd_1237059 := by
    simpa [prefixWord, tailWord_1237059, baseEnd_1237059] using wordTrace_append hprefix tailTrace_1237059
  have hstable : (prefixWord ++ tailWord_1237059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237059).length < 2 ^ (prefixWord ++ tailWord_1237059).sum := by decide
  have hdescent : baseEnd_1237059 < baseStart_1237059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237066 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_1237066 : Nat := 118140960795 + 1237066 * 2 ^ 59
def prefixEnd_1237066 : Nat := 4983230072969 + 3 ^ 40 * 1237066 * 2
def baseEnd_1237066 : Nat := 635209459334962207285843

theorem tailTrace_1237066 : CollatzResearch.WordTrace tailWord_1237066 prefixEnd_1237066 635209459334962207285843 := by
  unfold tailWord_1237066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11279875934082157724380763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30079669157552420598348701 11279875934082157724380763)
  ·
    refine ⟨16919813901123236586571145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11279875934082157724380763 16919813901123236586571145)
    ·
      refine ⟨12689860425842427439928359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16919813901123236586571145 12689860425842427439928359)
      ·
        refine ⟨19034790638763641159892539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12689860425842427439928359 19034790638763641159892539)
        ·
          refine ⟨28552185958145461739838809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19034790638763641159892539 28552185958145461739838809)
          ·
            refine ⟨21414139468609096304879107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28552185958145461739838809 21414139468609096304879107)
            ·
              refine ⟨32121209202913644457318661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21414139468609096304879107 32121209202913644457318661)
              ·
                refine ⟨6022726725546308335747249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32121209202913644457318661 6022726725546308335747249)
                ·
                  refine ⟨4517045044159731251810437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6022726725546308335747249 4517045044159731251810437)
                  ·
                    refine ⟨846945945779949609714457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517045044159731251810437 846945945779949609714457)
                    ·
                      refine ⟨635209459334962207285843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 846945945779949609714457 635209459334962207285843)
                      ·
                        rfl

theorem cell23_1237066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_1237066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237066 prefixEnd_1237066 := by exact prefixLift 1237066
  have htrace : WordTrace (prefixWord ++ tailWord_1237066) baseStart_1237066 baseEnd_1237066 := by
    simpa [prefixWord, tailWord_1237066, baseEnd_1237066] using wordTrace_append hprefix tailTrace_1237066
  have hstable : (prefixWord ++ tailWord_1237066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237066).length < 2 ^ (prefixWord ++ tailWord_1237066).sum := by decide
  have hdescent : baseEnd_1237066 < baseStart_1237066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237076 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1237076 : Nat := 118140960795 + 1237076 * 2 ^ 59
def prefixEnd_1237076 : Nat := 4983230072969 + 3 ^ 40 * 1237076 * 2
def baseEnd_1237076 : Nat := 211738198047169056053599

theorem tailTrace_1237076 : CollatzResearch.WordTrace tailWord_1237076 prefixEnd_1237076 211738198047169056053599 := by
  unfold tailWord_1237076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559934233146201302693541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30079912310861601736924721 22559934233146201302693541)
  ·
    refine ⟨4229987668714912744255039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22559934233146201302693541 4229987668714912744255039)
    ·
      refine ⟨6344981503072369116382559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4229987668714912744255039 6344981503072369116382559)
      ·
        refine ⟨9517472254608553674573839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6344981503072369116382559 9517472254608553674573839)
        ·
          refine ⟨14276208381912830511860759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9517472254608553674573839 14276208381912830511860759)
          ·
            refine ⟨21414312572869245767791139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14276208381912830511860759 21414312572869245767791139)
            ·
              refine ⟨32121468859303868651686709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21414312572869245767791139 32121468859303868651686709)
              ·
                refine ⟨3011387705559737686095629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32121468859303868651686709 3011387705559737686095629)
                ·
                  refine ⟨1129270389584901632285861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3011387705559737686095629 1129270389584901632285861)
                  ·
                    refine ⟨211738198047169056053599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129270389584901632285861 211738198047169056053599)
                    ·
                      rfl

theorem cell23_1237076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1237076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237076 prefixEnd_1237076 := by exact prefixLift 1237076
  have htrace : WordTrace (prefixWord ++ tailWord_1237076) baseStart_1237076 baseEnd_1237076 := by
    simpa [prefixWord, tailWord_1237076, baseEnd_1237076] using wordTrace_append hprefix tailTrace_1237076
  have hstable : (prefixWord ++ tailWord_1237076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237076).length < 2 ^ (prefixWord ++ tailWord_1237076).sum := by decide
  have hdescent : baseEnd_1237076 < baseStart_1237076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237103 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_1237103 : Nat := 118140960795 + 1237103 * 2 ^ 59
def prefixEnd_1237103 : Nat := 4983230072969 + 3 ^ 40 * 1237103 * 2
def baseEnd_1237103 : Nat := 635228458119178562523173

theorem tailTrace_1237103 : CollatzResearch.WordTrace tailWord_1237103 prefixEnd_1237103 635228458119178562523173 := by
  unfold tailWord_1237103
  simp only [CollatzResearch.WordTrace]
  refine ⟨45120853237194586216619963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30080568824796390811079975 45120853237194586216619963)
  ·
    refine ⟨67681279855791879324929945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45120853237194586216619963 67681279855791879324929945)
    ·
      refine ⟨50760959891843909493697459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67681279855791879324929945 50760959891843909493697459)
      ·
        refine ⟨76141439837765864240546189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50760959891843909493697459 76141439837765864240546189)
        ·
          refine ⟨28553039939162199090204821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76141439837765864240546189 28553039939162199090204821)
          ·
            refine ⟨1338423747148228082353351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28553039939162199090204821 1338423747148228082353351)
            ·
              refine ⟨2007635620722342123530027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338423747148228082353351 2007635620722342123530027)
              ·
                refine ⟨3011453431083513185295041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007635620722342123530027 3011453431083513185295041)
                ·
                  refine ⟨2258590073312634888971281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3011453431083513185295041 2258590073312634888971281)
                  ·
                    refine ⟨1693942554984476166728461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2258590073312634888971281 1693942554984476166728461)
                    ·
                      refine ⟨635228458119178562523173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1693942554984476166728461 635228458119178562523173)
                      ·
                        rfl

theorem cell23_1237103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_1237103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237103 prefixEnd_1237103 := by exact prefixLift 1237103
  have htrace : WordTrace (prefixWord ++ tailWord_1237103) baseStart_1237103 baseEnd_1237103 := by
    simpa [prefixWord, tailWord_1237103, baseEnd_1237103] using wordTrace_append hprefix tailTrace_1237103
  have hstable : (prefixWord ++ tailWord_1237103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237103).length < 2 ^ (prefixWord ++ tailWord_1237103).sum := by decide
  have hdescent : baseEnd_1237103 < baseStart_1237103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237110 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1237110 : Nat := 118140960795 + 1237110 * 2 ^ 59
def prefixEnd_1237110 : Nat := 4983230072969 + 3 ^ 40 * 1237110 * 2
def baseEnd_1237110 : Nat := 211744017494586678378547

theorem tailTrace_1237110 : CollatzResearch.WordTrace tailWord_1237110 prefixEnd_1237110 211744017494586678378547 := by
  unfold tailWord_1237110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820069284260576650757799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30080739032112817608083189 2820069284260576650757799)
  ·
    refine ⟨4230103926390864976136699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820069284260576650757799 4230103926390864976136699)
    ·
      refine ⟨6345155889586297464205049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230103926390864976136699 6345155889586297464205049)
      ·
        refine ⟨4758866917189723098153787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6345155889586297464205049 4758866917189723098153787)
        ·
          refine ⟨7138300375784584647230681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758866917189723098153787 7138300375784584647230681)
          ·
            refine ⟨5353725281838438485423011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7138300375784584647230681 5353725281838438485423011)
            ·
              refine ⟨8030587922757657728134517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5353725281838438485423011 8030587922757657728134517)
              ·
                refine ⟨752867617758530412012611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8030587922757657728134517 752867617758530412012611)
                ·
                  refine ⟨1129301426637795618018917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752867617758530412012611 1129301426637795618018917)
                  ·
                    refine ⟨211744017494586678378547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129301426637795618018917 211744017494586678378547)
                    ·
                      rfl

theorem cell23_1237110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1237110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237110 prefixEnd_1237110 := by exact prefixLift 1237110
  have htrace : WordTrace (prefixWord ++ tailWord_1237110) baseStart_1237110 baseEnd_1237110 := by
    simpa [prefixWord, tailWord_1237110, baseEnd_1237110] using wordTrace_append hprefix tailTrace_1237110
  have hstable : (prefixWord ++ tailWord_1237110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237110).length < 2 ^ (prefixWord ++ tailWord_1237110).sum := by decide
  have hdescent : baseEnd_1237110 < baseStart_1237110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237153 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1237153 : Nat := 118140960795 + 1237153 * 2 ^ 59
def prefixEnd_1237153 : Nat := 4983230072969 + 3 ^ 40 * 1237153 * 2
def baseEnd_1237153 : Nat := 211751377383967788965981

theorem tailTrace_1237153 : CollatzResearch.WordTrace tailWord_1237153 prefixEnd_1237153 211751377383967788965981 := by
  unfold tailWord_1237153
  simp only [CollatzResearch.WordTrace]
  refine ⟨45122676887013444755940113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30081784591342296503960075 45122676887013444755940113)
  ·
    refine ⟨33842007665260083566955085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45122676887013444755940113 33842007665260083566955085)
    ·
      refine ⟨12690752874472531337608157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33842007665260083566955085 12690752874472531337608157)
      ·
        refine ⟨4759032327927199251603059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12690752874472531337608157 4759032327927199251603059)
        ·
          refine ⟨7138548491890798877404589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759032327927199251603059 7138548491890798877404589)
          ·
            refine ⟨2676955684459049579026721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7138548491890798877404589 2676955684459049579026721)
            ·
              refine ⟨2007716763344287184270041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2676955684459049579026721 2007716763344287184270041)
              ·
                refine ⟨1505787572508215388202531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007716763344287184270041 1505787572508215388202531)
                ·
                  refine ⟨2258681358762323082303797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505787572508215388202531 2258681358762323082303797)
                  ·
                    refine ⟨211751377383967788965981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2258681358762323082303797 211751377383967788965981)
                    ·
                      rfl

theorem cell23_1237153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1237153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237153 prefixEnd_1237153 := by exact prefixLift 1237153
  have htrace : WordTrace (prefixWord ++ tailWord_1237153) baseStart_1237153 baseEnd_1237153 := by
    simpa [prefixWord, tailWord_1237153, baseEnd_1237153] using wordTrace_append hprefix tailTrace_1237153
  have hstable : (prefixWord ++ tailWord_1237153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237153).length < 2 ^ (prefixWord ++ tailWord_1237153).sum := by decide
  have hdescent : baseEnd_1237153 < baseStart_1237153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237176 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_1237176 : Nat := 118140960795 + 1237176 * 2 ^ 59
def prefixEnd_1237176 : Nat := 4983230072969 + 3 ^ 40 * 1237176 * 2
def baseEnd_1237176 : Nat := 635265942206956776910337

theorem tailTrace_1237176 : CollatzResearch.WordTrace tailWord_1237176 prefixEnd_1237176 635265942206956776910337 := by
  unfold tailWord_1237176
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561757882965059842013691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30082343843953413122684921 22561757882965059842013691)
  ·
    refine ⟨33842636824447589763020537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22561757882965059842013691 33842636824447589763020537)
    ·
      refine ⟨25381977618335692322265403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33842636824447589763020537 25381977618335692322265403)
      ·
        refine ⟨38072966427503538483398105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25381977618335692322265403 38072966427503538483398105)
        ·
          refine ⟨28554724820627653862548579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38072966427503538483398105 28554724820627653862548579)
          ·
            refine ⟨42832087230941480793822869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28554724820627653862548579 42832087230941480793822869)
            ·
              refine ⟨2007754088950381912210447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42832087230941480793822869 2007754088950381912210447)
              ·
                refine ⟨3011631133425572868315671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007754088950381912210447 3011631133425572868315671)
                ·
                  refine ⟨4517446700138359302473507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011631133425572868315671 4517446700138359302473507)
                  ·
                    refine ⟨6776170050207538953710261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4517446700138359302473507 6776170050207538953710261)
                    ·
                      refine ⟨635265942206956776910337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6776170050207538953710261 635265942206956776910337)
                      ·
                        rfl

theorem cell23_1237176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_1237176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237176 prefixEnd_1237176 := by exact prefixLift 1237176
  have htrace : WordTrace (prefixWord ++ tailWord_1237176) baseStart_1237176 baseEnd_1237176 := by
    simpa [prefixWord, tailWord_1237176, baseEnd_1237176] using wordTrace_append hprefix tailTrace_1237176
  have hstable : (prefixWord ++ tailWord_1237176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237176).length < 2 ^ (prefixWord ++ tailWord_1237176).sum := by decide
  have hdescent : baseEnd_1237176 < baseStart_1237176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237199 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_1237199 : Nat := 118140960795 + 1237199 * 2 ^ 59
def prefixEnd_1237199 : Nat := 4983230072969 + 3 ^ 40 * 1237199 * 2
def baseEnd_1237199 : Nat := 635277752262010186922731

theorem tailTrace_1237199 : CollatzResearch.WordTrace tailWord_1237199 prefixEnd_1237199 635277752262010186922731 := by
  unfold tailWord_1237199
  simp only [CollatzResearch.WordTrace]
  refine ⟨45124354644846794612114651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30082903096564529741409767 45124354644846794612114651)
  ·
    refine ⟨67686531967270191918171977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45124354644846794612114651 67686531967270191918171977)
    ·
      refine ⟨50764898975452643938628983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67686531967270191918171977 50764898975452643938628983)
      ·
        refine ⟨76147348463178965907943475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50764898975452643938628983 76147348463178965907943475)
        ·
          refine ⟨114221022694768448861915213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76147348463178965907943475 114221022694768448861915213)
          ·
            refine ⟨42832883510538168323218205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114221022694768448861915213 42832883510538168323218205)
            ·
              refine ⟨16062331316451813121206827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42832883510538168323218205 16062331316451813121206827)
              ·
                refine ⟨24093496974677719681810241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16062331316451813121206827 24093496974677719681810241)
                ·
                  refine ⟨18070122731008289761357681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24093496974677719681810241 18070122731008289761357681)
                  ·
                    refine ⟨13552592048256217321018261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18070122731008289761357681 13552592048256217321018261)
                    ·
                      refine ⟨635277752262010186922731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13552592048256217321018261 635277752262010186922731)
                      ·
                        rfl

theorem cell23_1237199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_1237199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237199 prefixEnd_1237199 := by exact prefixLift 1237199
  have htrace : WordTrace (prefixWord ++ tailWord_1237199) baseStart_1237199 baseEnd_1237199 := by
    simpa [prefixWord, tailWord_1237199, baseEnd_1237199] using wordTrace_append hprefix tailTrace_1237199
  have hstable : (prefixWord ++ tailWord_1237199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237199).length < 2 ^ (prefixWord ++ tailWord_1237199).sum := by decide
  have hdescent : baseEnd_1237199 < baseStart_1237199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237223 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1237223 : Nat := 118140960795 + 1237223 * 2 ^ 59
def prefixEnd_1237223 : Nat := 4983230072969 + 3 ^ 40 * 1237223 * 2
def baseEnd_1237223 : Nat := 635290075797718093022621

theorem tailTrace_1237223 : CollatzResearch.WordTrace tailWord_1237223 prefixEnd_1237223 635290075797718093022621 := by
  unfold tailWord_1237223
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125229996759846710988323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30083486664506564473992215 45125229996759846710988323)
  ·
    refine ⟨67687844995139770066482485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45125229996759846710988323 67687844995139770066482485)
    ·
      refine ⟨6345735468294353443732733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67687844995139770066482485 6345735468294353443732733)
      ·
        refine ⟨2379650800610382541399775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6345735468294353443732733 2379650800610382541399775)
        ·
          refine ⟨3569476200915573812099663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379650800610382541399775 3569476200915573812099663)
          ·
            refine ⟨5354214301373360718149495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569476200915573812099663 5354214301373360718149495)
            ·
              refine ⟨8031321452060041077224243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354214301373360718149495 8031321452060041077224243)
              ·
                refine ⟨12046982178090061615836365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031321452060041077224243 12046982178090061615836365)
                ·
                  refine ⟨4517618316783773105938637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12046982178090061615836365 4517618316783773105938637)
                  ·
                    refine ⟨1694106868793914914726989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4517618316783773105938637 1694106868793914914726989)
                    ·
                      refine ⟨635290075797718093022621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1694106868793914914726989 635290075797718093022621)
                      ·
                        rfl

theorem cell23_1237223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1237223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237223 prefixEnd_1237223 := by exact prefixLift 1237223
  have htrace : WordTrace (prefixWord ++ tailWord_1237223) baseStart_1237223 baseEnd_1237223 := by
    simpa [prefixWord, tailWord_1237223, baseEnd_1237223] using wordTrace_append hprefix tailTrace_1237223
  have hstable : (prefixWord ++ tailWord_1237223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237223).length < 2 ^ (prefixWord ++ tailWord_1237223).sum := by decide
  have hdescent : baseEnd_1237223 < baseStart_1237223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237256 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1237256 : Nat := 118140960795 + 1237256 * 2 ^ 59
def prefixEnd_1237256 : Nat := 4983230072969 + 3 ^ 40 * 1237256 * 2
def baseEnd_1237256 : Nat := 211769006886438821303323

theorem tailTrace_1237256 : CollatzResearch.WordTrace tailWord_1237256 prefixEnd_1237256 211769006886438821303323 := by
  unfold tailWord_1237256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563216802820146673469811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30084289070426862231293081 22563216802820146673469811)
  ·
    refine ⟨33844825204230220010204717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22563216802820146673469811 33844825204230220010204717)
    ·
      refine ⟨12691809451586332503826769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33844825204230220010204717 12691809451586332503826769)
      ·
        refine ⟨9518857088689749377870077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12691809451586332503826769 9518857088689749377870077)
        ·
          refine ⟨3569571408258656016701279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9518857088689749377870077 3569571408258656016701279)
          ·
            refine ⟨5354357112387984025051919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569571408258656016701279 5354357112387984025051919)
            ·
              refine ⟨8031535668581976037577879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354357112387984025051919 8031535668581976037577879)
              ·
                refine ⟨12047303502872964056366819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031535668581976037577879 12047303502872964056366819)
                ·
                  refine ⟨18070955254309446084550229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12047303502872964056366819 18070955254309446084550229)
                  ·
                    refine ⟨211769006886438821303323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18070955254309446084550229 211769006886438821303323)
                    ·
                      rfl

theorem cell23_1237256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1237256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237256 prefixEnd_1237256 := by exact prefixLift 1237256
  have htrace : WordTrace (prefixWord ++ tailWord_1237256) baseStart_1237256 baseEnd_1237256 := by
    simpa [prefixWord, tailWord_1237256, baseEnd_1237256] using wordTrace_append hprefix tailTrace_1237256
  have hstable : (prefixWord ++ tailWord_1237256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237256).length < 2 ^ (prefixWord ++ tailWord_1237256).sum := by decide
  have hdescent : baseEnd_1237256 < baseStart_1237256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237276 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1237276 : Nat := 118140960795 + 1237276 * 2 ^ 59
def prefixEnd_1237276 : Nat := 4983230072969 + 3 ^ 40 * 1237276 * 2
def baseEnd_1237276 : Nat := 635317290272406385659877

theorem tailTrace_1237276 : CollatzResearch.WordTrace tailWord_1237276 prefixEnd_1237276 635317290272406385659877 := by
  unfold tailWord_1237276
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563581532783918381333841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30084775377045224508445121 22563581532783918381333841)
  ·
    refine ⟨16922686149587938786000381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22563581532783918381333841 16922686149587938786000381)
    ·
      refine ⟨6346007306095477044750143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16922686149587938786000381 6346007306095477044750143)
      ·
        refine ⟨9519010959143215567125215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6346007306095477044750143 9519010959143215567125215)
        ·
          refine ⟨14278516438714823350687823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9519010959143215567125215 14278516438714823350687823)
          ·
            refine ⟨21417774658072235026031735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14278516438714823350687823 21417774658072235026031735)
            ·
              refine ⟨32126661987108352539047603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21417774658072235026031735 32126661987108352539047603)
              ·
                refine ⟨48189992980662528808571405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32126661987108352539047603 48189992980662528808571405)
                ·
                  refine ⟨18071247367748448303214277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48189992980662528808571405 18071247367748448303214277)
                  ·
                    refine ⟨3388358881452834056852677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18071247367748448303214277 3388358881452834056852677)
                    ·
                      refine ⟨635317290272406385659877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3388358881452834056852677 635317290272406385659877)
                      ·
                        rfl

theorem cell23_1237276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1237276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237276 prefixEnd_1237276 := by exact prefixLift 1237276
  have htrace : WordTrace (prefixWord ++ tailWord_1237276) baseStart_1237276 baseEnd_1237276 := by
    simpa [prefixWord, tailWord_1237276, baseEnd_1237276] using wordTrace_append hprefix tailTrace_1237276
  have hstable : (prefixWord ++ tailWord_1237276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237276).length < 2 ^ (prefixWord ++ tailWord_1237276).sum := by decide
  have hdescent : baseEnd_1237276 < baseStart_1237276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237280 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1237280 : Nat := 118140960795 + 1237280 * 2 ^ 59
def prefixEnd_1237280 : Nat := 4983230072969 + 3 ^ 40 * 1237280 * 2
def baseEnd_1237280 : Nat := 635319344195024370009859

theorem tailTrace_1237280 : CollatzResearch.WordTrace tailWord_1237280 prefixEnd_1237280 635319344195024370009859 := by
  unfold tailWord_1237280
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563654478776672722906647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30084872638368896963875529 22563654478776672722906647)
  ·
    refine ⟨33845481718165009084359971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22563654478776672722906647 33845481718165009084359971)
    ·
      refine ⟨50768222577247513626539957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33845481718165009084359971 50768222577247513626539957)
      ·
        refine ⟨4759520866616954402488121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50768222577247513626539957 4759520866616954402488121)
        ·
          refine ⟨3569640649962715801866091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4759520866616954402488121 3569640649962715801866091)
          ·
            refine ⟨5354460974944073702799137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569640649962715801866091 5354460974944073702799137)
            ·
              refine ⟨4015845731208055277099353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354460974944073702799137 4015845731208055277099353)
              ·
                refine ⟨3011884298406041457824515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015845731208055277099353 3011884298406041457824515)
                ·
                  refine ⟨4517826447609062186736773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011884298406041457824515 4517826447609062186736773)
                  ·
                    refine ⟨847092458926699160013145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517826447609062186736773 847092458926699160013145)
                    ·
                      refine ⟨635319344195024370009859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847092458926699160013145 635319344195024370009859)
                      ·
                        rfl

theorem cell23_1237280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1237280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237280 prefixEnd_1237280 := by exact prefixLift 1237280
  have htrace : WordTrace (prefixWord ++ tailWord_1237280) baseStart_1237280 baseEnd_1237280 := by
    simpa [prefixWord, tailWord_1237280, baseEnd_1237280] using wordTrace_append hprefix tailTrace_1237280
  have hstable : (prefixWord ++ tailWord_1237280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237280).length < 2 ^ (prefixWord ++ tailWord_1237280).sum := by decide
  have hdescent : baseEnd_1237280 < baseStart_1237280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237284 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_1237284 : Nat := 118140960795 + 1237284 * 2 ^ 59
def prefixEnd_1237284 : Nat := 4983230072969 + 3 ^ 40 * 1237284 * 2
def baseEnd_1237284 : Nat := 635321398117642354359841

theorem tailTrace_1237284 : CollatzResearch.WordTrace tailWord_1237284 prefixEnd_1237284 635321398117642354359841 := by
  unfold tailWord_1237284
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563727424769427064479453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30084969899692569419305937 22563727424769427064479453)
  ·
    refine ⟨8461397784288535149179795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22563727424769427064479453 8461397784288535149179795)
    ·
      refine ⟨12692096676432802723769693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461397784288535149179795 12692096676432802723769693)
      ·
        refine ⟨4759536253662301021413635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12692096676432802723769693 4759536253662301021413635)
        ·
          refine ⟨7139304380493451532120453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759536253662301021413635 7139304380493451532120453)
          ·
            refine ⟨1338619571342522162272585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7139304380493451532120453 1338619571342522162272585)
            ·
              refine ⟨1003964678506891621704439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338619571342522162272585 1003964678506891621704439)
              ·
                refine ⟨1505947017760337432556659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003964678506891621704439 1505947017760337432556659)
                ·
                  refine ⟨2258920526640506148834989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505947017760337432556659 2258920526640506148834989)
                  ·
                    refine ⟨847095197490189805813121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258920526640506148834989 847095197490189805813121)
                    ·
                      refine ⟨635321398117642354359841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847095197490189805813121 635321398117642354359841)
                      ·
                        rfl

theorem cell23_1237284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_1237284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237284 prefixEnd_1237284 := by exact prefixLift 1237284
  have htrace : WordTrace (prefixWord ++ tailWord_1237284) baseStart_1237284 baseEnd_1237284 := by
    simpa [prefixWord, tailWord_1237284, baseEnd_1237284] using wordTrace_append hprefix tailTrace_1237284
  have hstable : (prefixWord ++ tailWord_1237284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237284).length < 2 ^ (prefixWord ++ tailWord_1237284).sum := by decide
  have hdescent : baseEnd_1237284 < baseStart_1237284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237297 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_1237297 : Nat := 118140960795 + 1237297 * 2 ^ 59
def prefixEnd_1237297 : Nat := 4983230072969 + 3 ^ 40 * 1237297 * 2
def baseEnd_1237297 : Nat := 635328073366150803497281

theorem tailTrace_1237297 : CollatzResearch.WordTrace tailWord_1237297 prefixEnd_1237297 635328073366150803497281 := by
  unfold tailWord_1237297
  simp only [CollatzResearch.WordTrace]
  refine ⟨45127928998491757349182145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30085285998994504899454763 45127928998491757349182145)
  ·
    refine ⟨33845946748868818011886609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45127928998491757349182145 33845946748868818011886609)
    ·
      refine ⟨25384460061651613508914957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33845946748868818011886609 25384460061651613508914957)
      ·
        refine ⟨9519172523119355065843109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25384460061651613508914957 9519172523119355065843109)
        ·
          refine ⟨1784844848084879074845583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9519172523119355065843109 1784844848084879074845583)
          ·
            refine ⟨2677267272127318612268375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784844848084879074845583 2677267272127318612268375)
            ·
              refine ⟨4015900908190977918402563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677267272127318612268375 4015900908190977918402563)
              ·
                refine ⟨6023851362286466877603845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015900908190977918402563 6023851362286466877603845)
                ·
                  refine ⟨1129472130428712539550721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6023851362286466877603845 1129472130428712539550721)
                  ·
                    refine ⟨847104097821534404663041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1129472130428712539550721 847104097821534404663041)
                    ·
                      refine ⟨635328073366150803497281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847104097821534404663041 635328073366150803497281)
                      ·
                        rfl

theorem cell23_1237297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_1237297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237297 prefixEnd_1237297 := by exact prefixLift 1237297
  have htrace : WordTrace (prefixWord ++ tailWord_1237297) baseStart_1237297 baseEnd_1237297 := by
    simpa [prefixWord, tailWord_1237297, baseEnd_1237297] using wordTrace_append hprefix tailTrace_1237297
  have hstable : (prefixWord ++ tailWord_1237297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237297).length < 2 ^ (prefixWord ++ tailWord_1237297).sum := by decide
  have hdescent : baseEnd_1237297 < baseStart_1237297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237326 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1237326 : Nat := 118140960795 + 1237326 * 2 ^ 59
def prefixEnd_1237326 : Nat := 4983230072969 + 3 ^ 40 * 1237326 * 2
def baseEnd_1237326 : Nat := 635342964305131190034647

theorem tailTrace_1237326 : CollatzResearch.WordTrace tailWord_1237326 prefixEnd_1237326 635342964305131190034647 := by
  unfold tailWord_1237326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641123339423336912748479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30085991143591130201325221 5641123339423336912748479)
  ·
    refine ⟨8461685009135005369122719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641123339423336912748479 8461685009135005369122719)
    ·
      refine ⟨12692527513702508053684079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461685009135005369122719 12692527513702508053684079)
      ·
        refine ⟨19038791270553762080526119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12692527513702508053684079 19038791270553762080526119)
        ·
          refine ⟨28558186905830643120789179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19038791270553762080526119 28558186905830643120789179)
          ·
            refine ⟨42837280358745964681183769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28558186905830643120789179 42837280358745964681183769)
            ·
              refine ⟨32127960269059473510887827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42837280358745964681183769 32127960269059473510887827)
              ·
                refine ⟨48191940403589210266331741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32127960269059473510887827 48191940403589210266331741)
                ·
                  refine ⟨18071977651345953849874403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48191940403589210266331741 18071977651345953849874403)
                  ·
                    refine ⟨27107966477018930774811605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18071977651345953849874403 27107966477018930774811605)
                    ·
                      refine ⟨635342964305131190034647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27107966477018930774811605 635342964305131190034647)
                      ·
                        rfl

theorem cell23_1237326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1237326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237326 prefixEnd_1237326 := by exact prefixLift 1237326
  have htrace : WordTrace (prefixWord ++ tailWord_1237326) baseStart_1237326 baseEnd_1237326 := by
    simpa [prefixWord, tailWord_1237326, baseEnd_1237326] using wordTrace_append hprefix tailTrace_1237326
  have hstable : (prefixWord ++ tailWord_1237326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237326).length < 2 ^ (prefixWord ++ tailWord_1237326).sum := by decide
  have hdescent : baseEnd_1237326 < baseStart_1237326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237353 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_1237353 : Nat := 118140960795 + 1237353 * 2 ^ 59
def prefixEnd_1237353 : Nat := 4983230072969 + 3 ^ 40 * 1237353 * 2
def baseEnd_1237353 : Nat := 635356828282802584397023

theorem tailTrace_1237353 : CollatzResearch.WordTrace tailWord_1237353 prefixEnd_1237353 635356828282802584397023 := by
  unfold tailWord_1237353
  simp only [CollatzResearch.WordTrace]
  refine ⟨45129971486288878913220713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30086647657525919275480475 45129971486288878913220713)
  ·
    refine ⟨33847478614716659184915535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45129971486288878913220713 33847478614716659184915535)
    ·
      refine ⟨50771217922074988777373303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33847478614716659184915535 50771217922074988777373303)
      ·
        refine ⟨76156826883112483166059955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50771217922074988777373303 76156826883112483166059955)
        ·
          refine ⟨114235240324668724749089933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76156826883112483166059955 114235240324668724749089933)
          ·
            refine ⟨42838215121750771780908725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114235240324668724749089933 42838215121750771780908725)
            ·
              refine ⟨4016082667664134854460193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42838215121750771780908725 4016082667664134854460193)
              ·
                refine ⟨3012062000748101140845145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4016082667664134854460193 3012062000748101140845145)
                ·
                  refine ⟨2259046500561075855633859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012062000748101140845145 2259046500561075855633859)
                  ·
                    refine ⟨3388569750841613783450789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2259046500561075855633859 3388569750841613783450789)
                    ·
                      refine ⟨635356828282802584397023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3388569750841613783450789 635356828282802584397023)
                      ·
                        rfl

theorem cell23_1237353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_1237353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237353 prefixEnd_1237353 := by exact prefixLift 1237353
  have htrace : WordTrace (prefixWord ++ tailWord_1237353) baseStart_1237353 baseEnd_1237353 := by
    simpa [prefixWord, tailWord_1237353, baseEnd_1237353] using wordTrace_append hprefix tailTrace_1237353
  have hstable : (prefixWord ++ tailWord_1237353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237353).length < 2 ^ (prefixWord ++ tailWord_1237353).sum := by decide
  have hdescent : baseEnd_1237353 < baseStart_1237353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237410 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_1237410 : Nat := 118140960795 + 1237410 * 2 ^ 59
def prefixEnd_1237410 : Nat := 4983230072969 + 3 ^ 40 * 1237410 * 2
def baseEnd_1237410 : Nat := 70598455186678762376029

theorem tailTrace_1237410 : CollatzResearch.WordTrace tailWord_1237410 prefixEnd_1237410 70598455186678762376029 := by
  unfold tailWord_1237410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283012611770594412011421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30088033631388251765363789 11283012611770594412011421)
  ·
    refine ⟨4231129729413972904504283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11283012611770594412011421 4231129729413972904504283)
    ·
      refine ⟨6346694594120959356756425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231129729413972904504283 6346694594120959356756425)
      ·
        refine ⟨4760020945590719517567319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6346694594120959356756425 4760020945590719517567319)
        ·
          refine ⟨7140031418386079276350979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760020945590719517567319 7140031418386079276350979)
          ·
            refine ⟨10710047127579118914526469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140031418386079276350979 10710047127579118914526469)
            ·
              refine ⟨2008133836421084796473713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10710047127579118914526469 2008133836421084796473713)
              ·
                refine ⟨1506100377315813597355285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008133836421084796473713 1506100377315813597355285)
                ·
                  refine ⟨70598455186678762376029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1506100377315813597355285 70598455186678762376029)
                  ·
                    rfl

theorem cell23_1237410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_1237410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237410 prefixEnd_1237410 := by exact prefixLift 1237410
  have htrace : WordTrace (prefixWord ++ tailWord_1237410) baseStart_1237410 baseEnd_1237410 := by
    simpa [prefixWord, tailWord_1237410, baseEnd_1237410] using wordTrace_append hprefix tailTrace_1237410
  have hstable : (prefixWord ++ tailWord_1237410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237410).length < 2 ^ (prefixWord ++ tailWord_1237410).sum := by decide
  have hdescent : baseEnd_1237410 < baseStart_1237410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237420 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_1237420 : Nat := 118140960795 + 1237420 * 2 ^ 59
def prefixEnd_1237420 : Nat := 4983230072969 + 3 ^ 40 * 1237420 * 2
def baseEnd_1237420 : Nat := 635391231486653822259215

theorem tailTrace_1237420 : CollatzResearch.WordTrace tailWord_1237420 prefixEnd_1237420 635391231486653822259215 := by
  unfold tailWord_1237420
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566207588523074677954857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30088276784697432903939809 22566207588523074677954857)
  ·
    refine ⟨16924655691392306008466143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22566207588523074677954857 16924655691392306008466143)
    ·
      refine ⟨25386983537088459012699215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16924655691392306008466143 25386983537088459012699215)
      ·
        refine ⟨38080475305632688519048823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25386983537088459012699215 38080475305632688519048823)
        ·
          refine ⟨57120712958449032778573235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38080475305632688519048823 57120712958449032778573235)
          ·
            refine ⟨85681069437673549167859853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57120712958449032778573235 85681069437673549167859853)
            ·
              refine ⟨32130401039127580937947445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85681069437673549167859853 32130401039127580937947445)
              ·
                refine ⟨3012225097418210712932573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32130401039127580937947445 3012225097418210712932573)
                ·
                  refine ⟨1129584411531829017349715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3012225097418210712932573 1129584411531829017349715)
                  ·
                    refine ⟨1694376617297743526024573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129584411531829017349715 1694376617297743526024573)
                    ·
                      refine ⟨635391231486653822259215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1694376617297743526024573 635391231486653822259215)
                      ·
                        rfl

theorem cell23_1237420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_1237420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237420 prefixEnd_1237420 := by exact prefixLift 1237420
  have htrace : WordTrace (prefixWord ++ tailWord_1237420) baseStart_1237420 baseEnd_1237420 := by
    simpa [prefixWord, tailWord_1237420, baseEnd_1237420] using wordTrace_append hprefix tailTrace_1237420
  have hstable : (prefixWord ++ tailWord_1237420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237420).length < 2 ^ (prefixWord ++ tailWord_1237420).sum := by decide
  have hdescent : baseEnd_1237420 < baseStart_1237420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237437 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1237437 : Nat := 118140960795 + 1237437 * 2 ^ 59
def prefixEnd_1237437 : Nat := 4983230072969 + 3 ^ 40 * 1237437 * 2
def baseEnd_1237437 : Nat := 635399960657780255746637

theorem tailTrace_1237437 : CollatzResearch.WordTrace tailWord_1237437 prefixEnd_1237437 635399960657780255746637 := by
  unfold tailWord_1237437
  simp only [CollatzResearch.WordTrace]
  refine ⟨45133035217984561259278565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30088690145323040839519043 45133035217984561259278565)
  ·
    refine ⟨8462444103372105236114731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45133035217984561259278565 8462444103372105236114731)
    ·
      refine ⟨12693666155058157854172097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462444103372105236114731 12693666155058157854172097)
      ·
        refine ⟨9520249616293618390629073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12693666155058157854172097 9520249616293618390629073)
        ·
          refine ⟨7140187212220213792971805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9520249616293618390629073 7140187212220213792971805)
          ·
            refine ⟨2677570204582580172364427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7140187212220213792971805 2677570204582580172364427)
            ·
              refine ⟨4016355306873870258546641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677570204582580172364427 4016355306873870258546641)
              ·
                refine ⟨3012266480155402693909981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4016355306873870258546641 3012266480155402693909981)
                ·
                  refine ⟨1129599930058276010216243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3012266480155402693909981 1129599930058276010216243)
                  ·
                    refine ⟨1694399895087414015324365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129599930058276010216243 1694399895087414015324365)
                    ·
                      refine ⟨635399960657780255746637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1694399895087414015324365 635399960657780255746637)
                      ·
                        rfl

theorem cell23_1237437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1237437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237437 prefixEnd_1237437 := by exact prefixLift 1237437
  have htrace : WordTrace (prefixWord ++ tailWord_1237437) baseStart_1237437 baseEnd_1237437 := by
    simpa [prefixWord, tailWord_1237437, baseEnd_1237437] using wordTrace_append hprefix tailTrace_1237437
  have hstable : (prefixWord ++ tailWord_1237437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237437).length < 2 ^ (prefixWord ++ tailWord_1237437).sum := by decide
  have hdescent : baseEnd_1237437 < baseStart_1237437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237447 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_1237447 : Nat := 118140960795 + 1237447 * 2 ^ 59
def prefixEnd_1237447 : Nat := 4983230072969 + 3 ^ 40 * 1237447 * 2
def baseEnd_1237447 : Nat := 635405095464325216621591

theorem tailTrace_1237447 : CollatzResearch.WordTrace tailWord_1237447 prefixEnd_1237447 635405095464325216621591 := by
  unfold tailWord_1237447
  simp only [CollatzResearch.WordTrace]
  refine ⟨45133399947948332967142595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30088933298632221978095063 45133399947948332967142595)
  ·
    refine ⟨67700099921922499450713893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45133399947948332967142595 67700099921922499450713893)
    ·
      refine ⟨12693768735360468647008855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67700099921922499450713893 12693768735360468647008855)
      ·
        refine ⟨19040653103040702970513283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12693768735360468647008855 19040653103040702970513283)
        ·
          refine ⟨28560979654561054455769925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19040653103040702970513283 28560979654561054455769925)
          ·
            refine ⟨5355183685230197710456861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28560979654561054455769925 5355183685230197710456861)
            ·
              refine ⟨2008193881961324141421323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5355183685230197710456861 2008193881961324141421323)
              ·
                refine ⟨3012290822941986212131985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008193881961324141421323 3012290822941986212131985)
                ·
                  refine ⟨2259218117206489659098989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012290822941986212131985 2259218117206489659098989)
                  ·
                    refine ⟨847206793952433622162121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259218117206489659098989 847206793952433622162121)
                    ·
                      refine ⟨635405095464325216621591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847206793952433622162121 635405095464325216621591)
                      ·
                        rfl

theorem cell23_1237447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_1237447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237447 prefixEnd_1237447 := by exact prefixLift 1237447
  have htrace : WordTrace (prefixWord ++ tailWord_1237447) baseStart_1237447 baseEnd_1237447 := by
    simpa [prefixWord, tailWord_1237447, baseEnd_1237447] using wordTrace_append hprefix tailTrace_1237447
  have hstable : (prefixWord ++ tailWord_1237447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237447).length < 2 ^ (prefixWord ++ tailWord_1237447).sum := by decide
  have hdescent : baseEnd_1237447 < baseStart_1237447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237473 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1237473 : Nat := 118140960795 + 1237473 * 2 ^ 59
def prefixEnd_1237473 : Nat := 4983230072969 + 3 ^ 40 * 1237473 * 2
def baseEnd_1237473 : Nat := 635418445961342114896471

theorem tailTrace_1237473 : CollatzResearch.WordTrace tailWord_1237473 prefixEnd_1237473 635418445961342114896471 := by
  unfold tailWord_1237473
  simp only [CollatzResearch.WordTrace]
  refine ⟨45134348245854139407589073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30089565497236092938392715 45134348245854139407589073)
  ·
    refine ⟨33850761184390604555691805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45134348245854139407589073 33850761184390604555691805)
    ·
      refine ⟨12694035444146476708384427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33850761184390604555691805 12694035444146476708384427)
      ·
        refine ⟨19041053166219715062576641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694035444146476708384427 19041053166219715062576641)
        ·
          refine ⟨14280789874664786296932481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19041053166219715062576641 14280789874664786296932481)
          ·
            refine ⟨10710592405998589722699361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14280789874664786296932481 10710592405998589722699361)
            ·
              refine ⟨8032944304498942292024521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10710592405998589722699361 8032944304498942292024521)
              ·
                refine ⟨6024708228374206719018391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032944304498942292024521 6024708228374206719018391)
                ·
                  refine ⟨9037062342561310078527587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6024708228374206719018391 9037062342561310078527587)
                  ·
                    refine ⟨13555593513841965117791381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9037062342561310078527587 13555593513841965117791381)
                    ·
                      refine ⟨635418445961342114896471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13555593513841965117791381 635418445961342114896471)
                      ·
                        rfl

theorem cell23_1237473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1237473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237473 prefixEnd_1237473 := by exact prefixLift 1237473
  have htrace : WordTrace (prefixWord ++ tailWord_1237473) baseStart_1237473 baseEnd_1237473 := by
    simpa [prefixWord, tailWord_1237473, baseEnd_1237473] using wordTrace_append hprefix tailTrace_1237473
  have hstable : (prefixWord ++ tailWord_1237473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237473).length < 2 ^ (prefixWord ++ tailWord_1237473).sum := by decide
  have hdescent : baseEnd_1237473 < baseStart_1237473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237480 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1237480 : Nat := 118140960795 + 1237480 * 2 ^ 59
def prefixEnd_1237480 : Nat := 4983230072969 + 3 ^ 40 * 1237480 * 2
def baseEnd_1237480 : Nat := 635422040325923587508939

theorem tailTrace_1237480 : CollatzResearch.WordTrace tailWord_1237480 prefixEnd_1237480 635422040325923587508939 := by
  unfold tailWord_1237480
  simp only [CollatzResearch.WordTrace]
  refine ⟨22567301778414389801546947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30089735704552519735395929 22567301778414389801546947)
  ·
    refine ⟨33850952667621584702320421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22567301778414389801546947 33850952667621584702320421)
    ·
      refine ⟨6347053625179047131685079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33850952667621584702320421 6347053625179047131685079)
      ·
        refine ⟨9520580437768570697527619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6347053625179047131685079 9520580437768570697527619)
        ·
          refine ⟨14280870656652856046291429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9520580437768570697527619 14280870656652856046291429)
          ·
            refine ⟨2677663248122410508679643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14280870656652856046291429 2677663248122410508679643)
            ·
              refine ⟨4016494872183615763019465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677663248122410508679643 4016494872183615763019465)
              ·
                refine ⟨3012371154137711822264599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4016494872183615763019465 3012371154137711822264599)
                ·
                  refine ⟨4518556731206567733396899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012371154137711822264599 4518556731206567733396899)
                  ·
                    refine ⟨6777835096809851600095349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4518556731206567733396899 6777835096809851600095349)
                    ·
                      refine ⟨635422040325923587508939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6777835096809851600095349 635422040325923587508939)
                      ·
                        rfl

theorem cell23_1237480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1237480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237480 prefixEnd_1237480 := by exact prefixLift 1237480
  have htrace : WordTrace (prefixWord ++ tailWord_1237480) baseStart_1237480 baseEnd_1237480 := by
    simpa [prefixWord, tailWord_1237480, baseEnd_1237480] using wordTrace_append hprefix tailTrace_1237480
  have hstable : (prefixWord ++ tailWord_1237480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237480).length < 2 ^ (prefixWord ++ tailWord_1237480).sum := by decide
  have hdescent : baseEnd_1237480 < baseStart_1237480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237494 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1237494 : Nat := 118140960795 + 1237494 * 2 ^ 59
def prefixEnd_1237494 : Nat := 4983230072969 + 3 ^ 40 * 1237494 * 2
def baseEnd_1237494 : Nat := 635429229055086532733875

theorem tailTrace_1237494 : CollatzResearch.WordTrace tailWord_1237494 prefixEnd_1237494 635429229055086532733875 := by
  unfold tailWord_1237494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820944636173628749631471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30090076119185373329402357 2820944636173628749631471)
  ·
    refine ⟨4231416954260443124447207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820944636173628749631471 4231416954260443124447207)
    ·
      refine ⟨6347125431390664686670811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231416954260443124447207 6347125431390664686670811)
      ·
        refine ⟨9520688147085997030006217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6347125431390664686670811 9520688147085997030006217)
        ·
          refine ⟨7140516110314497772504663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9520688147085997030006217 7140516110314497772504663)
          ·
            refine ⟨10710774165471746658756995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140516110314497772504663 10710774165471746658756995)
            ·
              refine ⟨16066161248207619988135493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10710774165471746658756995 16066161248207619988135493)
              ·
                refine ⟨3012405234038928747775405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16066161248207619988135493 3012405234038928747775405)
                ·
                  refine ⟨1129651962764598280415777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3012405234038928747775405 1129651962764598280415777)
                  ·
                    refine ⟨847238972073448710311833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1129651962764598280415777 847238972073448710311833)
                    ·
                      refine ⟨635429229055086532733875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847238972073448710311833 635429229055086532733875)
                      ·
                        rfl

theorem cell23_1237494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1237494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237494 prefixEnd_1237494 := by exact prefixLift 1237494
  have htrace : WordTrace (prefixWord ++ tailWord_1237494) baseStart_1237494 baseEnd_1237494 := by
    simpa [prefixWord, tailWord_1237494, baseEnd_1237494] using wordTrace_append hprefix tailTrace_1237494
  have hstable : (prefixWord ++ tailWord_1237494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237494).length < 2 ^ (prefixWord ++ tailWord_1237494).sum := by decide
  have hdescent : baseEnd_1237494 < baseStart_1237494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237517 : List Nat := [1, 7, 1, 1, 1, 1, 11]
def baseStart_1237517 : Nat := 118140960795 + 1237517 * 2 ^ 59
def prefixEnd_1237517 : Nat := 4983230072969 + 3 ^ 40 * 1237517 * 2
def baseEnd_1237517 : Nat := 7844951100125184478349

theorem tailTrace_1237517 : CollatzResearch.WordTrace tailWord_1237517 prefixEnd_1237517 7844951100125184478349 := by
  unfold tailWord_1237517
  simp only [CollatzResearch.WordTrace]
  refine ⟨45135953057694734922190805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30090635371796489948127203 45135953057694734922190805)
  ·
    refine ⟨1057873899789720349738847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45135953057694734922190805 1057873899789720349738847)
    ·
      refine ⟨1586810849684580524608271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057873899789720349738847 1586810849684580524608271)
      ·
        refine ⟨2380216274526870786912407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586810849684580524608271 2380216274526870786912407)
        ·
          refine ⟨3570324411790306180368611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380216274526870786912407 3570324411790306180368611)
          ·
            refine ⟨5355486617685459270552917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570324411790306180368611 5355486617685459270552917)
            ·
              refine ⟨7844951100125184478349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5355486617685459270552917 7844951100125184478349)
              ·
                rfl

theorem cell23_1237517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 11].length) (baseStart_1237517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237517 prefixEnd_1237517 := by exact prefixLift 1237517
  have htrace : WordTrace (prefixWord ++ tailWord_1237517) baseStart_1237517 baseEnd_1237517 := by
    simpa [prefixWord, tailWord_1237517, baseEnd_1237517] using wordTrace_append hprefix tailTrace_1237517
  have hstable : (prefixWord ++ tailWord_1237517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237517).length < 2 ^ (prefixWord ++ tailWord_1237517).sum := by decide
  have hdescent : baseEnd_1237517 < baseStart_1237517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237523 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_1237523 : Nat := 118140960795 + 1237523 * 2 ^ 59
def prefixEnd_1237523 : Nat := 4983230072969 + 3 ^ 40 * 1237523 * 2
def baseEnd_1237523 : Nat := 635444119994066919271241

theorem tailTrace_1237523 : CollatzResearch.WordTrace tailWord_1237523 prefixEnd_1237523 635444119994066919271241 := by
  unfold tailWord_1237523
  simp only [CollatzResearch.WordTrace]
  refine ⟨45136171895672997946909223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30090781263781998631272815 45136171895672997946909223)
  ·
    refine ⟨67704257843509496920363835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45136171895672997946909223 67704257843509496920363835)
    ·
      refine ⟨101556386765264245380545753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67704257843509496920363835 101556386765264245380545753)
      ·
        refine ⟨76167290073948184035409315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101556386765264245380545753 76167290073948184035409315)
        ·
          refine ⟨114250935110922276053113973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76167290073948184035409315 114250935110922276053113973)
          ·
            refine ⟨10711025166648963379979435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114250935110922276053113973 10711025166648963379979435)
            ·
              refine ⟨16066537749973445069969153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10711025166648963379979435 16066537749973445069969153)
              ·
                refine ⟨12049903312480083802476865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16066537749973445069969153 12049903312480083802476865)
                ·
                  refine ⟨9037427484360062851857649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12049903312480083802476865 9037427484360062851857649)
                  ·
                    refine ⟨6778070613270047138893237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9037427484360062851857649 6778070613270047138893237)
                    ·
                      refine ⟨635444119994066919271241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6778070613270047138893237 635444119994066919271241)
                      ·
                        rfl

theorem cell23_1237523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_1237523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237523 prefixEnd_1237523 := by exact prefixLift 1237523
  have htrace : WordTrace (prefixWord ++ tailWord_1237523) baseStart_1237523 baseEnd_1237523 := by
    simpa [prefixWord, tailWord_1237523, baseEnd_1237523] using wordTrace_append hprefix tailTrace_1237523
  have hstable : (prefixWord ++ tailWord_1237523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237523).length < 2 ^ (prefixWord ++ tailWord_1237523).sum := by decide
  have hdescent : baseEnd_1237523 < baseStart_1237523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237528 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1237528 : Nat := 118140960795 + 1237528 * 2 ^ 59
def prefixEnd_1237528 : Nat := 4983230072969 + 3 ^ 40 * 1237528 * 2
def baseEnd_1237528 : Nat := 635446687397339399708719

theorem tailTrace_1237528 : CollatzResearch.WordTrace tailWord_1237528 prefixEnd_1237528 635446687397339399708719 := by
  unfold tailWord_1237528
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568177130327441900420619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30090902840436589200560825 22568177130327441900420619)
  ·
    refine ⟨33852265695491162850630929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22568177130327441900420619 33852265695491162850630929)
    ·
      refine ⟨25389199271618372137973197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33852265695491162850630929 25389199271618372137973197)
      ·
        refine ⟨9520949726856889551739949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25389199271618372137973197 9520949726856889551739949)
        ·
          refine ⟨3570356147571333581902481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9520949726856889551739949 3570356147571333581902481)
          ·
            refine ⟨2677767110678500186426861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3570356147571333581902481 2677767110678500186426861)
            ·
              refine ⟨1004162666504437569910073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2677767110678500186426861 1004162666504437569910073)
              ·
                refine ⟨753121999878328177432555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004162666504437569910073 753121999878328177432555)
                ·
                  refine ⟨1129682999817492266148833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753121999878328177432555 1129682999817492266148833)
                  ·
                    refine ⟨847262249863119199611625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1129682999817492266148833 847262249863119199611625)
                    ·
                      refine ⟨635446687397339399708719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847262249863119199611625 635446687397339399708719)
                      ·
                        rfl

theorem cell23_1237528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1237528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237528 prefixEnd_1237528 := by exact prefixLift 1237528
  have htrace : WordTrace (prefixWord ++ tailWord_1237528) baseStart_1237528 baseEnd_1237528 := by
    simpa [prefixWord, tailWord_1237528, baseEnd_1237528] using wordTrace_append hprefix tailTrace_1237528
  have hstable : (prefixWord ++ tailWord_1237528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237528).length < 2 ^ (prefixWord ++ tailWord_1237528).sum := by decide
  have hdescent : baseEnd_1237528 < baseStart_1237528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237537 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_1237537 : Nat := 118140960795 + 1237537 * 2 ^ 59
def prefixEnd_1237537 : Nat := 4983230072969 + 3 ^ 40 * 1237537 * 2
def baseEnd_1237537 : Nat := 635451308723229864496177

theorem tailTrace_1237537 : CollatzResearch.WordTrace tailWord_1237537 prefixEnd_1237537 635451308723229864496177 := by
  unfold tailWord_1237537
  simp only [CollatzResearch.WordTrace]
  refine ⟨45136682517622278337918865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30091121678414852225279243 45136682517622278337918865)
  ·
    refine ⟨33852511888216708753439149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45136682517622278337918865 33852511888216708753439149)
    ·
      refine ⟨12694691958081265782539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33852511888216708753439149 12694691958081265782539681)
      ·
        refine ⟨9521018968560949336904761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12694691958081265782539681 9521018968560949336904761)
        ·
          refine ⟨7140764226420712002678571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9521018968560949336904761 7140764226420712002678571)
          ·
            refine ⟨10711146339631068004017857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140764226420712002678571 10711146339631068004017857)
            ·
              refine ⟨8033359754723301003013393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711146339631068004017857 8033359754723301003013393)
              ·
                refine ⟨6025019816042475752260045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8033359754723301003013393 6025019816042475752260045)
                ·
                  refine ⟨2259382431015928407097517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6025019816042475752260045 2259382431015928407097517)
                  ·
                    refine ⟨847268411630973152661569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259382431015928407097517 847268411630973152661569)
                    ·
                      refine ⟨635451308723229864496177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847268411630973152661569 635451308723229864496177)
                      ·
                        rfl

theorem cell23_1237537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_1237537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237537 prefixEnd_1237537 := by exact prefixLift 1237537
  have htrace : WordTrace (prefixWord ++ tailWord_1237537) baseStart_1237537 baseEnd_1237537 := by
    simpa [prefixWord, tailWord_1237537, baseEnd_1237537] using wordTrace_append hprefix tailTrace_1237537
  have hstable : (prefixWord ++ tailWord_1237537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237537).length < 2 ^ (prefixWord ++ tailWord_1237537).sum := by decide
  have hdescent : baseEnd_1237537 < baseStart_1237537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237554 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_1237554 : Nat := 118140960795 + 1237554 * 2 ^ 59
def prefixEnd_1237554 : Nat := 4983230072969 + 3 ^ 40 * 1237554 * 2
def baseEnd_1237554 : Nat := 635460037894356297983599

theorem tailTrace_1237554 : CollatzResearch.WordTrace tailWord_1237554 prefixEnd_1237554 635460037894356297983599 := by
  unfold tailWord_1237554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11284325639640172560321929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30091535039040460160858477 11284325639640172560321929)
  ·
    refine ⟨8463244229730129420241447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11284325639640172560321929 8463244229730129420241447)
    ·
      refine ⟨12694866344595194130362171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463244229730129420241447 12694866344595194130362171)
      ·
        refine ⟨19042299516892791195543257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694866344595194130362171 19042299516892791195543257)
        ·
          refine ⟨14281724637669593396657443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19042299516892791195543257 14281724637669593396657443)
          ·
            refine ⟨21422586956504390094986165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14281724637669593396657443 21422586956504390094986165)
            ·
              refine ⟨2008367527172286571404953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21422586956504390094986165 2008367527172286571404953)
              ·
                refine ⟨1506275645379214928553715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008367527172286571404953 1506275645379214928553715)
                ·
                  refine ⟨2259413468068822392830573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506275645379214928553715 2259413468068822392830573)
                  ·
                    refine ⟨847280050525808397311465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259413468068822392830573 847280050525808397311465)
                    ·
                      refine ⟨635460037894356297983599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847280050525808397311465 635460037894356297983599)
                      ·
                        rfl

theorem cell23_1237554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_1237554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237554 prefixEnd_1237554 := by exact prefixLift 1237554
  have htrace : WordTrace (prefixWord ++ tailWord_1237554) baseStart_1237554 baseEnd_1237554 := by
    simpa [prefixWord, tailWord_1237554, baseEnd_1237554] using wordTrace_append hprefix tailTrace_1237554
  have hstable : (prefixWord ++ tailWord_1237554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237554).length < 2 ^ (prefixWord ++ tailWord_1237554).sum := by decide
  have hdescent : baseEnd_1237554 < baseStart_1237554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237567 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 1, 4, 2]
def baseStart_1237567 : Nat := 118140960795 + 1237567 * 2 ^ 59
def prefixEnd_1237567 : Nat := 4983230072969 + 3 ^ 40 * 1237567 * 2
def baseEnd_1237567 : Nat := 635466713142864747121039

theorem tailTrace_1237567 : CollatzResearch.WordTrace tailWord_1237567 prefixEnd_1237567 635466713142864747121039 := by
  unfold tailWord_1237567
  simp only [CollatzResearch.WordTrace]
  refine ⟨45137776707513593461510955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30091851138342395641007303 45137776707513593461510955)
  ·
    refine ⟨67706665061270390192266433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45137776707513593461510955 67706665061270390192266433)
    ·
      refine ⟨50779998795952792644199825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67706665061270390192266433 50779998795952792644199825)
      ·
        refine ⟨38084999096964594483149869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50779998795952792644199825 38084999096964594483149869)
        ·
          refine ⟨14281874661361722931181201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38084999096964594483149869 14281874661361722931181201)
          ·
            refine ⟨10711405996021292198385901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14281874661361722931181201 10711405996021292198385901)
            ·
              refine ⟨4016777248507984574394713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10711405996021292198385901 4016777248507984574394713)
              ·
                refine ⟨3012582936380988430796035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4016777248507984574394713 3012582936380988430796035)
                ·
                  refine ⟨4518874404571482646194053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012582936380988430796035 4518874404571482646194053)
                  ·
                    refine ⟨847288950857152996161385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518874404571482646194053 847288950857152996161385)
                    ·
                      refine ⟨635466713142864747121039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847288950857152996161385 635466713142864747121039)
                      ·
                        rfl

theorem cell23_1237567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_1237567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237567 prefixEnd_1237567 := by exact prefixLift 1237567
  have htrace : WordTrace (prefixWord ++ tailWord_1237567) baseStart_1237567 baseEnd_1237567 := by
    simpa [prefixWord, tailWord_1237567, baseEnd_1237567] using wordTrace_append hprefix tailTrace_1237567
  have hstable : (prefixWord ++ tailWord_1237567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237567).length < 2 ^ (prefixWord ++ tailWord_1237567).sum := by decide
  have hdescent : baseEnd_1237567 < baseStart_1237567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237580 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1237580 : Nat := 118140960795 + 1237580 * 2 ^ 59
def prefixEnd_1237580 : Nat := 4983230072969 + 3 ^ 40 * 1237580 * 2
def baseEnd_1237580 : Nat := 635473388391373196258479

theorem tailTrace_1237580 : CollatzResearch.WordTrace tailWord_1237580 prefixEnd_1237580 635473388391373196258479 := by
  unfold tailWord_1237580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22569125428233248340867097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30092167237644331121156129 22569125428233248340867097)
  ·
    refine ⟨16926844071174936255650323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22569125428233248340867097 16926844071174936255650323)
    ·
      refine ⟨25390266106762404383475485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16926844071174936255650323 25390266106762404383475485)
      ·
        refine ⟨9521349790035901643803307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25390266106762404383475485 9521349790035901643803307)
        ·
          refine ⟨14282024685053852465704961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9521349790035901643803307 14282024685053852465704961)
          ·
            refine ⟨10711518513790389349278721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14282024685053852465704961 10711518513790389349278721)
            ·
              refine ⟨8033638885342792011959041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711518513790389349278721 8033638885342792011959041)
              ·
                refine ⟨6025229164007094008969281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8033638885342792011959041 6025229164007094008969281)
                ·
                  refine ⟨4518921873005320506726961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025229164007094008969281 4518921873005320506726961)
                  ·
                    refine ⟨3389191404753990380045221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4518921873005320506726961 3389191404753990380045221)
                    ·
                      refine ⟨635473388391373196258479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3389191404753990380045221 635473388391373196258479)
                      ·
                        rfl

theorem cell23_1237580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1237580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237580 prefixEnd_1237580 := by exact prefixLift 1237580
  have htrace : WordTrace (prefixWord ++ tailWord_1237580) baseStart_1237580 baseEnd_1237580 := by
    simpa [prefixWord, tailWord_1237580, baseEnd_1237580] using wordTrace_append hprefix tailTrace_1237580
  have hstable : (prefixWord ++ tailWord_1237580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237580).length < 2 ^ (prefixWord ++ tailWord_1237580).sum := by decide
  have hdescent : baseEnd_1237580 < baseStart_1237580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237583 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_1237583 : Nat := 118140960795 + 1237583 * 2 ^ 59
def prefixEnd_1237583 : Nat := 4983230072969 + 3 ^ 40 * 1237583 * 2
def baseEnd_1237583 : Nat := 635474928833336684520965

theorem tailTrace_1237583 : CollatzResearch.WordTrace tailWord_1237583 prefixEnd_1237583 635474928833336684520965 := by
  unfold tailWord_1237583
  simp only [CollatzResearch.WordTrace]
  refine ⟨45138360275455628194093403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30092240183637085462728935 45138360275455628194093403)
  ·
    refine ⟨67707540413183442291140105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45138360275455628194093403 67707540413183442291140105)
    ·
      refine ⟨50780655309887581718355079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67707540413183442291140105 50780655309887581718355079)
      ·
        refine ⟨76170982964831372577532619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50780655309887581718355079 76170982964831372577532619)
        ·
          refine ⟨114256474447247058866298929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76170982964831372577532619 114256474447247058866298929)
          ·
            refine ⟨85692355835435294149724197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114256474447247058866298929 85692355835435294149724197)
            ·
              refine ⟨16067316719144117653073287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85692355835435294149724197 16067316719144117653073287)
              ·
                refine ⟨24100975078716176479609931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16067316719144117653073287 24100975078716176479609931)
                ·
                  refine ⟨36151462618074264719414897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24100975078716176479609931 36151462618074264719414897)
                  ·
                    refine ⟨27113596963555698539561173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36151462618074264719414897 27113596963555698539561173)
                    ·
                      refine ⟨635474928833336684520965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27113596963555698539561173 635474928833336684520965)
                      ·
                        rfl

theorem cell23_1237583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_1237583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237583 prefixEnd_1237583 := by exact prefixLift 1237583
  have htrace : WordTrace (prefixWord ++ tailWord_1237583) baseStart_1237583 baseEnd_1237583 := by
    simpa [prefixWord, tailWord_1237583, baseEnd_1237583] using wordTrace_append hprefix tailTrace_1237583
  have hstable : (prefixWord ++ tailWord_1237583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237583).length < 2 ^ (prefixWord ++ tailWord_1237583).sum := by decide
  have hdescent : baseEnd_1237583 < baseStart_1237583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237593 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1237593 : Nat := 118140960795 + 1237593 * 2 ^ 59
def prefixEnd_1237593 : Nat := 4983230072969 + 3 ^ 40 * 1237593 * 2
def baseEnd_1237593 : Nat := 635480063639881645395919

theorem tailTrace_1237593 : CollatzResearch.WordTrace tailWord_1237593 prefixEnd_1237593 635480063639881645395919 := by
  unfold tailWord_1237593
  simp only [CollatzResearch.WordTrace]
  refine ⟨45138725005419399901957433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30092483336946266601304955 45138725005419399901957433)
  ·
    refine ⟨33854043754064549926468075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45138725005419399901957433 33854043754064549926468075)
    ·
      refine ⟨50781065631096824889702113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33854043754064549926468075 50781065631096824889702113)
      ·
        refine ⟨38085799223322618667276585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50781065631096824889702113 38085799223322618667276585)
        ·
          refine ⟨28564349417491964000457439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38085799223322618667276585 28564349417491964000457439)
          ·
            refine ⟨42846524126237946000686159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28564349417491964000457439 42846524126237946000686159)
            ·
              refine ⟨64269786189356919001029239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42846524126237946000686159 64269786189356919001029239)
              ·
                refine ⟨96404679284035378501543859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64269786189356919001029239 96404679284035378501543859)
                ·
                  refine ⟨144607018926053067752315789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96404679284035378501543859 144607018926053067752315789)
                  ·
                    refine ⟨54227632097269900407118421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144607018926053067752315789 54227632097269900407118421)
                    ·
                      refine ⟨635480063639881645395919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 54227632097269900407118421 635480063639881645395919)
                      ·
                        rfl

theorem cell23_1237593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1237593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237593 prefixEnd_1237593 := by exact prefixLift 1237593
  have htrace : WordTrace (prefixWord ++ tailWord_1237593) baseStart_1237593 baseEnd_1237593 := by
    simpa [prefixWord, tailWord_1237593, baseEnd_1237593] using wordTrace_append hprefix tailTrace_1237593
  have hstable : (prefixWord ++ tailWord_1237593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237593).length < 2 ^ (prefixWord ++ tailWord_1237593).sum := by decide
  have hdescent : baseEnd_1237593 < baseStart_1237593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237600 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1237600 : Nat := 118140960795 + 1237600 * 2 ^ 59
def prefixEnd_1237600 : Nat := 4983230072969 + 3 ^ 40 * 1237600 * 2
def baseEnd_1237600 : Nat := 635483658004463118008387

theorem tailTrace_1237600 : CollatzResearch.WordTrace tailWord_1237600 prefixEnd_1237600 635483658004463118008387 := by
  unfold tailWord_1237600
  simp only [CollatzResearch.WordTrace]
  refine ⟨22569490158197020048731127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30092653544262693398308169 22569490158197020048731127)
  ·
    refine ⟨33854235237295530073096691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22569490158197020048731127 33854235237295530073096691)
    ·
      refine ⟨50781352855943295109645037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33854235237295530073096691 50781352855943295109645037)
      ·
        refine ⟨19043007320978735666116889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50781352855943295109645037 19043007320978735666116889)
        ·
          refine ⟨14282255490734051749587667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19043007320978735666116889 14282255490734051749587667)
          ·
            refine ⟨21423383236101077624381501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14282255490734051749587667 21423383236101077624381501)
            ·
              refine ⟨8033768713537904109143063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21423383236101077624381501 8033768713537904109143063)
              ·
                refine ⟨12050653070306856163714595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8033768713537904109143063 12050653070306856163714595)
                ·
                  refine ⟨18075979605460284245571893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12050653070306856163714595 18075979605460284245571893)
                  ·
                    refine ⟨1694623088011901648022365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18075979605460284245571893 1694623088011901648022365)
                    ·
                      refine ⟨635483658004463118008387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1694623088011901648022365 635483658004463118008387)
                      ·
                        rfl

theorem cell23_1237600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1237600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237600 prefixEnd_1237600 := by exact prefixLift 1237600
  have htrace : WordTrace (prefixWord ++ tailWord_1237600) baseStart_1237600 baseEnd_1237600 := by
    simpa [prefixWord, tailWord_1237600, baseEnd_1237600] using wordTrace_append hprefix tailTrace_1237600
  have hstable : (prefixWord ++ tailWord_1237600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237600).length < 2 ^ (prefixWord ++ tailWord_1237600).sum := by decide
  have hdescent : baseEnd_1237600 < baseStart_1237600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237657 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 2, 4, 2]
def baseStart_1237657 : Nat := 118140960795 + 1237657 * 2 ^ 59
def prefixEnd_1237657 : Nat := 4983230072969 + 3 ^ 40 * 1237657 * 2
def baseEnd_1237657 : Nat := 635512926401769394995625

theorem tailTrace_1237657 : CollatzResearch.WordTrace tailWord_1237657 prefixEnd_1237657 635512926401769394995625 := by
  unfold tailWord_1237657
  simp only [CollatzResearch.WordTrace]
  refine ⟨45141059277187538832287225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30094039518125025888191483 45141059277187538832287225)
  ·
    refine ⟨33855794457890654124215419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45141059277187538832287225 33855794457890654124215419)
    ·
      refine ⟨50783691686835981186323129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33855794457890654124215419 50783691686835981186323129)
      ·
        refine ⟨38087768765126985889742347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50783691686835981186323129 38087768765126985889742347)
        ·
          refine ⟨57131653147690478834613521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38087768765126985889742347 57131653147690478834613521)
          ·
            refine ⟨42848739860767859125960141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57131653147690478834613521 42848739860767859125960141)
            ·
              refine ⟨16068277447787947172235053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42848739860767859125960141 16068277447787947172235053)
              ·
                refine ⟨6025604042920480189588145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16068277447787947172235053 6025604042920480189588145)
                ·
                  refine ⟨4519203032190360142191109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6025604042920480189588145 4519203032190360142191109)
                  ·
                    refine ⟨847350568535692526660833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519203032190360142191109 847350568535692526660833)
                    ·
                      refine ⟨635512926401769394995625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847350568535692526660833 635512926401769394995625)
                      ·
                        rfl

theorem cell23_1237657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_1237657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237657 prefixEnd_1237657 := by exact prefixLift 1237657
  have htrace : WordTrace (prefixWord ++ tailWord_1237657) baseStart_1237657 baseEnd_1237657 := by
    simpa [prefixWord, tailWord_1237657, baseEnd_1237657] using wordTrace_append hprefix tailTrace_1237657
  have hstable : (prefixWord ++ tailWord_1237657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237657).length < 2 ^ (prefixWord ++ tailWord_1237657).sum := by decide
  have hdescent : baseEnd_1237657 < baseStart_1237657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237694 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1237694 : Nat := 118140960795 + 1237694 * 2 ^ 59
def prefixEnd_1237694 : Nat := 4983230072969 + 3 ^ 40 * 1237694 * 2
def baseEnd_1237694 : Nat := 635531925185985750232955

theorem tailTrace_1237694 : CollatzResearch.WordTrace tailWord_1237694 prefixEnd_1237694 635531925185985750232955 := by
  unfold tailWord_1237694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5642801097256686768923017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30094939185368996100922757 5642801097256686768923017)
  ·
    refine ⟨4232100822942515076692263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5642801097256686768923017 4232100822942515076692263)
    ·
      refine ⟨6348151234413772615038395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4232100822942515076692263 6348151234413772615038395)
      ·
        refine ⟨9522226851620658922557593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6348151234413772615038395 9522226851620658922557593)
        ·
          refine ⟨7141670138715494191918195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9522226851620658922557593 7141670138715494191918195)
          ·
            refine ⟨10712505208073241287877293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141670138715494191918195 10712505208073241287877293)
            ·
              refine ⟨4017189453027465482953985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10712505208073241287877293 4017189453027465482953985)
              ·
                refine ⟨3012892089770599112215489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4017189453027465482953985 3012892089770599112215489)
                ·
                  refine ⟨2259669067327949334161617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012892089770599112215489 2259669067327949334161617)
                  ·
                    refine ⟨1694751800495962000621213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2259669067327949334161617 1694751800495962000621213)
                    ·
                      refine ⟨635531925185985750232955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1694751800495962000621213 635531925185985750232955)
                      ·
                        rfl

theorem cell23_1237694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1237694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237694 prefixEnd_1237694 := by exact prefixLift 1237694
  have htrace : WordTrace (prefixWord ++ tailWord_1237694) baseStart_1237694 baseEnd_1237694 := by
    simpa [prefixWord, tailWord_1237694, baseEnd_1237694] using wordTrace_append hprefix tailTrace_1237694
  have hstable : (prefixWord ++ tailWord_1237694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237694).length < 2 ^ (prefixWord ++ tailWord_1237694).sum := by decide
  have hdescent : baseEnd_1237694 < baseStart_1237694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237714 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_1237714 : Nat := 118140960795 + 1237714 * 2 ^ 59
def prefixEnd_1237714 : Nat := 4983230072969 + 3 ^ 40 * 1237714 * 2
def baseEnd_1237714 : Nat := 70615799422119519109207

theorem tailTrace_1237714 : CollatzResearch.WordTrace tailWord_1237714 prefixEnd_1237714 70615799422119519109207 := by
  unfold tailWord_1237714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285784559495259391778049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30095425491987358378074797 11285784559495259391778049)
  ·
    refine ⟨8464338419621444543833537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11285784559495259391778049 8464338419621444543833537)
    ·
      refine ⟨6348253814716083407875153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8464338419621444543833537 6348253814716083407875153)
      ·
        refine ⟨4761190361037062555906365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6348253814716083407875153 4761190361037062555906365)
        ·
          refine ⟨1785446385388898458464887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4761190361037062555906365 1785446385388898458464887)
          ·
            refine ⟨2678169578083347687697331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785446385388898458464887 2678169578083347687697331)
            ·
              refine ⟨4017254367125021531545997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678169578083347687697331 4017254367125021531545997)
              ·
                refine ⟨1506470387671883074329749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4017254367125021531545997 1506470387671883074329749)
                ·
                  refine ⟨70615799422119519109207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1506470387671883074329749 70615799422119519109207)
                  ·
                    rfl

theorem cell23_1237714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_1237714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237714 prefixEnd_1237714 := by exact prefixLift 1237714
  have htrace : WordTrace (prefixWord ++ tailWord_1237714) baseStart_1237714 baseEnd_1237714 := by
    simpa [prefixWord, tailWord_1237714, baseEnd_1237714] using wordTrace_append hprefix tailTrace_1237714
  have hstable : (prefixWord ++ tailWord_1237714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237714).length < 2 ^ (prefixWord ++ tailWord_1237714).sum := by decide
  have hdescent : baseEnd_1237714 < baseStart_1237714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237727 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 3, 5]
def baseStart_1237727 : Nat := 118140960795 + 1237727 * 2 ^ 59
def prefixEnd_1237727 : Nat := 4983230072969 + 3 ^ 40 * 1237727 * 2
def baseEnd_1237727 : Nat := 211849623349194707040101

theorem tailTrace_1237727 : CollatzResearch.WordTrace tailWord_1237727 prefixEnd_1237727 211849623349194707040101 := by
  unfold tailWord_1237727
  simp only [CollatzResearch.WordTrace]
  refine ⟨45143612386933940787335435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30095741591289293858223623 45143612386933940787335435)
  ·
    refine ⟨67715418580400911181003153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45143612386933940787335435 67715418580400911181003153)
    ·
      refine ⟨50786563935300683385752365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67715418580400911181003153 50786563935300683385752365)
      ·
        refine ⟨19044961475737756269657137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50786563935300683385752365 19044961475737756269657137)
        ·
          refine ⟨14283721106803317202242853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19044961475737756269657137 14283721106803317202242853)
          ·
            refine ⟨2678197707525621975420535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14283721106803317202242853 2678197707525621975420535)
            ·
              refine ⟨4017296561288432963130803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678197707525621975420535 4017296561288432963130803)
              ·
                refine ⟨6025944841932649444696205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017296561288432963130803 6025944841932649444696205)
                ·
                  refine ⟨2259729315724743541761077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6025944841932649444696205 2259729315724743541761077)
                  ·
                    refine ⟨211849623349194707040101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2259729315724743541761077 211849623349194707040101)
                    ·
                      rfl

theorem cell23_1237727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_1237727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237727 prefixEnd_1237727 := by exact prefixLift 1237727
  have htrace : WordTrace (prefixWord ++ tailWord_1237727) baseStart_1237727 baseEnd_1237727 := by
    simpa [prefixWord, tailWord_1237727, baseEnd_1237727] using wordTrace_append hprefix tailTrace_1237727
  have hstable : (prefixWord ++ tailWord_1237727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237727).length < 2 ^ (prefixWord ++ tailWord_1237727).sum := by decide
  have hdescent : baseEnd_1237727 < baseStart_1237727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237744 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 1, 5]
def baseStart_1237744 : Nat := 118140960795 + 1237744 * 2 ^ 59
def prefixEnd_1237744 : Nat := 4983230072969 + 3 ^ 40 * 1237744 * 2
def baseEnd_1237744 : Nat := 211852533072903518202575

theorem tailTrace_1237744 : CollatzResearch.WordTrace tailWord_1237744 prefixEnd_1237744 211852533072903518202575 := by
  unfold tailWord_1237744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572116213936176345352143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30096154951914901793802857 22572116213936176345352143)
  ·
    refine ⟨33858174320904264518028215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22572116213936176345352143 33858174320904264518028215)
    ·
      refine ⟨50787261481356396777042323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33858174320904264518028215 50787261481356396777042323)
      ·
        refine ⟨76180892222034595165563485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50787261481356396777042323 76180892222034595165563485)
        ·
          refine ⟨28567834583262973187086307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76180892222034595165563485 28567834583262973187086307)
          ·
            refine ⟨42851751874894459780629461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28567834583262973187086307 42851751874894459780629461)
            ·
              refine ⟨1004337934567838901108503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42851751874894459780629461 1004337934567838901108503)
              ·
                refine ⟨1506506901851758351662755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004337934567838901108503 1506506901851758351662755)
                ·
                  refine ⟨2259760352777637527494133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506506901851758351662755 2259760352777637527494133)
                  ·
                    refine ⟨211852533072903518202575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2259760352777637527494133 211852533072903518202575)
                    ·
                      rfl

theorem cell23_1237744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_1237744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237744 prefixEnd_1237744 := by exact prefixLift 1237744
  have htrace : WordTrace (prefixWord ++ tailWord_1237744) baseStart_1237744 baseEnd_1237744 := by
    simpa [prefixWord, tailWord_1237744, baseEnd_1237744] using wordTrace_append hprefix tailTrace_1237744
  have hstable : (prefixWord ++ tailWord_1237744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237744).length < 2 ^ (prefixWord ++ tailWord_1237744).sum := by decide
  have hdescent : baseEnd_1237744 < baseStart_1237744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237748 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1237748 : Nat := 118140960795 + 1237748 * 2 ^ 59
def prefixEnd_1237748 : Nat := 4983230072969 + 3 ^ 40 * 1237748 * 2
def baseEnd_1237748 : Nat := 70617739237925393217523

theorem tailTrace_1237748 : CollatzResearch.WordTrace tailWord_1237748 prefixEnd_1237748 70617739237925393217523 := by
  unfold tailWord_1237748
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572189159928930686924949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30096252213238574249233265 22572189159928930686924949)
  ·
    refine ⟨1058071366871668625949607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22572189159928930686924949 1058071366871668625949607)
    ·
      refine ⟨1587107050307502938924411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058071366871668625949607 1587107050307502938924411)
      ·
        refine ⟨2380660575461254408386617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587107050307502938924411 2380660575461254408386617)
        ·
          refine ⟨1785495431595940806289963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380660575461254408386617 1785495431595940806289963)
          ·
            refine ⟨2678243147393911209434945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785495431595940806289963 2678243147393911209434945)
            ·
              refine ⟨2008682360545433407076209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678243147393911209434945 2008682360545433407076209)
              ·
                refine ⟨1506511770409075055307157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008682360545433407076209 1506511770409075055307157)
                ·
                  refine ⟨70617739237925393217523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1506511770409075055307157 70617739237925393217523)
                  ·
                    rfl

theorem cell23_1237748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1237748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237748 prefixEnd_1237748 := by exact prefixLift 1237748
  have htrace : WordTrace (prefixWord ++ tailWord_1237748) baseStart_1237748 baseEnd_1237748 := by
    simpa [prefixWord, tailWord_1237748, baseEnd_1237748] using wordTrace_append hprefix tailTrace_1237748
  have hstable : (prefixWord ++ tailWord_1237748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237748).length < 2 ^ (prefixWord ++ tailWord_1237748).sum := by decide
  have hdescent : baseEnd_1237748 < baseStart_1237748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237777 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_1237777 : Nat := 118140960795 + 1237777 * 2 ^ 59
def prefixEnd_1237777 : Nat := 4983230072969 + 3 ^ 40 * 1237777 * 2
def baseEnd_1237777 : Nat := 635574544080308925495073

theorem tailTrace_1237777 : CollatzResearch.WordTrace tailWord_1237777 prefixEnd_1237777 635574544080308925495073 := by
  unfold tailWord_1237777
  simp only [CollatzResearch.WordTrace]
  refine ⟨45145436036752799326655585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30096957357835199551103723 45145436036752799326655585)
  ·
    refine ⟨33859077027564599494991689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45145436036752799326655585 33859077027564599494991689)
    ·
      refine ⟨25394307770673449621243767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33859077027564599494991689 25394307770673449621243767)
      ·
        refine ⟨38091461656010174431865651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25394307770673449621243767 38091461656010174431865651)
        ·
          refine ⟨57137192484015261647798477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38091461656010174431865651 57137192484015261647798477)
          ·
            refine ⟨21426447181505723117924429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57137192484015261647798477 21426447181505723117924429)
            ·
              refine ⟨8034917693064646169221661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21426447181505723117924429 8034917693064646169221661)
              ·
                refine ⟨3013094134899242313458123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8034917693064646169221661 3013094134899242313458123)
                ·
                  refine ⟨4519641202348863470187185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013094134899242313458123 4519641202348863470187185)
                  ·
                    refine ⟨3389730901761647602640389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519641202348863470187185 3389730901761647602640389)
                    ·
                      refine ⟨635574544080308925495073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3389730901761647602640389 635574544080308925495073)
                      ·
                        rfl

theorem cell23_1237777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_1237777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237777 prefixEnd_1237777 := by exact prefixLift 1237777
  have htrace : WordTrace (prefixWord ++ tailWord_1237777) baseStart_1237777 baseEnd_1237777 := by
    simpa [prefixWord, tailWord_1237777, baseEnd_1237777] using wordTrace_append hprefix tailTrace_1237777
  have hstable : (prefixWord ++ tailWord_1237777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237777).length < 2 ^ (prefixWord ++ tailWord_1237777).sum := by decide
  have hdescent : baseEnd_1237777 < baseStart_1237777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237781 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_1237781 : Nat := 118140960795 + 1237781 * 2 ^ 59
def prefixEnd_1237781 : Nat := 4983230072969 + 3 ^ 40 * 1237781 * 2
def baseEnd_1237781 : Nat := 635576598002926909845055

theorem tailTrace_1237781 : CollatzResearch.WordTrace tailWord_1237781 prefixEnd_1237781 635576598002926909845055 := by
  unfold tailWord_1237781
  simp only [CollatzResearch.WordTrace]
  refine ⟨45145581928738308009801197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30097054619158872006534131 45145581928738308009801197)
  ·
    refine ⟨16929593223276865503675449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45145581928738308009801197 16929593223276865503675449)
    ·
      refine ⟨12697194917457649127756587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16929593223276865503675449 12697194917457649127756587)
      ·
        refine ⟨19045792376186473691634881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12697194917457649127756587 19045792376186473691634881)
        ·
          refine ⟨14284344282139855268726161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19045792376186473691634881 14284344282139855268726161)
          ·
            refine ⟨10713258211604891451544621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14284344282139855268726161 10713258211604891451544621)
            ·
              refine ⟨4017471829351834294329233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10713258211604891451544621 4017471829351834294329233)
              ·
                refine ⟨3013103872013875720746925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4017471829351834294329233 3013103872013875720746925)
                ·
                  refine ⟨1129913952005203395280097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3013103872013875720746925 1129913952005203395280097)
                  ·
                    refine ⟨847435464003902546460073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1129913952005203395280097 847435464003902546460073)
                    ·
                      refine ⟨635576598002926909845055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847435464003902546460073 635576598002926909845055)
                      ·
                        rfl

theorem cell23_1237781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_1237781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237781 prefixEnd_1237781 := by exact prefixLift 1237781
  have htrace : WordTrace (prefixWord ++ tailWord_1237781) baseStart_1237781 baseEnd_1237781 := by
    simpa [prefixWord, tailWord_1237781, baseEnd_1237781] using wordTrace_append hprefix tailTrace_1237781
  have hstable : (prefixWord ++ tailWord_1237781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237781).length < 2 ^ (prefixWord ++ tailWord_1237781).sum := by decide
  have hdescent : baseEnd_1237781 < baseStart_1237781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237784 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1237784 : Nat := 118140960795 + 1237784 * 2 ^ 59
def prefixEnd_1237784 : Nat := 4983230072969 + 3 ^ 40 * 1237784 * 2
def baseEnd_1237784 : Nat := 635578138444890398107541

theorem tailTrace_1237784 : CollatzResearch.WordTrace tailWord_1237784 prefixEnd_1237784 635578138444890398107541 := by
  unfold tailWord_1237784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572845673863719761080203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30097127565151626348106937 22572845673863719761080203)
  ·
    refine ⟨33859268510795579641620305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22572845673863719761080203 33859268510795579641620305)
    ·
      refine ⟨25394451383096684731215229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33859268510795579641620305 25394451383096684731215229)
      ·
        refine ⟨9522919268661256774205711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25394451383096684731215229 9522919268661256774205711)
        ·
          refine ⟨14284378902991885161308567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522919268661256774205711 14284378902991885161308567)
          ·
            refine ⟨21426568354487827741962851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14284378902991885161308567 21426568354487827741962851)
            ·
              refine ⟨32139852531731741612944277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21426568354487827741962851 32139852531731741612944277)
              ·
                refine ⟨1506555587424925388106763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32139852531731741612944277 1506555587424925388106763)
                ·
                  refine ⟨2259833381137388082160145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506555587424925388106763 2259833381137388082160145)
                  ·
                    refine ⟨1694875035853041061620109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2259833381137388082160145 1694875035853041061620109)
                    ·
                      refine ⟨635578138444890398107541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1694875035853041061620109 635578138444890398107541)
                      ·
                        rfl

theorem cell23_1237784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1237784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237784 prefixEnd_1237784 := by exact prefixLift 1237784
  have htrace : WordTrace (prefixWord ++ tailWord_1237784) baseStart_1237784 baseEnd_1237784 := by
    simpa [prefixWord, tailWord_1237784, baseEnd_1237784] using wordTrace_append hprefix tailTrace_1237784
  have hstable : (prefixWord ++ tailWord_1237784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237784).length < 2 ^ (prefixWord ++ tailWord_1237784).sum := by decide
  have hdescent : baseEnd_1237784 < baseStart_1237784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237794 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1237794 : Nat := 118140960795 + 1237794 * 2 ^ 59
def prefixEnd_1237794 : Nat := 4983230072969 + 3 ^ 40 * 1237794 * 2
def baseEnd_1237794 : Nat := 635583273251435358982495

theorem tailTrace_1237794 : CollatzResearch.WordTrace tailWord_1237794 prefixEnd_1237794 635583273251435358982495 := by
  unfold tailWord_1237794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11286514019422802807506109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30097370718460807486682957 11286514019422802807506109)
  ·
    refine ⟨4232442757283551052814791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11286514019422802807506109 4232442757283551052814791)
    ·
      refine ⟨6348664135925326579222187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4232442757283551052814791 6348664135925326579222187)
      ·
        refine ⟨9522996203887989868833281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6348664135925326579222187 9522996203887989868833281)
        ·
          refine ⟨7142247152915992401624961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9522996203887989868833281 7142247152915992401624961)
          ·
            refine ⟨5356685364686994301218721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7142247152915992401624961 5356685364686994301218721)
            ·
              refine ⟨4017514023515245725914041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5356685364686994301218721 4017514023515245725914041)
              ·
                refine ⟨3013135517636434294435531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4017514023515245725914041 3013135517636434294435531)
                ·
                  refine ⟨4519703276454651441653297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013135517636434294435531 4519703276454651441653297)
                  ·
                    refine ⟨3389777457340988581239973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519703276454651441653297 3389777457340988581239973)
                    ·
                      refine ⟨635583273251435358982495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3389777457340988581239973 635583273251435358982495)
                      ·
                        rfl

theorem cell23_1237794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1237794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237794 prefixEnd_1237794 := by exact prefixLift 1237794
  have htrace : WordTrace (prefixWord ++ tailWord_1237794) baseStart_1237794 baseEnd_1237794 := by
    simpa [prefixWord, tailWord_1237794, baseEnd_1237794] using wordTrace_append hprefix tailTrace_1237794
  have hstable : (prefixWord ++ tailWord_1237794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237794).length < 2 ^ (prefixWord ++ tailWord_1237794).sum := by decide
  have hdescent : baseEnd_1237794 < baseStart_1237794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237824 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2]
def baseStart_1237824 : Nat := 118140960795 + 1237824 * 2 ^ 59
def prefixEnd_1237824 : Nat := 4983230072969 + 3 ^ 40 * 1237824 * 2
def baseEnd_1237824 : Nat := 635598677671070241607357

theorem tailTrace_1237824 : CollatzResearch.WordTrace tailWord_1237824 prefixEnd_1237824 635598677671070241607357 := by
  unfold tailWord_1237824
  simp only [CollatzResearch.WordTrace]
  refine ⟨22573575133791263176808263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30098100178388350902411017 22573575133791263176808263)
  ·
    refine ⟨33860362700686894765212395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22573575133791263176808263 33860362700686894765212395)
    ·
      refine ⟨50790544051030342147818593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33860362700686894765212395 50790544051030342147818593)
      ·
        refine ⟨38092908038272756610863945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50790544051030342147818593 38092908038272756610863945)
        ·
          refine ⟨28569681028704567458147959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38092908038272756610863945 28569681028704567458147959)
          ·
            refine ⟨42854521543056851187221939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28569681028704567458147959 42854521543056851187221939)
            ·
              refine ⟨64281782314585276780832909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42854521543056851187221939 64281782314585276780832909)
              ·
                refine ⟨24105668367969478792812341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64281782314585276780832909 24105668367969478792812341)
                ·
                  refine ⟨2259906409497138636826157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24105668367969478792812341 2259906409497138636826157)
                  ·
                    refine ⟨847464903561426988809809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259906409497138636826157 847464903561426988809809)
                    ·
                      refine ⟨635598677671070241607357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847464903561426988809809 635598677671070241607357)
                      ·
                        rfl

theorem cell23_1237824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_1237824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237824 prefixEnd_1237824 := by exact prefixLift 1237824
  have htrace : WordTrace (prefixWord ++ tailWord_1237824) baseStart_1237824 baseEnd_1237824 := by
    simpa [prefixWord, tailWord_1237824, baseEnd_1237824] using wordTrace_append hprefix tailTrace_1237824
  have hstable : (prefixWord ++ tailWord_1237824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237824).length < 2 ^ (prefixWord ++ tailWord_1237824).sum := by decide
  have hdescent : baseEnd_1237824 < baseStart_1237824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237825 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1237825 : Nat := 118140960795 + 1237825 * 2 ^ 59
def prefixEnd_1237825 : Nat := 4983230072969 + 3 ^ 40 * 1237825 * 2
def baseEnd_1237825 : Nat := 211866397050574912564951

theorem tailTrace_1237825 : CollatzResearch.WordTrace tailWord_1237825 prefixEnd_1237825 211866397050574912564951 := by
  unfold tailWord_1237825
  simp only [CollatzResearch.WordTrace]
  refine ⟨45147186740578903524402929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30098124493719269016268619 45147186740578903524402929)
  ·
    refine ⟨33860390055434177643302197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45147186740578903524402929 33860390055434177643302197)
    ·
      refine ⟨3174411567696954154059581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33860390055434177643302197 3174411567696954154059581)
      ·
        refine ⟨1190404337886357807772343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3174411567696954154059581 1190404337886357807772343)
        ·
          refine ⟨1785606506829536711658515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190404337886357807772343 1785606506829536711658515)
          ·
            refine ⟨2678409760244305067487773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785606506829536711658515 2678409760244305067487773)
            ·
              refine ⟨1004403660091614400307915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2678409760244305067487773 1004403660091614400307915)
              ·
                refine ⟨1506605490137421600461873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004403660091614400307915 1506605490137421600461873)
                ·
                  refine ⟨1129954117603066200346405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1506605490137421600461873 1129954117603066200346405)
                  ·
                    refine ⟨211866397050574912564951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129954117603066200346405 211866397050574912564951)
                    ·
                      rfl

theorem cell23_1237825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1237825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237825 prefixEnd_1237825 := by exact prefixLift 1237825
  have htrace : WordTrace (prefixWord ++ tailWord_1237825) baseStart_1237825 baseEnd_1237825 := by
    simpa [prefixWord, tailWord_1237825, baseEnd_1237825] using wordTrace_append hprefix tailTrace_1237825
  have hstable : (prefixWord ++ tailWord_1237825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237825).length < 2 ^ (prefixWord ++ tailWord_1237825).sum := by decide
  have hdescent : baseEnd_1237825 < baseStart_1237825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237867 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_1237867 : Nat := 118140960795 + 1237867 * 2 ^ 59
def prefixEnd_1237867 : Nat := 4983230072969 + 3 ^ 40 * 1237867 * 2
def baseEnd_1237867 : Nat := 635620757339213573369659

theorem tailTrace_1237867 : CollatzResearch.WordTrace tailWord_1237867 prefixEnd_1237867 635620757339213573369659 := by
  unfold tailWord_1237867
  simp only [CollatzResearch.WordTrace]
  refine ⟨45148718606426744697431855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30099145737617829798287903 45148718606426744697431855)
  ·
    refine ⟨67723077909640117046147783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45148718606426744697431855 67723077909640117046147783)
    ·
      refine ⟨101584616864460175569221675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67723077909640117046147783 101584616864460175569221675)
      ·
        refine ⟨152376925296690263353832513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101584616864460175569221675 152376925296690263353832513)
        ·
          refine ⟨114282693972517697515374385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152376925296690263353832513 114282693972517697515374385)
          ·
            refine ⟨85712020479388273136530789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114282693972517697515374385 85712020479388273136530789)
            ·
              refine ⟨16071003839885301213099523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85712020479388273136530789 16071003839885301213099523)
              ·
                refine ⟨24106505759827951819649285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16071003839885301213099523 24106505759827951819649285)
                ·
                  refine ⟨4519969829967740966184241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24106505759827951819649285 4519969829967740966184241)
                  ·
                    refine ⟨3389977372475805724638181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4519969829967740966184241 3389977372475805724638181)
                    ·
                      refine ⟨635620757339213573369659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3389977372475805724638181 635620757339213573369659)
                      ·
                        rfl

theorem cell23_1237867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_1237867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237867 prefixEnd_1237867 := by exact prefixLift 1237867
  have htrace : WordTrace (prefixWord ++ tailWord_1237867) baseStart_1237867 baseEnd_1237867 := by
    simpa [prefixWord, tailWord_1237867, baseEnd_1237867] using wordTrace_append hprefix tailTrace_1237867
  have hstable : (prefixWord ++ tailWord_1237867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237867).length < 2 ^ (prefixWord ++ tailWord_1237867).sum := by decide
  have hdescent : baseEnd_1237867 < baseStart_1237867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237924 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1237924 : Nat := 118140960795 + 1237924 * 2 ^ 59
def prefixEnd_1237924 : Nat := 4983230072969 + 3 ^ 40 * 1237924 * 2
def baseEnd_1237924 : Nat := 211883341912173283452299

theorem tailTrace_1237924 : CollatzResearch.WordTrace tailWord_1237924 prefixEnd_1237924 211883341912173283452299 := by
  unfold tailWord_1237924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575398783610121716128413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30100531711480162288171217 22575398783610121716128413)
  ·
    refine ⟨8465774543853795643548155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22575398783610121716128413 8465774543853795643548155)
    ·
      refine ⟨12698661815780693465322233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8465774543853795643548155 12698661815780693465322233)
      ·
        refine ⟨9523996361835520098991675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12698661815780693465322233 9523996361835520098991675)
        ·
          refine ⟨14285994542753280148487513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9523996361835520098991675 14285994542753280148487513)
          ·
            refine ⟨10714495907064960111365635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14285994542753280148487513 10714495907064960111365635)
            ·
              refine ⟨16071743860597440167048453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10714495907064960111365635 16071743860597440167048453)
              ·
                refine ⟨3013451973862020031321585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16071743860597440167048453 3013451973862020031321585)
                ·
                  refine ⟨2260088980396515023491189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3013451973862020031321585 2260088980396515023491189)
                  ·
                    refine ⟨211883341912173283452299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2260088980396515023491189 211883341912173283452299)
                    ·
                      rfl

theorem cell23_1237924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1237924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237924 prefixEnd_1237924 := by exact prefixLift 1237924
  have htrace : WordTrace (prefixWord ++ tailWord_1237924) baseStart_1237924 baseEnd_1237924 := by
    simpa [prefixWord, tailWord_1237924, baseEnd_1237924] using wordTrace_append hprefix tailTrace_1237924
  have hstable : (prefixWord ++ tailWord_1237924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237924).length < 2 ^ (prefixWord ++ tailWord_1237924).sum := by decide
  have hdescent : baseEnd_1237924 < baseStart_1237924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1237947 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_1237947 : Nat := 118140960795 + 1237947 * 2 ^ 59
def prefixEnd_1237947 : Nat := 4983230072969 + 3 ^ 40 * 1237947 * 2
def baseEnd_1237947 : Nat := 635661835791573260369291

theorem tailTrace_1237947 : CollatzResearch.WordTrace tailWord_1237947 prefixEnd_1237947 635661835791573260369291 := by
  unfold tailWord_1237947
  simp only [CollatzResearch.WordTrace]
  refine ⟨45151636446136918360344095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30101090964091278906896063 45151636446136918360344095)
  ·
    refine ⟨67727454669205377540516143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45151636446136918360344095 67727454669205377540516143)
    ·
      refine ⟨101591182003808066310774215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67727454669205377540516143 101591182003808066310774215)
      ·
        refine ⟨152386773005712099466161323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101591182003808066310774215 152386773005712099466161323)
        ·
          refine ⟨228580159508568149199241985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152386773005712099466161323 228580159508568149199241985)
          ·
            refine ⟨171435119631426111899431489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228580159508568149199241985 171435119631426111899431489)
            ·
              refine ⟨128576339723569583924573617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171435119631426111899431489 128576339723569583924573617)
              ·
                refine ⟨96432254792677187943430213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128576339723569583924573617 96432254792677187943430213)
                ·
                  refine ⟨18081047773626972739393165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96432254792677187943430213 18081047773626972739393165)
                  ·
                    refine ⟨6780392915110114777272437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18081047773626972739393165 6780392915110114777272437)
                    ·
                      refine ⟨635661835791573260369291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6780392915110114777272437 635661835791573260369291)
                      ·
                        rfl

theorem cell23_1237947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_1237947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1237947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1237947 prefixEnd_1237947 := by exact prefixLift 1237947
  have htrace : WordTrace (prefixWord ++ tailWord_1237947) baseStart_1237947 baseEnd_1237947 := by
    simpa [prefixWord, tailWord_1237947, baseEnd_1237947] using wordTrace_append hprefix tailTrace_1237947
  have hstable : (prefixWord ++ tailWord_1237947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1237947).length < 2 ^ (prefixWord ++ tailWord_1237947).sum := by decide
  have hdescent : baseEnd_1237947 < baseStart_1237947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1237947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238021 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_1238021 : Nat := 118140960795 + 1238021 * 2 ^ 59
def prefixEnd_1238021 : Nat := 4983230072969 + 3 ^ 40 * 1238021 * 2
def baseEnd_1238021 : Nat := 635699833360005970843951

theorem tailTrace_1238021 : CollatzResearch.WordTrace tailWord_1238021 prefixEnd_1238021 635699833360005970843951 := by
  unfold tailWord_1238021
  simp only [CollatzResearch.WordTrace]
  refine ⟨45154335447868828998537917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30102890298579219332358611 45154335447868828998537917)
  ·
    refine ⟨16932875792950810874451719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45154335447868828998537917 16932875792950810874451719)
    ·
      refine ⟨25399313689426216311677579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16932875792950810874451719 25399313689426216311677579)
      ·
        refine ⟨38098970534139324467516369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25399313689426216311677579 38098970534139324467516369)
        ·
          refine ⟨28574227900604493350637277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38098970534139324467516369 28574227900604493350637277)
          ·
            refine ⟨10715335462726685006488979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28574227900604493350637277 10715335462726685006488979)
            ·
              refine ⟨16073003194090027509733469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715335462726685006488979 16073003194090027509733469)
              ·
                refine ⟨6027376197783760316150051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16073003194090027509733469 6027376197783760316150051)
                ·
                  refine ⟨9041064296675640474225077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027376197783760316150051 9041064296675640474225077)
                  ·
                    refine ⟨847599777813341294458601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9041064296675640474225077 847599777813341294458601)
                    ·
                      refine ⟨635699833360005970843951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847599777813341294458601 635699833360005970843951)
                      ·
                        rfl

theorem cell23_1238021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_1238021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238021 prefixEnd_1238021 := by exact prefixLift 1238021
  have htrace : WordTrace (prefixWord ++ tailWord_1238021) baseStart_1238021 baseEnd_1238021 := by
    simpa [prefixWord, tailWord_1238021, baseEnd_1238021] using wordTrace_append hprefix tailTrace_1238021
  have hstable : (prefixWord ++ tailWord_1238021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238021).length < 2 ^ (prefixWord ++ tailWord_1238021).sum := by decide
  have hdescent : baseEnd_1238021 < baseStart_1238021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238064 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_1238064 : Nat := 118140960795 + 1238064 * 2 ^ 59
def prefixEnd_1238064 : Nat := 4983230072969 + 3 ^ 40 * 1238064 * 2
def baseEnd_1238064 : Nat := 635721913028149302606253

theorem tailTrace_1238064 : CollatzResearch.WordTrace tailWord_1238064 prefixEnd_1238064 635721913028149302606253 := by
  unfold tailWord_1238064
  simp only [CollatzResearch.WordTrace]
  refine ⟨22577951893356523671176623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30103935857808698228235497 22577951893356523671176623)
  ·
    refine ⟨33866927840034785506764935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22577951893356523671176623 33866927840034785506764935)
    ·
      refine ⟨50800391760052178260147403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33866927840034785506764935 50800391760052178260147403)
      ·
        refine ⟨76200587640078267390221105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50800391760052178260147403 76200587640078267390221105)
        ·
          refine ⟨57150440730058700542665829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76200587640078267390221105 57150440730058700542665829)
          ·
            refine ⟨10715707636886006351749843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57150440730058700542665829 10715707636886006351749843)
            ·
              refine ⟨16073561455329009527624765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715707636886006351749843 16073561455329009527624765)
              ·
                refine ⟨6027585545748378572859287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16073561455329009527624765 6027585545748378572859287)
                ·
                  refine ⟨9041378318622567859288931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6027585545748378572859287 9041378318622567859288931)
                  ·
                    refine ⟨13562067477933851788933397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9041378318622567859288931 13562067477933851788933397)
                    ·
                      refine ⟨635721913028149302606253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13562067477933851788933397 635721913028149302606253)
                      ·
                        rfl

theorem cell23_1238064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_1238064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238064 prefixEnd_1238064 := by exact prefixLift 1238064
  have htrace : WordTrace (prefixWord ++ tailWord_1238064) baseStart_1238064 baseEnd_1238064 := by
    simpa [prefixWord, tailWord_1238064, baseEnd_1238064] using wordTrace_append hprefix tailTrace_1238064
  have hstable : (prefixWord ++ tailWord_1238064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238064).length < 2 ^ (prefixWord ++ tailWord_1238064).sum := by decide
  have hdescent : baseEnd_1238064 < baseStart_1238064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238074 : List Nat := [3, 1, 1, 1, 3, 1, 4, 9]
def baseStart_1238074 : Nat := 118140960795 + 1238074 * 2 ^ 59
def prefixEnd_1238074 : Nat := 4983230072969 + 3 ^ 40 * 1238074 * 2
def baseEnd_1238074 : Nat := 23545446216099787536341

theorem tailTrace_1238074 : CollatzResearch.WordTrace tailWord_1238074 prefixEnd_1238074 23545446216099787536341 := by
  unfold tailWord_1238074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289067129169204762554319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30104179011117879366811517 11289067129169204762554319)
  ·
    refine ⟨16933600693753807143831479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11289067129169204762554319 16933600693753807143831479)
    ·
      refine ⟨25400401040630710715747219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16933600693753807143831479 25400401040630710715747219)
      ·
        refine ⟨38100601560946066073620829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25400401040630710715747219 38100601560946066073620829)
        ·
          refine ⟨14287725585354774777607811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38100601560946066073620829 14287725585354774777607811)
          ·
            refine ⟨21431588378032162166411717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14287725585354774777607811 21431588378032162166411717)
            ·
              refine ⟨4018422820881030406202197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21431588378032162166411717 4018422820881030406202197)
              ·
                refine ⟨23545446216099787536341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4018422820881030406202197 23545446216099787536341)
                ·
                  rfl

theorem cell23_1238074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_1238074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238074 prefixEnd_1238074 := by exact prefixLift 1238074
  have htrace : WordTrace (prefixWord ++ tailWord_1238074) baseStart_1238074 baseEnd_1238074 := by
    simpa [prefixWord, tailWord_1238074, baseEnd_1238074] using wordTrace_append hprefix tailTrace_1238074
  have hstable : (prefixWord ++ tailWord_1238074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238074).length < 2 ^ (prefixWord ++ tailWord_1238074).sum := by decide
  have hdescent : baseEnd_1238074 < baseStart_1238074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238078 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1238078 : Nat := 118140960795 + 1238078 * 2 ^ 59
def prefixEnd_1238078 : Nat := 4983230072969 + 3 ^ 40 * 1238078 * 2
def baseEnd_1238078 : Nat := 211909700585770749277063

theorem tailTrace_1238078 : CollatzResearch.WordTrace tailWord_1238078 prefixEnd_1238078 211909700585770749277063 := by
  unfold tailWord_1238078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644551801082790966670361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30104276272441551822241925 5644551801082790966670361)
  ·
    refine ⟨4233413850812093225002771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5644551801082790966670361 4233413850812093225002771)
    ·
      refine ⟨6350120776218139837504157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4233413850812093225002771 6350120776218139837504157)
      ·
        refine ⟨2381295291081802439064059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6350120776218139837504157 2381295291081802439064059)
        ·
          refine ⟨3571942936622703658596089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381295291081802439064059 3571942936622703658596089)
          ·
            refine ⟨2678957202467027743947067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3571942936622703658596089 2678957202467027743947067)
            ·
              refine ⟨4018435803700541615920601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678957202467027743947067 4018435803700541615920601)
              ·
                refine ⟨3013826852775406211940451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018435803700541615920601 3013826852775406211940451)
                ·
                  refine ⟨4520740279163109317910677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013826852775406211940451 4520740279163109317910677)
                  ·
                    refine ⟨211909700585770749277063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4520740279163109317910677 211909700585770749277063)
                    ·
                      rfl

theorem cell23_1238078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1238078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238078 prefixEnd_1238078 := by exact prefixLift 1238078
  have htrace : WordTrace (prefixWord ++ tailWord_1238078) baseStart_1238078 baseEnd_1238078 := by
    simpa [prefixWord, tailWord_1238078, baseEnd_1238078] using wordTrace_append hprefix tailTrace_1238078
  have hstable : (prefixWord ++ tailWord_1238078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238078).length < 2 ^ (prefixWord ++ tailWord_1238078).sum := by decide
  have hdescent : baseEnd_1238078 < baseStart_1238078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238101 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1238101 : Nat := 118140960795 + 1238101 * 2 ^ 59
def prefixEnd_1238101 : Nat := 4983230072969 + 3 ^ 40 * 1238101 * 2
def baseEnd_1238101 : Nat := 635740911812365657843583

theorem tailTrace_1238101 : CollatzResearch.WordTrace tailWord_1238101 prefixEnd_1238101 635740911812365657843583 := by
  unfold tailWord_1238101
  simp only [CollatzResearch.WordTrace]
  refine ⟨45157253287579002661450157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30104835525052668440966771 45157253287579002661450157)
  ·
    refine ⟨16933969982842125998043809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45157253287579002661450157 16933969982842125998043809)
    ·
      refine ⟨12700477487131594498532857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16933969982842125998043809 12700477487131594498532857)
      ·
        refine ⟨9525358115348695873899643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12700477487131594498532857 9525358115348695873899643)
        ·
          refine ⟨14288037173023043810849465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9525358115348695873899643 14288037173023043810849465)
          ·
            refine ⟨10716027879767282858137099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14288037173023043810849465 10716027879767282858137099)
            ·
              refine ⟨16074041819650924287205649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716027879767282858137099 16074041819650924287205649)
              ·
                refine ⟨12055531364738193215404237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16074041819650924287205649 12055531364738193215404237)
                ·
                  refine ⟨4520824261776822455776589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12055531364738193215404237 4520824261776822455776589)
                  ·
                    refine ⟨1695309098166308420916221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4520824261776822455776589 1695309098166308420916221)
                    ·
                      refine ⟨635740911812365657843583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1695309098166308420916221 635740911812365657843583)
                      ·
                        rfl

theorem cell23_1238101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1238101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238101 prefixEnd_1238101 := by exact prefixLift 1238101
  have htrace : WordTrace (prefixWord ++ tailWord_1238101) baseStart_1238101 baseEnd_1238101 := by
    simpa [prefixWord, tailWord_1238101, baseEnd_1238101] using wordTrace_append hprefix tailTrace_1238101
  have hstable : (prefixWord ++ tailWord_1238101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238101).length < 2 ^ (prefixWord ++ tailWord_1238101).sum := by decide
  have hdescent : baseEnd_1238101 < baseStart_1238101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238104 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1238104 : Nat := 118140960795 + 1238104 * 2 ^ 59
def prefixEnd_1238104 : Nat := 4983230072969 + 3 ^ 40 * 1238104 * 2
def baseEnd_1238104 : Nat := 211914150751443048702023

theorem tailTrace_1238104 : CollatzResearch.WordTrace tailWord_1238104 prefixEnd_1238104 211914150751443048702023 := by
  unfold tailWord_1238104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22578681353284067086904683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30104908471045422782539577 22578681353284067086904683)
  ·
    refine ⟨33868022029926100630357025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22578681353284067086904683 33868022029926100630357025)
    ·
      refine ⟨25401016522444575472767769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33868022029926100630357025 25401016522444575472767769)
      ·
        refine ⟨19050762391833431604575827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25401016522444575472767769 19050762391833431604575827)
        ·
          refine ⟨28576143587750147406863741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19050762391833431604575827 28576143587750147406863741)
          ·
            refine ⟨10716053845406305277573903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28576143587750147406863741 10716053845406305277573903)
            ·
              refine ⟨16074080768109457916360855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716053845406305277573903 16074080768109457916360855)
              ·
                refine ⟨24111121152164186874541283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16074080768109457916360855 24111121152164186874541283)
                ·
                  refine ⟨36166681728246280311811925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24111121152164186874541283 36166681728246280311811925)
                  ·
                    refine ⟨211914150751443048702023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 36166681728246280311811925 211914150751443048702023)
                    ·
                      rfl

theorem cell23_1238104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1238104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238104 prefixEnd_1238104 := by exact prefixLift 1238104
  have htrace : WordTrace (prefixWord ++ tailWord_1238104) baseStart_1238104 baseEnd_1238104 := by
    simpa [prefixWord, tailWord_1238104, baseEnd_1238104] using wordTrace_append hprefix tailTrace_1238104
  have hstable : (prefixWord ++ tailWord_1238104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238104).length < 2 ^ (prefixWord ++ tailWord_1238104).sum := by decide
  have hdescent : baseEnd_1238104 < baseStart_1238104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238128 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2]
def baseStart_1238128 : Nat := 118140960795 + 1238128 * 2 ^ 59
def prefixEnd_1238128 : Nat := 4983230072969 + 3 ^ 40 * 1238128 * 2
def baseEnd_1238128 : Nat := 635754775790037052205959

theorem tailTrace_1238128 : CollatzResearch.WordTrace tailWord_1238128 prefixEnd_1238128 635754775790037052205959 := by
  unfold tailWord_1238128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22579119029240593136341519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30105492038987457515122025 22579119029240593136341519)
  ·
    refine ⟨33868678543860889704512279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22579119029240593136341519 33868678543860889704512279)
    ·
      refine ⟨50803017815791334556768419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33868678543860889704512279 50803017815791334556768419)
      ·
        refine ⟨76204526723687001835152629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50803017815791334556768419 76204526723687001835152629)
        ·
          refine ⟨7144174380345656422045559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76204526723687001835152629 7144174380345656422045559)
          ·
            refine ⟨10716261570518484633068339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144174380345656422045559 10716261570518484633068339)
            ·
              refine ⟨16074392355777726949602509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10716261570518484633068339 16074392355777726949602509)
              ·
                refine ⟨6027897133416647606100941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16074392355777726949602509 6027897133416647606100941)
                ·
                  refine ⟨2260461425031242852287853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6027897133416647606100941 2260461425031242852287853)
                  ·
                    refine ⟨847673034386716069607945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260461425031242852287853 847673034386716069607945)
                    ·
                      refine ⟨635754775790037052205959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 847673034386716069607945 635754775790037052205959)
                      ·
                        rfl

theorem cell23_1238128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2].length) (baseStart_1238128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238128 prefixEnd_1238128 := by exact prefixLift 1238128
  have htrace : WordTrace (prefixWord ++ tailWord_1238128) baseStart_1238128 baseEnd_1238128 := by
    simpa [prefixWord, tailWord_1238128, baseEnd_1238128] using wordTrace_append hprefix tailTrace_1238128
  have hstable : (prefixWord ++ tailWord_1238128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238128).length < 2 ^ (prefixWord ++ tailWord_1238128).sum := by decide
  have hdescent : baseEnd_1238128 < baseStart_1238128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238181 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 7]
def baseStart_1238181 : Nat := 118140960795 + 1238181 * 2 ^ 59
def prefixEnd_1238181 : Nat := 4983230072969 + 3 ^ 40 * 1238181 * 2
def baseEnd_1238181 : Nat := 70642443362747260538135

theorem tailTrace_1238181 : CollatzResearch.WordTrace tailWord_1238181 prefixEnd_1238181 70642443362747260538135 := by
  unfold tailWord_1238181
  simp only [CollatzResearch.WordTrace]
  refine ⟨45160171127289176324362397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30106780751526117549574931 45160171127289176324362397)
  ·
    refine ⟨16935064172733441121635899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45160171127289176324362397 16935064172733441121635899)
    ·
      refine ⟨25402596259100161682453849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16935064172733441121635899 25402596259100161682453849)
      ·
        refine ⟨19051947194325121261840387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25402596259100161682453849 19051947194325121261840387)
        ·
          refine ⟨28577920791487681892760581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19051947194325121261840387 28577920791487681892760581)
          ·
            refine ⟨5358360148403940354892609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28577920791487681892760581 5358360148403940354892609)
            ·
              refine ⟨4018770111302955266169457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5358360148403940354892609 4018770111302955266169457)
              ·
                refine ⟨3014077583477216449627093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018770111302955266169457 3014077583477216449627093)
                ·
                  refine ⟨70642443362747260538135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3014077583477216449627093 70642443362747260538135)
                  ·
                    rfl

theorem cell23_1238181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_1238181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238181 prefixEnd_1238181 := by exact prefixLift 1238181
  have htrace : WordTrace (prefixWord ++ tailWord_1238181) baseStart_1238181 baseEnd_1238181 := by
    simpa [prefixWord, tailWord_1238181, baseEnd_1238181] using wordTrace_append hprefix tailTrace_1238181
  have hstable : (prefixWord ++ tailWord_1238181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238181).length < 2 ^ (prefixWord ++ tailWord_1238181).sum := by decide
  have hdescent : baseEnd_1238181 < baseStart_1238181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238191 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_1238191 : Nat := 118140960795 + 1238191 * 2 ^ 59
def prefixEnd_1238191 : Nat := 4983230072969 + 3 ^ 40 * 1238191 * 2
def baseEnd_1238191 : Nat := 635787125071270305718169

theorem tailTrace_1238191 : CollatzResearch.WordTrace tailWord_1238191 prefixEnd_1238191 635787125071270305718169 := by
  unfold tailWord_1238191
  simp only [CollatzResearch.WordTrace]
  refine ⟨45160535857252948032226427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30107023904835298688150951 45160535857252948032226427)
  ·
    refine ⟨67740803785879422048339641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45160535857252948032226427 67740803785879422048339641)
    ·
      refine ⟨50805602839409566536254731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67740803785879422048339641 50805602839409566536254731)
      ·
        refine ⟨76208404259114349804382097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50805602839409566536254731 76208404259114349804382097)
        ·
          refine ⟨57156303194335762353286573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76208404259114349804382097 57156303194335762353286573)
          ·
            refine ⟨21433613697875910882482465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57156303194335762353286573 21433613697875910882482465)
            ·
              refine ⟨16075210273406933161861849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21433613697875910882482465 16075210273406933161861849)
              ·
                refine ⟨12056407705055199871396387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16075210273406933161861849 12056407705055199871396387)
                ·
                  refine ⟨18084611557582799807094581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12056407705055199871396387 18084611557582799807094581)
                  ·
                    refine ⟨1695432333523387481915117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18084611557582799807094581 1695432333523387481915117)
                    ·
                      refine ⟨635787125071270305718169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1695432333523387481915117 635787125071270305718169)
                      ·
                        rfl

theorem cell23_1238191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_1238191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238191 prefixEnd_1238191 := by exact prefixLift 1238191
  have htrace : WordTrace (prefixWord ++ tailWord_1238191) baseStart_1238191 baseEnd_1238191 := by
    simpa [prefixWord, tailWord_1238191, baseEnd_1238191] using wordTrace_append hprefix tailTrace_1238191
  have hstable : (prefixWord ++ tailWord_1238191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238191).length < 2 ^ (prefixWord ++ tailWord_1238191).sum := by decide
  have hdescent : baseEnd_1238191 < baseStart_1238191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238231 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1238231 : Nat := 118140960795 + 1238231 * 2 ^ 59
def prefixEnd_1238231 : Nat := 4983230072969 + 3 ^ 40 * 1238231 * 2
def baseEnd_1238231 : Nat := 635807664297450149217985

theorem tailTrace_1238231 : CollatzResearch.WordTrace tailWord_1238231 prefixEnd_1238231 635807664297450149217985 := by
  unfold tailWord_1238231
  simp only [CollatzResearch.WordTrace]
  refine ⟨45161994777108034863682547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30107996518072023242455031 45161994777108034863682547)
  ·
    refine ⟨67742992165662052295523821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45161994777108034863682547 67742992165662052295523821)
    ·
      refine ⟨25403622062123269610821433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67742992165662052295523821 25403622062123269610821433)
      ·
        refine ⟨19052716546592452208116075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25403622062123269610821433 19052716546592452208116075)
        ·
          refine ⟨28579074819888678312174113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19052716546592452208116075 28579074819888678312174113)
          ·
            refine ⟨21434306114916508734130585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28579074819888678312174113 21434306114916508734130585)
            ·
              refine ⟨16075729586187381550597939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21434306114916508734130585 16075729586187381550597939)
              ·
                refine ⟨24113594379281072325896909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16075729586187381550597939 24113594379281072325896909)
                ·
                  refine ⟨9042597892230402122211341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24113594379281072325896909 9042597892230402122211341)
                  ·
                    refine ⟨3390974209586400795829253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9042597892230402122211341 3390974209586400795829253)
                    ·
                      refine ⟨635807664297450149217985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3390974209586400795829253 635807664297450149217985)
                      ·
                        rfl

theorem cell23_1238231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1238231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238231 prefixEnd_1238231 := by exact prefixLift 1238231
  have htrace : WordTrace (prefixWord ++ tailWord_1238231) baseStart_1238231 baseEnd_1238231 := by
    simpa [prefixWord, tailWord_1238231, baseEnd_1238231] using wordTrace_append hprefix tailTrace_1238231
  have hstable : (prefixWord ++ tailWord_1238231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238231).length < 2 ^ (prefixWord ++ tailWord_1238231).sum := by decide
  have hdescent : baseEnd_1238231 < baseStart_1238231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238245 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_1238245 : Nat := 118140960795 + 1238245 * 2 ^ 59
def prefixEnd_1238245 : Nat := 4983230072969 + 3 ^ 40 * 1238245 * 2
def baseEnd_1238245 : Nat := 211938284342204364814307

theorem tailTrace_1238245 : CollatzResearch.WordTrace tailWord_1238245 prefixEnd_1238245 211938284342204364814307 := by
  unfold tailWord_1238245
  simp only [CollatzResearch.WordTrace]
  refine ⟨45162505399057315254692189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30108336932704876836461459 45162505399057315254692189)
  ·
    refine ⟨16935939524646493220509571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45162505399057315254692189 16935939524646493220509571)
    ·
      refine ⟨25403909286969739830764357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16935939524646493220509571 25403909286969739830764357)
      ·
        refine ⟨4763232991306826218268317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25403909286969739830764357 4763232991306826218268317)
        ·
          refine ⟨1786212371740059831850619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4763232991306826218268317 1786212371740059831850619)
          ·
            refine ⟨2679318557610089747775929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786212371740059831850619 2679318557610089747775929)
            ·
              refine ⟨2009488918207567310831947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679318557610089747775929 2009488918207567310831947)
              ·
                refine ⟨3014233377311350966247921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009488918207567310831947 3014233377311350966247921)
                ·
                  refine ⟨2260675032983513224685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014233377311350966247921 2260675032983513224685941)
                  ·
                    refine ⟨211938284342204364814307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2260675032983513224685941 211938284342204364814307)
                    ·
                      rfl

theorem cell23_1238245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_1238245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238245 prefixEnd_1238245 := by exact prefixLift 1238245
  have htrace : WordTrace (prefixWord ++ tailWord_1238245) baseStart_1238245 baseEnd_1238245 := by
    simpa [prefixWord, tailWord_1238245, baseEnd_1238245] using wordTrace_append hprefix tailTrace_1238245
  have hstable : (prefixWord ++ tailWord_1238245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238245).length < 2 ^ (prefixWord ++ tailWord_1238245).sum := by decide
  have hdescent : baseEnd_1238245 < baseStart_1238245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238332 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_1238332 : Nat := 118140960795 + 1238332 * 2 ^ 59
def prefixEnd_1238332 : Nat := 4983230072969 + 3 ^ 40 * 1238332 * 2
def baseEnd_1238332 : Nat := 635859525843554254055021

theorem tailTrace_1238332 : CollatzResearch.WordTrace tailWord_1238332 prefixEnd_1238332 635859525843554254055021 := by
  unfold tailWord_1238332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582839274871064556554625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30110452366494752742072833 22582839274871064556554625)
  ·
    refine ⟨16937129456153298417415969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22582839274871064556554625 16937129456153298417415969)
    ·
      refine ⟨12702847092114973813061977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16937129456153298417415969 12702847092114973813061977)
      ·
        refine ⟨9527135319086230359796483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12702847092114973813061977 9527135319086230359796483)
        ·
          refine ⟨14290702978629345539694725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9527135319086230359796483 14290702978629345539694725)
          ·
            refine ⟨2679506808493002288692761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14290702978629345539694725 2679506808493002288692761)
            ·
              refine ⟨2009630106369751716519571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679506808493002288692761 2009630106369751716519571)
              ·
                refine ⟨3014445159554627574779357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009630106369751716519571 3014445159554627574779357)
                ·
                  refine ⟨1130416934832985340542259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3014445159554627574779357 1130416934832985340542259)
                  ·
                    refine ⟨1695625402249478010813389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1130416934832985340542259 1695625402249478010813389)
                    ·
                      refine ⟨635859525843554254055021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1695625402249478010813389 635859525843554254055021)
                      ·
                        rfl

theorem cell23_1238332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_1238332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238332 prefixEnd_1238332 := by exact prefixLift 1238332
  have htrace : WordTrace (prefixWord ++ tailWord_1238332) baseStart_1238332 baseEnd_1238332 := by
    simpa [prefixWord, tailWord_1238332, baseEnd_1238332] using wordTrace_append hprefix tailTrace_1238332
  have hstable : (prefixWord ++ tailWord_1238332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238332).length < 2 ^ (prefixWord ++ tailWord_1238332).sum := by decide
  have hdescent : baseEnd_1238332 < baseStart_1238332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238355 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 4]
def baseStart_1238355 : Nat := 118140960795 + 1238355 * 2 ^ 59
def prefixEnd_1238355 : Nat := 4983230072969 + 3 ^ 40 * 1238355 * 2
def baseEnd_1238355 : Nat := 635871335898607664067415

theorem tailTrace_1238355 : CollatzResearch.WordTrace tailWord_1238355 prefixEnd_1238355 635871335898607664067415 := by
  unfold tailWord_1238355
  simp only [CollatzResearch.WordTrace]
  refine ⟨45166517428658804041196519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30111011619105869360797679 45166517428658804041196519)
  ·
    refine ⟨67749776142988206061794779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45166517428658804041196519 67749776142988206061794779)
    ·
      refine ⟨101624664214482309092692169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67749776142988206061794779 101624664214482309092692169)
      ·
        refine ⟨76218498160861731819519127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101624664214482309092692169 76218498160861731819519127)
        ·
          refine ⟨114327747241292597729278691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76218498160861731819519127 114327747241292597729278691)
          ·
            refine ⟨171491620861938896593918037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114327747241292597729278691 171491620861938896593918037)
            ·
              refine ⟨2009667431975846444459977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 171491620861938896593918037 2009667431975846444459977)
              ·
                refine ⟨1507250573981884833344983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009667431975846444459977 1507250573981884833344983)
                ·
                  refine ⟨2260875860972827250017475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507250573981884833344983 2260875860972827250017475)
                  ·
                    refine ⟨3391313791459240875026213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2260875860972827250017475 3391313791459240875026213)
                    ·
                      refine ⟨635871335898607664067415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3391313791459240875026213 635871335898607664067415)
                      ·
                        rfl

theorem cell23_1238355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_1238355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238355 prefixEnd_1238355 := by exact prefixLift 1238355
  have htrace : WordTrace (prefixWord ++ tailWord_1238355) baseStart_1238355 baseEnd_1238355 := by
    simpa [prefixWord, tailWord_1238355, baseEnd_1238355] using wordTrace_append hprefix tailTrace_1238355
  have hstable : (prefixWord ++ tailWord_1238355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238355).length < 2 ^ (prefixWord ++ tailWord_1238355).sum := by decide
  have hdescent : baseEnd_1238355 < baseStart_1238355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238402 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1238402 : Nat := 118140960795 + 1238402 * 2 ^ 59
def prefixEnd_1238402 : Nat := 4983230072969 + 3 ^ 40 * 1238402 * 2
def baseEnd_1238402 : Nat := 635895469489368980179699

theorem tailTrace_1238402 : CollatzResearch.WordTrace tailWord_1238402 prefixEnd_1238402 635895469489368980179699 := by
  unfold tailWord_1238402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11292057914872132767039365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30112154439659020712104973 11292057914872132767039365)
  ·
    refine ⟨2117260859038524893819881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11292057914872132767039365 2117260859038524893819881)
    ·
      refine ⟨1587945644278893670364911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2117260859038524893819881 1587945644278893670364911)
      ·
        refine ⟨2381918466418340505547367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587945644278893670364911 2381918466418340505547367)
        ·
          refine ⟨3572877699627510758321051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381918466418340505547367 3572877699627510758321051)
          ·
            refine ⟨5359316549441266137481577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572877699627510758321051 5359316549441266137481577)
            ·
              refine ⟨4019487412080949603111183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5359316549441266137481577 4019487412080949603111183)
              ·
                refine ⟨6029231118121424404666775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019487412080949603111183 6029231118121424404666775)
                ·
                  refine ⟨9043846677182136607000163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6029231118121424404666775 9043846677182136607000163)
                  ·
                    refine ⟨13565770015773204910500245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9043846677182136607000163 13565770015773204910500245)
                    ·
                      refine ⟨635895469489368980179699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13565770015773204910500245 635895469489368980179699)
                      ·
                        rfl

theorem cell23_1238402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1238402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238402 prefixEnd_1238402 := by exact prefixLift 1238402
  have htrace : WordTrace (prefixWord ++ tailWord_1238402) baseStart_1238402 baseEnd_1238402 := by
    simpa [prefixWord, tailWord_1238402, baseEnd_1238402] using wordTrace_append hprefix tailTrace_1238402
  have hstable : (prefixWord ++ tailWord_1238402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238402).length < 2 ^ (prefixWord ++ tailWord_1238402).sum := by decide
  have hdescent : baseEnd_1238402 < baseStart_1238402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238409 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_1238409 : Nat := 118140960795 + 1238409 * 2 ^ 59
def prefixEnd_1238409 : Nat := 4983230072969 + 3 ^ 40 * 1238409 * 2
def baseEnd_1238409 : Nat := 635899063853950452792167

theorem tailTrace_1238409 : CollatzResearch.WordTrace tailWord_1238409 prefixEnd_1238409 635899063853950452792167 := by
  unfold tailWord_1238409
  simp only [CollatzResearch.WordTrace]
  refine ⟨45168486970463171263662281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30112324646975447509108187 45168486970463171263662281)
  ·
    refine ⟨33876365227847378447746711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45168486970463171263662281 33876365227847378447746711)
    ·
      refine ⟨50814547841771067671620067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33876365227847378447746711 50814547841771067671620067)
      ·
        refine ⟨76221821762656601507430101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50814547841771067671620067 76221821762656601507430101)
        ·
          refine ⟨1786448947562264097830393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76221821762656601507430101 1786448947562264097830393)
          ·
            refine ⟨1339836710671698073372795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1786448947562264097830393 1339836710671698073372795)
            ·
              refine ⟨2009755066007547110059193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339836710671698073372795 2009755066007547110059193)
              ·
                refine ⟨1507316299505660332544395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009755066007547110059193 1507316299505660332544395)
                ·
                  refine ⟨2260974449258490498816593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507316299505660332544395 2260974449258490498816593)
                  ·
                    refine ⟨1695730836943867874112445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2260974449258490498816593 1695730836943867874112445)
                    ·
                      refine ⟨635899063853950452792167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1695730836943867874112445 635899063853950452792167)
                      ·
                        rfl

theorem cell23_1238409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_1238409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238409 prefixEnd_1238409 := by exact prefixLift 1238409
  have htrace : WordTrace (prefixWord ++ tailWord_1238409) baseStart_1238409 baseEnd_1238409 := by
    simpa [prefixWord, tailWord_1238409, baseEnd_1238409] using wordTrace_append hprefix tailTrace_1238409
  have hstable : (prefixWord ++ tailWord_1238409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238409).length < 2 ^ (prefixWord ++ tailWord_1238409).sum := by decide
  have hdescent : baseEnd_1238409 < baseStart_1238409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238439 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1238439 : Nat := 118140960795 + 1238439 * 2 ^ 59
def prefixEnd_1238439 : Nat := 4983230072969 + 3 ^ 40 * 1238439 * 2
def baseEnd_1238439 : Nat := 635914468273585335417029

theorem tailTrace_1238439 : CollatzResearch.WordTrace tailWord_1238439 prefixEnd_1238439 635914468273585335417029 := by
  unfold tailWord_1238439
  simp only [CollatzResearch.WordTrace]
  refine ⟨45169581160354486387254371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30113054106902990924836247 45169581160354486387254371)
  ·
    refine ⟨67754371740531729580881557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45169581160354486387254371 67754371740531729580881557)
    ·
      refine ⟨3175986175337424824103823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67754371740531729580881557 3175986175337424824103823)
      ·
        refine ⟨4763979263006137236155735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175986175337424824103823 4763979263006137236155735)
        ·
          refine ⟨7145968894509205854233603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763979263006137236155735 7145968894509205854233603)
          ·
            refine ⟨10718953341763808781350405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145968894509205854233603 10718953341763808781350405)
            ·
              refine ⟨2009803751580714146503201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10718953341763808781350405 2009803751580714146503201)
              ·
                refine ⟨1507352813685535609877401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009803751580714146503201 1507352813685535609877401)
                ·
                  refine ⟨1130514610264151707408051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507352813685535609877401 1130514610264151707408051)
                  ·
                    refine ⟨1695771915396227561112077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1130514610264151707408051 1695771915396227561112077)
                    ·
                      refine ⟨635914468273585335417029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1695771915396227561112077 635914468273585335417029)
                      ·
                        rfl

theorem cell23_1238439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1238439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238439 prefixEnd_1238439 := by exact prefixLift 1238439
  have htrace : WordTrace (prefixWord ++ tailWord_1238439) baseStart_1238439 baseEnd_1238439 := by
    simpa [prefixWord, tailWord_1238439, baseEnd_1238439] using wordTrace_append hprefix tailTrace_1238439
  have hstable : (prefixWord ++ tailWord_1238439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238439).length < 2 ^ (prefixWord ++ tailWord_1238439).sum := by decide
  have hdescent : baseEnd_1238439 < baseStart_1238439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_1238448 : Nat := 118140960795 + 1238448 * 2 ^ 59
def prefixEnd_1238448 : Nat := 4983230072969 + 3 ^ 40 * 1238448 * 2
def baseEnd_1238448 : Nat := 635919089599475800204487

theorem tailTrace_1238448 : CollatzResearch.WordTrace tailWord_1238448 prefixEnd_1238448 635919089599475800204487 := by
  unfold tailWord_1238448
  simp only [CollatzResearch.WordTrace]
  refine ⟨22584954708660940462165999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30113272944881253949554665 22584954708660940462165999)
  ·
    refine ⟨33877432062991410693248999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22584954708660940462165999 33877432062991410693248999)
    ·
      refine ⟨50816148094487116039873499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33877432062991410693248999 50816148094487116039873499)
      ·
        refine ⟨76224222141730674059810249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50816148094487116039873499 76224222141730674059810249)
        ·
          refine ⟨57168166606298005544857687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76224222141730674059810249 57168166606298005544857687)
          ·
            refine ⟨85752249909447008317286531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57168166606298005544857687 85752249909447008317286531)
            ·
              refine ⟨128628374864170512475929797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85752249909447008317286531 128628374864170512475929797)
              ·
                refine ⟨24117820287031971089236837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128628374864170512475929797 24117820287031971089236837)
                ·
                  refine ⟨4522091303818494579231907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24117820287031971089236837 4522091303818494579231907)
                  ·
                    refine ⟨6783136955727741868847861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522091303818494579231907 6783136955727741868847861)
                    ·
                      refine ⟨635919089599475800204487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6783136955727741868847861 635919089599475800204487)
                      ·
                        rfl

theorem cell23_1238448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_1238448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238448 prefixEnd_1238448 := by exact prefixLift 1238448
  have htrace : WordTrace (prefixWord ++ tailWord_1238448) baseStart_1238448 baseEnd_1238448 := by
    simpa [prefixWord, tailWord_1238448, baseEnd_1238448] using wordTrace_append hprefix tailTrace_1238448
  have hstable : (prefixWord ++ tailWord_1238448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238448).length < 2 ^ (prefixWord ++ tailWord_1238448).sum := by decide
  have hdescent : baseEnd_1238448 < baseStart_1238448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238495 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1238495 : Nat := 118140960795 + 1238495 * 2 ^ 59
def prefixEnd_1238495 : Nat := 4983230072969 + 3 ^ 40 * 1238495 * 2
def baseEnd_1238495 : Nat := 635943223190237116316771

theorem tailTrace_1238495 : CollatzResearch.WordTrace tailWord_1238495 prefixEnd_1238495 635943223190237116316771 := by
  unfold tailWord_1238495
  simp only [CollatzResearch.WordTrace]
  refine ⟨45171623648151607951292939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30114415765434405300861959 45171623648151607951292939)
  ·
    refine ⟨67757435472227411926939409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45171623648151607951292939 67757435472227411926939409)
    ·
      refine ⟨50818076604170558945204557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67757435472227411926939409 50818076604170558945204557)
      ·
        refine ⟨19056778726563959604451709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50818076604170558945204557 19056778726563959604451709)
        ·
          refine ⟨7146292022461484851669391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19056778726563959604451709 7146292022461484851669391)
          ·
            refine ⟨10719438033692227277504087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146292022461484851669391 10719438033692227277504087)
            ·
              refine ⟨16079157050538340916256131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10719438033692227277504087 16079157050538340916256131)
              ·
                refine ⟨24118735575807511374384197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16079157050538340916256131 24118735575807511374384197)
                ·
                  refine ⟨4522262920463908382697037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24118735575807511374384197 4522262920463908382697037)
                  ·
                    refine ⟨1695848595173965643511389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4522262920463908382697037 1695848595173965643511389)
                    ·
                      refine ⟨635943223190237116316771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1695848595173965643511389 635943223190237116316771)
                      ·
                        rfl

theorem cell23_1238495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1238495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238495 prefixEnd_1238495 := by exact prefixLift 1238495
  have htrace : WordTrace (prefixWord ++ tailWord_1238495) baseStart_1238495 baseEnd_1238495 := by
    simpa [prefixWord, tailWord_1238495, baseEnd_1238495] using wordTrace_append hprefix tailTrace_1238495
  have hstable : (prefixWord ++ tailWord_1238495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238495).length < 2 ^ (prefixWord ++ tailWord_1238495).sum := by decide
  have hdescent : baseEnd_1238495 < baseStart_1238495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238646 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1238646 : Nat := 118140960795 + 1238646 * 2 ^ 59
def prefixEnd_1238646 : Nat := 4983230072969 + 3 ^ 40 * 1238646 * 2
def baseEnd_1238646 : Nat := 636020758769066025528577

theorem tailTrace_1238646 : CollatzResearch.WordTrace tailWord_1238646 prefixEnd_1238646 636020758769066025528577 := by
  unfold tailWord_1238646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823570691912785046252487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30118087380403040493359861 2823570691912785046252487)
  ·
    refine ⟨4235356037869177569378731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2823570691912785046252487 4235356037869177569378731)
    ·
      refine ⟨6353034056803766354068097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235356037869177569378731 6353034056803766354068097)
      ·
        refine ⟨4764775542602824765551073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6353034056803766354068097 4764775542602824765551073)
        ·
          refine ⟨3573581656952118574163305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764775542602824765551073 3573581656952118574163305)
          ·
            refine ⟨2680186242714088930622479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3573581656952118574163305 2680186242714088930622479)
            ·
              refine ⟨4020279364071133395933719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680186242714088930622479 4020279364071133395933719)
              ·
                refine ⟨6030419046106700093900579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020279364071133395933719 6030419046106700093900579)
                ·
                  refine ⟨9045628569160050140850869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6030419046106700093900579 9045628569160050140850869)
                  ·
                    refine ⟨848027678358754700704769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9045628569160050140850869 848027678358754700704769)
                    ·
                      refine ⟨636020758769066025528577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848027678358754700704769 636020758769066025528577)
                      ·
                        rfl

theorem cell23_1238646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1238646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238646 prefixEnd_1238646 := by exact prefixLift 1238646
  have htrace : WordTrace (prefixWord ++ tailWord_1238646) baseStart_1238646 baseEnd_1238646 := by
    simpa [prefixWord, tailWord_1238646, baseEnd_1238646] using wordTrace_append hprefix tailTrace_1238646
  have hstable : (prefixWord ++ tailWord_1238646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238646).length < 2 ^ (prefixWord ++ tailWord_1238646).sum := by decide
  have hdescent : baseEnd_1238646 < baseStart_1238646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238652 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1238652 : Nat := 118140960795 + 1238652 * 2 ^ 59
def prefixEnd_1238652 : Nat := 4983230072969 + 3 ^ 40 * 1238652 * 2
def baseEnd_1238652 : Nat := 212007946550997667351183

theorem tailTrace_1238652 : CollatzResearch.WordTrace tailWord_1238652 prefixEnd_1238652 212007946550997667351183 := by
  unfold tailWord_1238652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22588674954291411882379105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30118233272388549176505473 22588674954291411882379105)
  ·
    refine ⟨16941506215718558911784329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22588674954291411882379105 16941506215718558911784329)
    ·
      refine ⟨12706129661788919183838247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16941506215718558911784329 12706129661788919183838247)
      ·
        refine ⟨19059194492683378775757371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706129661788919183838247 19059194492683378775757371)
        ·
          refine ⟨28588791739025068163636057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19059194492683378775757371 28588791739025068163636057)
          ·
            refine ⟨21441593804268801122727043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28588791739025068163636057 21441593804268801122727043)
            ·
              refine ⟨32162390706403201684090565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21441593804268801122727043 32162390706403201684090565)
              ·
                refine ⟨6030448257450600315766981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32162390706403201684090565 6030448257450600315766981)
                ·
                  refine ⟨1130709048271987559206309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6030448257450600315766981 1130709048271987559206309)
                  ·
                    refine ⟨212007946550997667351183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1130709048271987559206309 212007946550997667351183)
                    ·
                      rfl

theorem cell23_1238652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1238652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238652 prefixEnd_1238652 := by exact prefixLift 1238652
  have htrace : WordTrace (prefixWord ++ tailWord_1238652) baseStart_1238652 baseEnd_1238652 := by
    simpa [prefixWord, tailWord_1238652, baseEnd_1238652] using wordTrace_append hprefix tailTrace_1238652
  have hstable : (prefixWord ++ tailWord_1238652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238652).length < 2 ^ (prefixWord ++ tailWord_1238652).sum := by decide
  have hdescent : baseEnd_1238652 < baseStart_1238652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238653 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_1238653 : Nat := 118140960795 + 1238653 * 2 ^ 59
def prefixEnd_1238653 : Nat := 4983230072969 + 3 ^ 40 * 1238653 * 2
def baseEnd_1238653 : Nat := 636024353133647498141045

theorem tailTrace_1238653 : CollatzResearch.WordTrace tailWord_1238653 prefixEnd_1238653 636024353133647498141045 := by
  unfold tailWord_1238653
  simp only [CollatzResearch.WordTrace]
  refine ⟨45177386381579200935544613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30118257587719467290363075 45177386381579200935544613)
  ·
    refine ⟨8470759946546100175414615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45177386381579200935544613 8470759946546100175414615)
    ·
      refine ⟨12706139919819150263121923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8470759946546100175414615 12706139919819150263121923)
      ·
        refine ⟨19059209879728725394682885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706139919819150263121923 19059209879728725394682885)
        ·
          refine ⟨3573601852449136011503041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19059209879728725394682885 3573601852449136011503041)
          ·
            refine ⟨2680201389336852008627281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3573601852449136011503041 2680201389336852008627281)
            ·
              refine ⟨2010151042002639006470461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680201389336852008627281 2010151042002639006470461)
              ·
                refine ⟨753806640750989627426423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2010151042002639006470461 753806640750989627426423)
                ·
                  refine ⟨1130709961126484441139635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753806640750989627426423 1130709961126484441139635)
                  ·
                    refine ⟨1696064941689726661709453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1130709961126484441139635 1696064941689726661709453)
                    ·
                      refine ⟨636024353133647498141045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1696064941689726661709453 636024353133647498141045)
                      ·
                        rfl

theorem cell23_1238653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_1238653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238653 prefixEnd_1238653 := by exact prefixLift 1238653
  have htrace : WordTrace (prefixWord ++ tailWord_1238653) baseStart_1238653 baseEnd_1238653 := by
    simpa [prefixWord, tailWord_1238653, baseEnd_1238653] using wordTrace_append hprefix tailTrace_1238653
  have hstable : (prefixWord ++ tailWord_1238653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238653).length < 2 ^ (prefixWord ++ tailWord_1238653).sum := by decide
  have hdescent : baseEnd_1238653 < baseStart_1238653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238655 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_1238655 : Nat := 118140960795 + 1238655 * 2 ^ 59
def prefixEnd_1238655 : Nat := 4983230072969 + 3 ^ 40 * 1238655 * 2
def baseEnd_1238655 : Nat := 636025380094956490316035

theorem tailTrace_1238655 : CollatzResearch.WordTrace tailWord_1238655 prefixEnd_1238655 636025380094956490316035 := by
  unfold tailWord_1238655
  simp only [CollatzResearch.WordTrace]
  refine ⟨45177459327571955277117419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30118306218381303518078279 45177459327571955277117419)
  ·
    refine ⟨67766188991357932915676129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45177459327571955277117419 67766188991357932915676129)
    ·
      refine ⟨50824641743518449686757097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67766188991357932915676129 50824641743518449686757097)
      ·
        refine ⟨38118481307638837265067823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50824641743518449686757097 38118481307638837265067823)
        ·
          refine ⟨57177721961458255897601735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38118481307638837265067823 57177721961458255897601735)
          ·
            refine ⟨85766582942187383846402603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57177721961458255897601735 85766582942187383846402603)
            ·
              refine ⟨128649874413281075769603905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85766582942187383846402603 128649874413281075769603905)
              ·
                refine ⟨96487405809960806827202929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128649874413281075769603905 96487405809960806827202929)
                ·
                  refine ⟨72365554357470605120402197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96487405809960806827202929 72365554357470605120402197)
                  ·
                    refine ⟨3392135360506434615018853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72365554357470605120402197 3392135360506434615018853)
                    ·
                      refine ⟨636025380094956490316035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3392135360506434615018853 636025380094956490316035)
                      ·
                        rfl

theorem cell23_1238655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_1238655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238655 prefixEnd_1238655 := by exact prefixLift 1238655
  have htrace : WordTrace (prefixWord ++ tailWord_1238655) baseStart_1238655 baseEnd_1238655 := by
    simpa [prefixWord, tailWord_1238655, baseEnd_1238655] using wordTrace_append hprefix tailTrace_1238655
  have hstable : (prefixWord ++ tailWord_1238655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238655).length < 2 ^ (prefixWord ++ tailWord_1238655).sum := by decide
  have hdescent : baseEnd_1238655 < baseStart_1238655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238659 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 7, 2, 2]
def baseStart_1238659 : Nat := 118140960795 + 1238659 * 2 ^ 59
def prefixEnd_1238659 : Nat := 4983230072969 + 3 ^ 40 * 1238659 * 2
def baseEnd_1238659 : Nat := 636027434017574474666017

theorem tailTrace_1238659 : CollatzResearch.WordTrace tailWord_1238659 prefixEnd_1238659 636027434017574474666017 := by
  unfold tailWord_1238659
  simp only [CollatzResearch.WordTrace]
  refine ⟨45177605219557463960263031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30118403479704975973508687 45177605219557463960263031)
  ·
    refine ⟨67766407829336195940394547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45177605219557463960263031 67766407829336195940394547)
    ·
      refine ⟨101649611744004293910591821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67766407829336195940394547 101649611744004293910591821)
      ·
        refine ⟨38118604404001610216471933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101649611744004293910591821 38118604404001610216471933)
        ·
          refine ⟨14294476651500603831176975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38118604404001610216471933 14294476651500603831176975)
          ·
            refine ⟨21441714977250905746765463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294476651500603831176975 21441714977250905746765463)
            ·
              refine ⟨32162572465876358620148195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21441714977250905746765463 32162572465876358620148195)
              ·
                refine ⟨48243858698814537930222293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32162572465876358620148195 48243858698814537930222293)
                ·
                  refine ⟨1130715438253465732739585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48243858698814537930222293 1130715438253465732739585)
                  ·
                    refine ⟨848036578690099299554689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1130715438253465732739585 848036578690099299554689)
                    ·
                      refine ⟨636027434017574474666017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848036578690099299554689 636027434017574474666017)
                      ·
                        rfl

theorem cell23_1238659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_1238659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238659 prefixEnd_1238659 := by exact prefixLift 1238659
  have htrace : WordTrace (prefixWord ++ tailWord_1238659) baseStart_1238659 baseEnd_1238659 := by
    simpa [prefixWord, tailWord_1238659, baseEnd_1238659] using wordTrace_append hprefix tailTrace_1238659
  have hstable : (prefixWord ++ tailWord_1238659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238659).length < 2 ^ (prefixWord ++ tailWord_1238659).sum := by decide
  have hdescent : baseEnd_1238659 < baseStart_1238659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238686 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1238686 : Nat := 118140960795 + 1238686 * 2 ^ 59
def prefixEnd_1238686 : Nat := 4983230072969 + 3 ^ 40 * 1238686 * 2
def baseEnd_1238686 : Nat := 212013765998415289676131

theorem tailTrace_1238686 : CollatzResearch.WordTrace tailWord_1238686 prefixEnd_1238686 212013765998415289676131 := by
  unfold tailWord_1238686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647323748807455946436989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30119059993639765047663941 5647323748807455946436989)
  ·
    refine ⟨2117746405802795979913871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5647323748807455946436989 2117746405802795979913871)
    ·
      refine ⟨3176619608704193969870807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117746405802795979913871 3176619608704193969870807)
      ·
        refine ⟨4764929413056290954806211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176619608704193969870807 4764929413056290954806211)
        ·
          refine ⟨7147394119584436432209317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764929413056290954806211 7147394119584436432209317)
          ·
            refine ⟨1340136397422081831039247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7147394119584436432209317 1340136397422081831039247)
            ·
              refine ⟨2010204596133122746558871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340136397422081831039247 2010204596133122746558871)
              ·
                refine ⟨3015306894199684119838307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010204596133122746558871 3015306894199684119838307)
                ·
                  refine ⟨4522960341299526179757461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015306894199684119838307 4522960341299526179757461)
                  ·
                    refine ⟨212013765998415289676131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4522960341299526179757461 212013765998415289676131)
                    ·
                      rfl

theorem cell23_1238686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1238686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238686 prefixEnd_1238686 := by exact prefixLift 1238686
  have htrace : WordTrace (prefixWord ++ tailWord_1238686) baseStart_1238686 baseEnd_1238686 := by
    simpa [prefixWord, tailWord_1238686, baseEnd_1238686] using wordTrace_append hprefix tailTrace_1238686
  have hstable : (prefixWord ++ tailWord_1238686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238686).length < 2 ^ (prefixWord ++ tailWord_1238686).sum := by decide
  have hdescent : baseEnd_1238686 < baseStart_1238686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238689 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1238689 : Nat := 118140960795 + 1238689 * 2 ^ 59
def prefixEnd_1238689 : Nat := 4983230072969 + 3 ^ 40 * 1238689 * 2
def baseEnd_1238689 : Nat := 636042838437209357290879

theorem tailTrace_1238689 : CollatzResearch.WordTrace tailWord_1238689 prefixEnd_1238689 636042838437209357290879 := by
  unfold tailWord_1238689
  simp only [CollatzResearch.WordTrace]
  refine ⟨45178699409448779083855121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30119132939632519389236747 45178699409448779083855121)
  ·
    refine ⟨33884024557086584312891341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45178699409448779083855121 33884024557086584312891341)
    ·
      refine ⟨12706509208907469117334253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33884024557086584312891341 12706509208907469117334253)
      ·
        refine ⟨4764940953340300919000345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12706509208907469117334253 4764940953340300919000345)
        ·
          refine ⟨3573705715005225689250259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764940953340300919000345 3573705715005225689250259)
          ·
            refine ⟨5360558572507838533875389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573705715005225689250259 5360558572507838533875389)
            ·
              refine ⟨2010209464690439450203271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5360558572507838533875389 2010209464690439450203271)
              ·
                refine ⟨3015314197035659175304907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010209464690439450203271 3015314197035659175304907)
                ·
                  refine ⟨4522971295553488762957361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015314197035659175304907 4522971295553488762957361)
                  ·
                    refine ⟨3392228471665116572218021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522971295553488762957361 3392228471665116572218021)
                    ·
                      refine ⟨636042838437209357290879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3392228471665116572218021 636042838437209357290879)
                      ·
                        rfl

theorem cell23_1238689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1238689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238689 prefixEnd_1238689 := by exact prefixLift 1238689
  have htrace : WordTrace (prefixWord ++ tailWord_1238689) baseStart_1238689 baseEnd_1238689 := by
    simpa [prefixWord, tailWord_1238689, baseEnd_1238689] using wordTrace_append hprefix tailTrace_1238689
  have hstable : (prefixWord ++ tailWord_1238689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238689).length < 2 ^ (prefixWord ++ tailWord_1238689).sum := by decide
  have hdescent : baseEnd_1238689 < baseStart_1238689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238715 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_1238715 : Nat := 118140960795 + 1238715 * 2 ^ 59
def prefixEnd_1238715 : Nat := 4983230072969 + 3 ^ 40 * 1238715 * 2
def baseEnd_1238715 : Nat := 636056188934226255565759

theorem tailTrace_1238715 : CollatzResearch.WordTrace tailWord_1238715 prefixEnd_1238715 636056188934226255565759 := by
  unfold tailWord_1238715
  simp only [CollatzResearch.WordTrace]
  refine ⟨45179647707354585524301599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30119765138236390349534399 45179647707354585524301599)
  ·
    refine ⟨67769471561031878286452399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45179647707354585524301599 67769471561031878286452399)
    ·
      refine ⟨101654207341547817429678599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67769471561031878286452399 101654207341547817429678599)
      ·
        refine ⟨152481311012321726144517899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101654207341547817429678599 152481311012321726144517899)
        ·
          refine ⟨228721966518482589216776849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152481311012321726144517899 228721966518482589216776849)
          ·
            refine ⟨171541474888861941912582637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228721966518482589216776849 171541474888861941912582637)
            ·
              refine ⟨64328053083323228217218489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171541474888861941912582637 64328053083323228217218489)
              ·
                refine ⟨48246039812492421162913867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64328053083323228217218489 48246039812492421162913867)
                ·
                  refine ⟨72369059718738631744370801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48246039812492421162913867 72369059718738631744370801)
                  ·
                    refine ⟨54276794789053973808278101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72369059718738631744370801 54276794789053973808278101)
                    ·
                      refine ⟨636056188934226255565759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 54276794789053973808278101 636056188934226255565759)
                      ·
                        rfl

theorem cell23_1238715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_1238715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238715 prefixEnd_1238715 := by exact prefixLift 1238715
  have htrace : WordTrace (prefixWord ++ tailWord_1238715) baseStart_1238715 baseEnd_1238715 := by
    simpa [prefixWord, tailWord_1238715, baseEnd_1238715] using wordTrace_append hprefix tailTrace_1238715
  have hstable : (prefixWord ++ tailWord_1238715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238715).length < 2 ^ (prefixWord ++ tailWord_1238715).sum := by decide
  have hdescent : baseEnd_1238715 < baseStart_1238715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238752 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1238752 : Nat := 118140960795 + 1238752 * 2 ^ 59
def prefixEnd_1238752 : Nat := 4983230072969 + 3 ^ 40 * 1238752 * 2
def baseEnd_1238752 : Nat := 636075187718442610803089

theorem tailTrace_1238752 : CollatzResearch.WordTrace tailWord_1238752 prefixEnd_1238752 636075187718442610803089 := by
  unfold tailWord_1238752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590498604110270421699255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30120664805480360562265673 22590498604110270421699255)
  ·
    refine ⟨33885747906165405632548883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22590498604110270421699255 33885747906165405632548883)
    ·
      refine ⟨50828621859248108448823325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33885747906165405632548883 50828621859248108448823325)
      ·
        refine ⟨19060733197218040668308747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50828621859248108448823325 19060733197218040668308747)
        ·
          refine ⟨28591099795827061002463121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19060733197218040668308747 28591099795827061002463121)
          ·
            refine ⟨21443324846870295751847341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28591099795827061002463121 21443324846870295751847341)
            ·
              refine ⟨8041246817576360906942753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21443324846870295751847341 8041246817576360906942753)
              ·
                refine ⟨6030935113182270680207065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8041246817576360906942753 6030935113182270680207065)
                ·
                  refine ⟨4523201334886703010155299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6030935113182270680207065 4523201334886703010155299)
                  ·
                    refine ⟨6784802002330054515232949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4523201334886703010155299 6784802002330054515232949)
                    ·
                      refine ⟨636075187718442610803089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6784802002330054515232949 636075187718442610803089)
                      ·
                        rfl

theorem cell23_1238752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1238752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238752 prefixEnd_1238752 := by exact prefixLift 1238752
  have htrace : WordTrace (prefixWord ++ tailWord_1238752) baseStart_1238752 baseEnd_1238752 := by
    simpa [prefixWord, tailWord_1238752, baseEnd_1238752] using wordTrace_append hprefix tailTrace_1238752
  have hstable : (prefixWord ++ tailWord_1238752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238752).length < 2 ^ (prefixWord ++ tailWord_1238752).sum := by decide
  have hdescent : baseEnd_1238752 < baseStart_1238752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238766 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_1238766 : Nat := 118140960795 + 1238766 * 2 ^ 59
def prefixEnd_1238766 : Nat := 4983230072969 + 3 ^ 40 * 1238766 * 2
def baseEnd_1238766 : Nat := 636082376447605556028025

theorem tailTrace_1238766 : CollatzResearch.WordTrace tailWord_1238766 prefixEnd_1238766 636082376447605556028025 := by
  unfold tailWord_1238766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647688478771227654301019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30121005220113214156272101 5647688478771227654301019)
  ·
    refine ⟨8471532718156841481451529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5647688478771227654301019 8471532718156841481451529)
    ·
      refine ⟨6353649538617631111088647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8471532718156841481451529 6353649538617631111088647)
      ·
        refine ⟨9530474307926446666632971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353649538617631111088647 9530474307926446666632971)
        ·
          refine ⟨14295711461889669999949457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530474307926446666632971 14295711461889669999949457)
          ·
            refine ⟨10721783596417252499962093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14295711461889669999949457 10721783596417252499962093)
            ·
              refine ⟨4020668848656469687485785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10721783596417252499962093 4020668848656469687485785)
              ·
                refine ⟨3015501636492352265614339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4020668848656469687485785 3015501636492352265614339)
                ·
                  refine ⟨4523252454738528398421509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015501636492352265614339 4523252454738528398421509)
                  ·
                    refine ⟨848109835263474074704033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523252454738528398421509 848109835263474074704033)
                    ·
                      refine ⟨636082376447605556028025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848109835263474074704033 636082376447605556028025)
                      ·
                        rfl

theorem cell23_1238766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_1238766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238766 prefixEnd_1238766 := by exact prefixLift 1238766
  have htrace : WordTrace (prefixWord ++ tailWord_1238766) baseStart_1238766 baseEnd_1238766 := by
    simpa [prefixWord, tailWord_1238766, baseEnd_1238766] using wordTrace_append hprefix tailTrace_1238766
  have hstable : (prefixWord ++ tailWord_1238766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238766).length < 2 ^ (prefixWord ++ tailWord_1238766).sum := by decide
  have hdescent : baseEnd_1238766 < baseStart_1238766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238819 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 2, 5]
def baseStart_1238819 : Nat := 118140960795 + 1238819 * 2 ^ 59
def prefixEnd_1238819 : Nat := 4983230072969 + 3 ^ 40 * 1238819 * 2
def baseEnd_1238819 : Nat := 212036530307431282888427

theorem tailTrace_1238819 : CollatzResearch.WordTrace tailWord_1238819 prefixEnd_1238819 212036530307431282888427 := by
  unfold tailWord_1238819
  simp only [CollatzResearch.WordTrace]
  refine ⟨45183440898977811286087511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30122293932651874190725007 45183440898977811286087511)
  ·
    refine ⟨67775161348466716929131267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45183440898977811286087511 67775161348466716929131267)
    ·
      refine ⟨101662742022700075393696901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67775161348466716929131267 101662742022700075393696901)
      ·
        refine ⟨19061764129256264136318169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101662742022700075393696901 19061764129256264136318169)
        ·
          refine ⟨14296323096942198102238627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19061764129256264136318169 14296323096942198102238627)
          ·
            refine ⟨21444484645413297153357941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14296323096942198102238627 21444484645413297153357941)
            ·
              refine ⟨2010420435507496608127307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21444484645413297153357941 2010420435507496608127307)
              ·
                refine ⟨3015630653261244912190961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010420435507496608127307 3015630653261244912190961)
                ·
                  refine ⟨2261722989945933684143221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015630653261244912190961 2261722989945933684143221)
                  ·
                    refine ⟨212036530307431282888427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2261722989945933684143221 212036530307431282888427)
                    ·
                      rfl

theorem cell23_1238819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 5].length) (baseStart_1238819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238819 prefixEnd_1238819 := by exact prefixLift 1238819
  have htrace : WordTrace (prefixWord ++ tailWord_1238819) baseStart_1238819 baseEnd_1238819 := by
    simpa [prefixWord, tailWord_1238819, baseEnd_1238819] using wordTrace_append hprefix tailTrace_1238819
  have hstable : (prefixWord ++ tailWord_1238819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238819).length < 2 ^ (prefixWord ++ tailWord_1238819).sum := by decide
  have hdescent : baseEnd_1238819 < baseStart_1238819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238856 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_1238856 : Nat := 118140960795 + 1238856 * 2 ^ 59
def prefixEnd_1238856 : Nat := 4983230072969 + 3 ^ 40 * 1238856 * 2
def baseEnd_1238856 : Nat := 636128589706510203902611

theorem tailTrace_1238856 : CollatzResearch.WordTrace tailWord_1238856 prefixEnd_1238856 636128589706510203902611 := by
  unfold tailWord_1238856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22592395199921883302592211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30123193599895844403456281 22592395199921883302592211)
  ·
    refine ⟨33888592799882824953888317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22592395199921883302592211 33888592799882824953888317)
    ·
      refine ⟨12708222299956059357708119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33888592799882824953888317 12708222299956059357708119)
      ·
        refine ⟨19062333449934089036562179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708222299956059357708119 19062333449934089036562179)
        ·
          refine ⟨28593500174901133554843269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19062333449934089036562179 28593500174901133554843269)
          ·
            refine ⟨5361281282793962541533113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28593500174901133554843269 5361281282793962541533113)
            ·
              refine ⟨4020960962095471906149835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361281282793962541533113 4020960962095471906149835)
              ·
                refine ⟨6031441443143207859224753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020960962095471906149835 6031441443143207859224753)
                ·
                  refine ⟨4523581082357405894418565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031441443143207859224753 4523581082357405894418565)
                  ·
                    refine ⟨848171452942013605203481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523581082357405894418565 848171452942013605203481)
                    ·
                      refine ⟨636128589706510203902611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848171452942013605203481 636128589706510203902611)
                      ·
                        rfl

theorem cell23_1238856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_1238856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238856 prefixEnd_1238856 := by exact prefixLift 1238856
  have htrace : WordTrace (prefixWord ++ tailWord_1238856) baseStart_1238856 baseEnd_1238856 := by
    simpa [prefixWord, tailWord_1238856, baseEnd_1238856] using wordTrace_append hprefix tailTrace_1238856
  have hstable : (prefixWord ++ tailWord_1238856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238856).length < 2 ^ (prefixWord ++ tailWord_1238856).sum := by decide
  have hdescent : baseEnd_1238856 < baseStart_1238856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238866 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1238866 : Nat := 118140960795 + 1238866 * 2 ^ 59
def prefixEnd_1238866 : Nat := 4983230072969 + 3 ^ 40 * 1238866 * 2
def baseEnd_1238866 : Nat := 212044574837685054925855

theorem tailTrace_1238866 : CollatzResearch.WordTrace tailWord_1238866 prefixEnd_1238866 212044574837685054925855 := by
  unfold tailWord_1238866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11296288782451884578262113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30123436753205025542032301 11296288782451884578262113)
  ·
    refine ⟨8472216586838913433696585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11296288782451884578262113 8472216586838913433696585)
    ·
      refine ⟨6354162440129185075272439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8472216586838913433696585 6354162440129185075272439)
      ·
        refine ⟨9531243660193777612908659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354162440129185075272439 9531243660193777612908659)
        ·
          refine ⟨14296865490290666419362989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531243660193777612908659 14296865490290666419362989)
          ·
            refine ⟨5361324558858999907261121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14296865490290666419362989 5361324558858999907261121)
            ·
              refine ⟨4020993419144249930445841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361324558858999907261121 4020993419144249930445841)
              ·
                refine ⟨3015745064358187447834381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4020993419144249930445841 3015745064358187447834381)
                ·
                  refine ⟨1130904399134320292937893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3015745064358187447834381 1130904399134320292937893)
                  ·
                    refine ⟨212044574837685054925855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1130904399134320292937893 212044574837685054925855)
                    ·
                      rfl

theorem cell23_1238866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1238866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238866 prefixEnd_1238866 := by exact prefixLift 1238866
  have htrace : WordTrace (prefixWord ++ tailWord_1238866) baseStart_1238866 baseEnd_1238866 := by
    simpa [prefixWord, tailWord_1238866, baseEnd_1238866] using wordTrace_append hprefix tailTrace_1238866
  have hstable : (prefixWord ++ tailWord_1238866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238866).length < 2 ^ (prefixWord ++ tailWord_1238866).sum := by decide
  have hdescent : baseEnd_1238866 < baseStart_1238866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238872 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1238872 : Nat := 118140960795 + 1238872 * 2 ^ 59
def prefixEnd_1238872 : Nat := 4983230072969 + 3 ^ 40 * 1238872 * 2
def baseEnd_1238872 : Nat := 636136805396982141302537

theorem tailTrace_1238872 : CollatzResearch.WordTrace tailWord_1238872 prefixEnd_1238872 636136805396982141302537 := by
  unfold tailWord_1238872
  simp only [CollatzResearch.WordTrace]
  refine ⟨22592686983892900668883435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30123582645190534225177913 22592686983892900668883435)
  ·
    refine ⟨33889030475839351003325153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22592686983892900668883435 33889030475839351003325153)
    ·
      refine ⟨25416772856879513252493865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33889030475839351003325153 25416772856879513252493865)
      ·
        refine ⟨19062579642659634939370399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25416772856879513252493865 19062579642659634939370399)
        ·
          refine ⟨28593869463989452409055599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19062579642659634939370399 28593869463989452409055599)
          ·
            refine ⟨42890804195984178613583399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28593869463989452409055599 42890804195984178613583399)
            ·
              refine ⟨64336206293976267920375099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42890804195984178613583399 64336206293976267920375099)
              ·
                refine ⟨96504309440964401880562649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64336206293976267920375099 96504309440964401880562649)
                ·
                  refine ⟨72378232080723301410421987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96504309440964401880562649 72378232080723301410421987)
                  ·
                    refine ⟨108567348121084952115632981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72378232080723301410421987 108567348121084952115632981)
                    ·
                      refine ⟨636136805396982141302537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 108567348121084952115632981 636136805396982141302537)
                      ·
                        rfl

theorem cell23_1238872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1238872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238872 prefixEnd_1238872 := by exact prefixLift 1238872
  have htrace : WordTrace (prefixWord ++ tailWord_1238872) baseStart_1238872 baseEnd_1238872 := by
    simpa [prefixWord, tailWord_1238872, baseEnd_1238872] using wordTrace_append hprefix tailTrace_1238872
  have hstable : (prefixWord ++ tailWord_1238872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238872).length < 2 ^ (prefixWord ++ tailWord_1238872).sum := by decide
  have hdescent : baseEnd_1238872 < baseStart_1238872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238909 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1238909 : Nat := 118140960795 + 1238909 * 2 ^ 59
def prefixEnd_1238909 : Nat := 4983230072969 + 3 ^ 40 * 1238909 * 2
def baseEnd_1238909 : Nat := 212051934727066165513289

theorem tailTrace_1238909 : CollatzResearch.WordTrace tailWord_1238909 prefixEnd_1238909 212051934727066165513289 := by
  unfold tailWord_1238909
  simp only [CollatzResearch.WordTrace]
  refine ⟨45186723468651756656863781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30124482312434504437909187 45186723468651756656863781)
  ·
    refine ⟨8472510650372204373161959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45186723468651756656863781 8472510650372204373161959)
    ·
      refine ⟨12708765975558306559742939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8472510650372204373161959 12708765975558306559742939)
      ·
        refine ⟨19063148963337459839614409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708765975558306559742939 19063148963337459839614409)
        ·
          refine ⟨14297361722503094879710807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19063148963337459839614409 14297361722503094879710807)
          ·
            refine ⟨21446042583754642319566211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297361722503094879710807 21446042583754642319566211)
            ·
              refine ⟨32169063875631963479349317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21446042583754642319566211 32169063875631963479349317)
              ·
                refine ⟨6031699476680993152377997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32169063875631963479349317 6031699476680993152377997)
                ·
                  refine ⟨2261887303755372432141749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6031699476680993152377997 2261887303755372432141749)
                  ·
                    refine ⟨212051934727066165513289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2261887303755372432141749 212051934727066165513289)
                    ·
                      rfl

theorem cell23_1238909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1238909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238909 prefixEnd_1238909 := by exact prefixLift 1238909
  have htrace : WordTrace (prefixWord ++ tailWord_1238909) baseStart_1238909 baseEnd_1238909 := by
    simpa [prefixWord, tailWord_1238909, baseEnd_1238909] using wordTrace_append hprefix tailTrace_1238909
  have hstable : (prefixWord ++ tailWord_1238909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238909).length < 2 ^ (prefixWord ++ tailWord_1238909).sum := by decide
  have hdescent : baseEnd_1238909 < baseStart_1238909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238913 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 6]
def baseStart_1238913 : Nat := 118140960795 + 1238913 * 2 ^ 59
def prefixEnd_1238913 : Nat := 4983230072969 + 3 ^ 40 * 1238913 * 2
def baseEnd_1238913 : Nat := 70684206455979608987761

theorem tailTrace_1238913 : CollatzResearch.WordTrace tailWord_1238913 prefixEnd_1238913 70684206455979608987761 := by
  unfold tailWord_1238913
  simp only [CollatzResearch.WordTrace]
  refine ⟨45186869360637265340009393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30124579573758176893339595 45186869360637265340009393)
  ·
    refine ⟨33890152020477949005007045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45186869360637265340009393 33890152020477949005007045)
    ·
      refine ⟨6354403503839615438438821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33890152020477949005007045 6354403503839615438438821)
      ·
        refine ⟨1191450656969927894707279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6354403503839615438438821 1191450656969927894707279)
        ·
          refine ⟨1787175985454891842060919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191450656969927894707279 1787175985454891842060919)
          ·
            refine ⟨2680763978182337763091379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787175985454891842060919 2680763978182337763091379)
            ·
              refine ⟨4021145967273506644637069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680763978182337763091379 4021145967273506644637069)
              ·
                refine ⟨1507929737727564991738901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021145967273506644637069 1507929737727564991738901)
                ·
                  refine ⟨70684206455979608987761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1507929737727564991738901 70684206455979608987761)
                  ·
                    rfl

theorem cell23_1238913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_1238913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238913 prefixEnd_1238913 := by exact prefixLift 1238913
  have htrace : WordTrace (prefixWord ++ tailWord_1238913) baseStart_1238913 baseEnd_1238913 := by
    simpa [prefixWord, tailWord_1238913, baseEnd_1238913] using wordTrace_append hprefix tailTrace_1238913
  have hstable : (prefixWord ++ tailWord_1238913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238913).length < 2 ^ (prefixWord ++ tailWord_1238913).sum := by decide
  have hdescent : baseEnd_1238913 < baseStart_1238913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238916 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_1238916 : Nat := 118140960795 + 1238916 * 2 ^ 59
def prefixEnd_1238916 : Nat := 4983230072969 + 3 ^ 40 * 1238916 * 2
def baseEnd_1238916 : Nat := 636159398545779969152335

theorem tailTrace_1238916 : CollatzResearch.WordTrace tailWord_1238916 prefixEnd_1238916 636159398545779969152335 := by
  unfold tailWord_1238916
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593489389813198426184301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30124652519750931234912401 22593489389813198426184301)
  ·
    refine ⟨8472558521179949409819113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22593489389813198426184301 8472558521179949409819113)
    ·
      refine ⟨6354418890884962057364335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8472558521179949409819113 6354418890884962057364335)
      ·
        refine ⟨9531628336327443086046503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354418890884962057364335 9531628336327443086046503)
        ·
          refine ⟨14297442504491164629069755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531628336327443086046503 14297442504491164629069755)
          ·
            refine ⟨21446163756736746943604633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297442504491164629069755 21446163756736746943604633)
            ·
              refine ⟨16084622817552560207703475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21446163756736746943604633 16084622817552560207703475)
              ·
                refine ⟨24126934226328840311555213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16084622817552560207703475 24126934226328840311555213)
                ·
                  refine ⟨9047600334873315116833205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24126934226328840311555213 9047600334873315116833205)
                  ·
                    refine ⟨848212531394373292203113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9047600334873315116833205 848212531394373292203113)
                    ·
                      refine ⟨636159398545779969152335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848212531394373292203113 636159398545779969152335)
                      ·
                        rfl

theorem cell23_1238916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_1238916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238916 prefixEnd_1238916 := by exact prefixLift 1238916
  have htrace : WordTrace (prefixWord ++ tailWord_1238916) baseStart_1238916 baseEnd_1238916 := by
    simpa [prefixWord, tailWord_1238916, baseEnd_1238916] using wordTrace_append hprefix tailTrace_1238916
  have hstable : (prefixWord ++ tailWord_1238916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238916).length < 2 ^ (prefixWord ++ tailWord_1238916).sum := by decide
  have hdescent : baseEnd_1238916 < baseStart_1238916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238933 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_1238933 : Nat := 118140960795 + 1238933 * 2 ^ 59
def prefixEnd_1238933 : Nat := 4983230072969 + 3 ^ 40 * 1238933 * 2
def baseEnd_1238933 : Nat := 636168127716906402639757

theorem tailTrace_1238933 : CollatzResearch.WordTrace tailWord_1238933 prefixEnd_1238933 636168127716906402639757 := by
  unfold tailWord_1238933
  simp only [CollatzResearch.WordTrace]
  refine ⟨45187598820564808755737453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30125065880376539170491635 45187598820564808755737453)
  ·
    refine ⟨16945349557711803283401545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45187598820564808755737453 16945349557711803283401545)
    ·
      refine ⟨12709012168283852462551159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16945349557711803283401545 12709012168283852462551159)
      ·
        refine ⟨19063518252425778693826739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12709012168283852462551159 19063518252425778693826739)
        ·
          refine ⟨28595277378638668040740109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19063518252425778693826739 28595277378638668040740109)
          ·
            refine ⟨10723229016989500515277541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28595277378638668040740109 10723229016989500515277541)
            ·
              refine ⟨2010605440685531346614539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10723229016989500515277541 2010605440685531346614539)
              ·
                refine ⟨3015908161028297019921809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010605440685531346614539 3015908161028297019921809)
                ·
                  refine ⟨2261931120771222764941357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3015908161028297019921809 2261931120771222764941357)
                  ·
                    refine ⟨848224170289208536853009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261931120771222764941357 848224170289208536853009)
                    ·
                      refine ⟨636168127716906402639757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848224170289208536853009 636168127716906402639757)
                      ·
                        rfl

theorem cell23_1238933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_1238933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238933 prefixEnd_1238933 := by exact prefixLift 1238933
  have htrace : WordTrace (prefixWord ++ tailWord_1238933) baseStart_1238933 baseEnd_1238933 := by
    simpa [prefixWord, tailWord_1238933, baseEnd_1238933] using wordTrace_append hprefix tailTrace_1238933
  have hstable : (prefixWord ++ tailWord_1238933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238933).length < 2 ^ (prefixWord ++ tailWord_1238933).sum := by decide
  have hdescent : baseEnd_1238933 < baseStart_1238933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238959 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_1238959 : Nat := 118140960795 + 1238959 * 2 ^ 59
def prefixEnd_1238959 : Nat := 4983230072969 + 3 ^ 40 * 1238959 * 2
def baseEnd_1238959 : Nat := 636181478213923300914637

theorem tailTrace_1238959 : CollatzResearch.WordTrace tailWord_1238959 prefixEnd_1238959 636181478213923300914637 := by
  unfold tailWord_1238959
  simp only [CollatzResearch.WordTrace]
  refine ⟨45188547118470615196183931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30125698078980410130789287 45188547118470615196183931)
  ·
    refine ⟨67782820677705922794275897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45188547118470615196183931 67782820677705922794275897)
    ·
      refine ⟨50837115508279442095706923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67782820677705922794275897 50837115508279442095706923)
      ·
        refine ⟨76255673262419163143560385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50837115508279442095706923 76255673262419163143560385)
        ·
          refine ⟨57191754946814372357670289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76255673262419163143560385 57191754946814372357670289)
          ·
            refine ⟨42893816210110779268252717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57191754946814372357670289 42893816210110779268252717)
            ·
              refine ⟨16085181078791542225594769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42893816210110779268252717 16085181078791542225594769)
              ·
                refine ⟨12063885809093656669196077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16085181078791542225594769 12063885809093656669196077)
                ·
                  refine ⟨4523957178410121250948529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12063885809093656669196077 4523957178410121250948529)
                  ·
                    refine ⟨3392967883807590938211397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4523957178410121250948529 3392967883807590938211397)
                    ·
                      refine ⟨636181478213923300914637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3392967883807590938211397 636181478213923300914637)
                      ·
                        rfl

theorem cell23_1238959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_1238959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238959 prefixEnd_1238959 := by exact prefixLift 1238959
  have htrace : WordTrace (prefixWord ++ tailWord_1238959) baseStart_1238959 baseEnd_1238959 := by
    simpa [prefixWord, tailWord_1238959, baseEnd_1238959] using wordTrace_append hprefix tailTrace_1238959
  have hstable : (prefixWord ++ tailWord_1238959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238959).length < 2 ^ (prefixWord ++ tailWord_1238959).sum := by decide
  have hdescent : baseEnd_1238959 < baseStart_1238959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238963 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 3, 2, 2]
def baseStart_1238963 : Nat := 118140960795 + 1238963 * 2 ^ 59
def prefixEnd_1238963 : Nat := 4983230072969 + 3 ^ 40 * 1238963 * 2
def baseEnd_1238963 : Nat := 636183532136541285264619

theorem tailTrace_1238963 : CollatzResearch.WordTrace tailWord_1238963 prefixEnd_1238963 636183532136541285264619 := by
  unfold tailWord_1238963
  simp only [CollatzResearch.WordTrace]
  refine ⟨45188693010456123879329543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30125795340304082586219695 45188693010456123879329543)
  ·
    refine ⟨67783039515684185818994315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45188693010456123879329543 67783039515684185818994315)
    ·
      refine ⟨101674559273526278728491473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67783039515684185818994315 101674559273526278728491473)
      ·
        refine ⟨76255919455144709046368605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101674559273526278728491473 76255919455144709046368605)
        ·
          refine ⟨28595969795679265892388227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76255919455144709046368605 28595969795679265892388227)
          ·
            refine ⟨42893954693518898838582341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28595969795679265892388227 42893954693518898838582341)
            ·
              refine ⟨8042616505034793532234189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42893954693518898838582341 8042616505034793532234189)
              ·
                refine ⟨3015981189388047574587821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8042616505034793532234189 3015981189388047574587821)
                ·
                  refine ⟨1130992946020517840470433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3015981189388047574587821 1130992946020517840470433)
                  ·
                    refine ⟨848244709515388380352825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1130992946020517840470433 848244709515388380352825)
                    ·
                      refine ⟨636183532136541285264619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848244709515388380352825 636183532136541285264619)
                      ·
                        rfl

theorem cell23_1238963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 2, 2].length) (baseStart_1238963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238963 prefixEnd_1238963 := by exact prefixLift 1238963
  have htrace : WordTrace (prefixWord ++ tailWord_1238963) baseStart_1238963 baseEnd_1238963 := by
    simpa [prefixWord, tailWord_1238963, baseEnd_1238963] using wordTrace_append hprefix tailTrace_1238963
  have hstable : (prefixWord ++ tailWord_1238963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238963).length < 2 ^ (prefixWord ++ tailWord_1238963).sum := by decide
  have hdescent : baseEnd_1238963 < baseStart_1238963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238973 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1238973 : Nat := 118140960795 + 1238973 * 2 ^ 59
def prefixEnd_1238973 : Nat := 4983230072969 + 3 ^ 40 * 1238973 * 2
def baseEnd_1238973 : Nat := 212062888981028748713191

theorem tailTrace_1238973 : CollatzResearch.WordTrace tailWord_1238973 prefixEnd_1238973 212062888981028748713191 := by
  unfold tailWord_1238973
  simp only [CollatzResearch.WordTrace]
  refine ⟨45189057740419895587193573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30126038493613263724795715 45189057740419895587193573)
  ·
    refine ⟨8472948326328730422598795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45189057740419895587193573 8472948326328730422598795)
    ·
      refine ⟨12709422489493095633898193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8472948326328730422598795 12709422489493095633898193)
      ·
        refine ⟨9532066867119821725423645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12709422489493095633898193 9532066867119821725423645)
        ·
          refine ⟨3574525075169933147033867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9532066867119821725423645 3574525075169933147033867)
          ·
            refine ⟨5361787612754899720550801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574525075169933147033867 5361787612754899720550801)
            ·
              refine ⟨4021340709566174790413101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361787612754899720550801 4021340709566174790413101)
              ·
                refine ⟨1508002766087315546404913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021340709566174790413101 1508002766087315546404913)
                ·
                  refine ⟨1131002074565486659803685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1508002766087315546404913 1131002074565486659803685)
                  ·
                    refine ⟨212062888981028748713191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131002074565486659803685 212062888981028748713191)
                    ·
                      rfl

theorem cell23_1238973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1238973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238973 prefixEnd_1238973 := by exact prefixLift 1238973
  have htrace : WordTrace (prefixWord ++ tailWord_1238973) baseStart_1238973 baseEnd_1238973 := by
    simpa [prefixWord, tailWord_1238973, baseEnd_1238973] using wordTrace_append hprefix tailTrace_1238973
  have hstable : (prefixWord ++ tailWord_1238973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238973).length < 2 ^ (prefixWord ++ tailWord_1238973).sum := by decide
  have hdescent : baseEnd_1238973 < baseStart_1238973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238976 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_1238976 : Nat := 118140960795 + 1238976 * 2 ^ 59
def prefixEnd_1238976 : Nat := 4983230072969 + 3 ^ 40 * 1238976 * 2
def baseEnd_1238976 : Nat := 636190207385049734402059

theorem tailTrace_1238976 : CollatzResearch.WordTrace tailWord_1238976 prefixEnd_1238976 636190207385049734402059 := by
  unfold tailWord_1238976
  simp only [CollatzResearch.WordTrace]
  refine ⟨22594583579704513549776391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30126111439606018066368521 22594583579704513549776391)
  ·
    refine ⟨33891875369556770324664587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22594583579704513549776391 33891875369556770324664587)
    ·
      refine ⟨50837813054335155486996881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33891875369556770324664587 50837813054335155486996881)
      ·
        refine ⟨38128359790751366615247661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50837813054335155486996881 38128359790751366615247661)
        ·
          refine ⟨14298134921531762480717873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38128359790751366615247661 14298134921531762480717873)
          ·
            refine ⟨10723601191148821860538405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298134921531762480717873 10723601191148821860538405)
            ·
              refine ⟨2010675223340404098850951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10723601191148821860538405 2010675223340404098850951)
              ·
                refine ⟨3016012835010606148276427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010675223340404098850951 3016012835010606148276427)
                ·
                  refine ⟨4524019252515909222414641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016012835010606148276427 4524019252515909222414641)
                  ·
                    refine ⟨3393014439386931916810981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524019252515909222414641 3393014439386931916810981)
                    ·
                      refine ⟨636190207385049734402059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3393014439386931916810981 636190207385049734402059)
                      ·
                        rfl

theorem cell23_1238976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_1238976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238976 prefixEnd_1238976 := by exact prefixLift 1238976
  have htrace : WordTrace (prefixWord ++ tailWord_1238976) baseStart_1238976 baseEnd_1238976 := by
    simpa [prefixWord, tailWord_1238976, baseEnd_1238976] using wordTrace_append hprefix tailTrace_1238976
  have hstable : (prefixWord ++ tailWord_1238976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238976).length < 2 ^ (prefixWord ++ tailWord_1238976).sum := by decide
  have hdescent : baseEnd_1238976 < baseStart_1238976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238997 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1238997 : Nat := 118140960795 + 1238997 * 2 ^ 59
def prefixEnd_1238997 : Nat := 4983230072969 + 3 ^ 40 * 1238997 * 2
def baseEnd_1238997 : Nat := 636200990478794152239463

theorem tailTrace_1238997 : CollatzResearch.WordTrace tailWord_1238997 prefixEnd_1238997 636200990478794152239463 := by
  unfold tailWord_1238997
  simp only [CollatzResearch.WordTrace]
  refine ⟨45189933092332947686067245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30126622061555298457378163 45189933092332947686067245)
  ·
    refine ⟨16946224909624855382275217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45189933092332947686067245 16946224909624855382275217)
    ·
      refine ⟨12709668682218641536706413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16946224909624855382275217 12709668682218641536706413)
      ·
        refine ⟨4766125755831990576264905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12709668682218641536706413 4766125755831990576264905)
        ·
          refine ⟨3574594316873992932198679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4766125755831990576264905 3574594316873992932198679)
          ·
            refine ⟨5361891475310989398298019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574594316873992932198679 5361891475310989398298019)
            ·
              refine ⟨8042837212966484097447029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361891475310989398298019 8042837212966484097447029)
              ·
                refine ⟨754015988715607884135659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8042837212966484097447029 754015988715607884135659)
                ·
                  refine ⟨1131023983073411826203489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754015988715607884135659 1131023983073411826203489)
                  ·
                    refine ⟨848267987305058869652617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1131023983073411826203489 848267987305058869652617)
                    ·
                      refine ⟨636200990478794152239463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848267987305058869652617 636200990478794152239463)
                      ·
                        rfl

theorem cell23_1238997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1238997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1238997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1238997 prefixEnd_1238997 := by exact prefixLift 1238997
  have htrace : WordTrace (prefixWord ++ tailWord_1238997) baseStart_1238997 baseEnd_1238997 := by
    simpa [prefixWord, tailWord_1238997, baseEnd_1238997] using wordTrace_append hprefix tailTrace_1238997
  have hstable : (prefixWord ++ tailWord_1238997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238997).length < 2 ^ (prefixWord ++ tailWord_1238997).sum := by decide
  have hdescent : baseEnd_1238997 < baseStart_1238997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239019 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_1239019 : Nat := 118140960795 + 1239019 * 2 ^ 59
def prefixEnd_1239019 : Nat := 4983230072969 + 3 ^ 40 * 1239019 * 2
def baseEnd_1239019 : Nat := 636212287053193066164361

theorem tailTrace_1239019 : CollatzResearch.WordTrace tailWord_1239019 prefixEnd_1239019 636212287053193066164361 := by
  unfold tailWord_1239019
  simp only [CollatzResearch.WordTrace]
  refine ⟨45190735498253245443368111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30127156998835496962245407 45190735498253245443368111)
  ·
    refine ⟨67786103247379868165052167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45190735498253245443368111 67786103247379868165052167)
    ·
      refine ⟨101679154871069802247578251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67786103247379868165052167 101679154871069802247578251)
      ·
        refine ⟨152518732306604703371367377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101679154871069802247578251 152518732306604703371367377)
        ·
          refine ⟨114389049229953527528525533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152518732306604703371367377 114389049229953527528525533)
          ·
            refine ⟨42895893461232572823197075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114389049229953527528525533 42895893461232572823197075)
            ·
              refine ⟨64343840191848859234795613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42895893461232572823197075 64343840191848859234795613)
              ·
                refine ⟨24128940071943322213048355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64343840191848859234795613 24128940071943322213048355)
                ·
                  refine ⟨36193410107914983319572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24128940071943322213048355 36193410107914983319572533)
                  ·
                    refine ⟨3393132197617029686209925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36193410107914983319572533 3393132197617029686209925)
                    ·
                      refine ⟨636212287053193066164361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3393132197617029686209925 636212287053193066164361)
                      ·
                        rfl

theorem cell23_1239019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_1239019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239019 prefixEnd_1239019 := by exact prefixLift 1239019
  have htrace : WordTrace (prefixWord ++ tailWord_1239019) baseStart_1239019 baseEnd_1239019 := by
    simpa [prefixWord, tailWord_1239019, baseEnd_1239019] using wordTrace_append hprefix tailTrace_1239019
  have hstable : (prefixWord ++ tailWord_1239019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239019).length < 2 ^ (prefixWord ++ tailWord_1239019).sum := by decide
  have hdescent : baseEnd_1239019 < baseStart_1239019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239039 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_1239039 : Nat := 118140960795 + 1239039 * 2 ^ 59
def prefixEnd_1239039 : Nat := 4983230072969 + 3 ^ 40 * 1239039 * 2
def baseEnd_1239039 : Nat := 636222556666282987914269

theorem tailTrace_1239039 : CollatzResearch.WordTrace tailWord_1239039 prefixEnd_1239039 636222556666282987914269 := by
  unfold tailWord_1239039
  simp only [CollatzResearch.WordTrace]
  refine ⟨45191464958180788859096171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30127643305453859239397447 45191464958180788859096171)
  ·
    refine ⟨67787197437271183288644257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45191464958180788859096171 67787197437271183288644257)
    ·
      refine ⟨50840398077953387466483193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67787197437271183288644257 50840398077953387466483193)
      ·
        refine ⟨38130298558465040599862395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50840398077953387466483193 38130298558465040599862395)
        ·
          refine ⟨57195447837697560899793593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38130298558465040599862395 57195447837697560899793593)
          ·
            refine ⟨42896585878273170674845195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57195447837697560899793593 42896585878273170674845195)
            ·
              refine ⟨64344878817409756012267793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42896585878273170674845195 64344878817409756012267793)
              ·
                refine ⟨48258659113057317009200845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64344878817409756012267793 48258659113057317009200845)
                ·
                  refine ⟨18096997167396493878450317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48258659113057317009200845 18096997167396493878450317)
                  ·
                    refine ⟨6786373937773685204418869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18096997167396493878450317 6786373937773685204418869)
                    ·
                      refine ⟨636222556666282987914269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6786373937773685204418869 636222556666282987914269)
                      ·
                        rfl

theorem cell23_1239039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_1239039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239039 prefixEnd_1239039 := by exact prefixLift 1239039
  have htrace : WordTrace (prefixWord ++ tailWord_1239039) baseStart_1239039 baseEnd_1239039 := by
    simpa [prefixWord, tailWord_1239039, baseEnd_1239039] using wordTrace_append hprefix tailTrace_1239039
  have hstable : (prefixWord ++ tailWord_1239039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239039).length < 2 ^ (prefixWord ++ tailWord_1239039).sum := by decide
  have hdescent : baseEnd_1239039 < baseStart_1239039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239059 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 9]
def baseStart_1239059 : Nat := 118140960795 + 1239059 * 2 ^ 59
def prefixEnd_1239059 : Nat := 4983230072969 + 3 ^ 40 * 1239059 * 2
def baseEnd_1239059 : Nat := 70692536253263656629353

theorem tailTrace_1239059 : CollatzResearch.WordTrace tailWord_1239059 prefixEnd_1239059 70692536253263656629353 := by
  unfold tailWord_1239059
  simp only [CollatzResearch.WordTrace]
  refine ⟨45192194418108332274824231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30128129612072221516549487 45192194418108332274824231)
  ·
    refine ⟨67788291627162498412236347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45192194418108332274824231 67788291627162498412236347)
    ·
      refine ⟨101682437440743747618354521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67788291627162498412236347 101682437440743747618354521)
      ·
        refine ⟨76261828080557810713765891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101682437440743747618354521 76261828080557810713765891)
        ·
          refine ⟨114392742120836716070648837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76261828080557810713765891 114392742120836716070648837)
          ·
            refine ⟨21448639147656884263246657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114392742120836716070648837 21448639147656884263246657)
            ·
              refine ⟨16086479360742663197434993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21448639147656884263246657 16086479360742663197434993)
              ·
                refine ⟨12064859520556997398076245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16086479360742663197434993 12064859520556997398076245)
                ·
                  refine ⟨70692536253263656629353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12064859520556997398076245 70692536253263656629353)
                  ·
                    rfl

theorem cell23_1239059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 9].length) (baseStart_1239059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239059 prefixEnd_1239059 := by exact prefixLift 1239059
  have htrace : WordTrace (prefixWord ++ tailWord_1239059) baseStart_1239059 baseEnd_1239059 := by
    simpa [prefixWord, tailWord_1239059, baseEnd_1239059] using wordTrace_append hprefix tailTrace_1239059
  have hstable : (prefixWord ++ tailWord_1239059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239059).length < 2 ^ (prefixWord ++ tailWord_1239059).sum := by decide
  have hdescent : baseEnd_1239059 < baseStart_1239059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239116 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1239116 : Nat := 118140960795 + 1239116 * 2 ^ 59
def prefixEnd_1239116 : Nat := 4983230072969 + 3 ^ 40 * 1239116 * 2
def baseEnd_1239116 : Nat := 636262094676679186651415

theorem tailTrace_1239116 : CollatzResearch.WordTrace tailWord_1239116 prefixEnd_1239116 636262094676679186651415 := by
  unfold tailWord_1239116
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597136689450915504824601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30129515585934554006432801 22597136689450915504824601)
  ·
    refine ⟨16947852517088186628618451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22597136689450915504824601 16947852517088186628618451)
    ·
      refine ⟨25421778775632279942927677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16947852517088186628618451 25421778775632279942927677)
      ·
        refine ⟨9533167040862104978597879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25421778775632279942927677 9533167040862104978597879)
        ·
          refine ⟨14299750561293157467896819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9533167040862104978597879 14299750561293157467896819)
          ·
            refine ⟨21449625841939736201845229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14299750561293157467896819 21449625841939736201845229)
            ·
              refine ⟨8043609690727401075691961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21449625841939736201845229 8043609690727401075691961)
              ·
                refine ⟨6032707268045550806768971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8043609690727401075691961 6032707268045550806768971)
                ·
                  refine ⟨9049060902068326210153457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6032707268045550806768971 9049060902068326210153457)
                  ·
                    refine ⟨6786795676551244657615093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9049060902068326210153457 6786795676551244657615093)
                    ·
                      refine ⟨636262094676679186651415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6786795676551244657615093 636262094676679186651415)
                      ·
                        rfl

theorem cell23_1239116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1239116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239116 prefixEnd_1239116 := by exact prefixLift 1239116
  have htrace : WordTrace (prefixWord ++ tailWord_1239116) baseStart_1239116 baseEnd_1239116 := by
    simpa [prefixWord, tailWord_1239116, baseEnd_1239116] using wordTrace_append hprefix tailTrace_1239116
  have hstable : (prefixWord ++ tailWord_1239116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239116).length < 2 ^ (prefixWord ++ tailWord_1239116).sum := by decide
  have hdescent : baseEnd_1239116 < baseStart_1239116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239153 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_1239153 : Nat := 118140960795 + 1239153 * 2 ^ 59
def prefixEnd_1239153 : Nat := 4983230072969 + 3 ^ 40 * 1239153 * 2
def baseEnd_1239153 : Nat := 212093697820298513962915

theorem tailTrace_1239153 : CollatzResearch.WordTrace tailWord_1239153 prefixEnd_1239153 212093697820298513962915 := by
  unfold tailWord_1239153
  simp only [CollatzResearch.WordTrace]
  refine ⟨45195622879767786328746113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30130415253178524219164075 45195622879767786328746113)
  ·
    refine ⟨33896717159825839746559585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45195622879767786328746113 33896717159825839746559585)
    ·
      refine ⟨25422537869869379809919689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33896717159825839746559585 25422537869869379809919689)
      ·
        refine ⟨19066903402402034857439767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25422537869869379809919689 19066903402402034857439767)
        ·
          refine ⟨28600355103603052286159651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19066903402402034857439767 28600355103603052286159651)
          ·
            refine ⟨42900532655404578429239477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28600355103603052286159651 42900532655404578429239477)
            ·
              refine ⟨4021924936444179227741201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42900532655404578429239477 4021924936444179227741201)
              ·
                refine ⟨3016443702333134420805901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4021924936444179227741201 3016443702333134420805901)
                ·
                  refine ⟨1131166388374925407802213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3016443702333134420805901 1131166388374925407802213)
                  ·
                    refine ⟨212093697820298513962915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131166388374925407802213 212093697820298513962915)
                    ·
                      rfl

theorem cell23_1239153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_1239153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239153 prefixEnd_1239153 := by exact prefixLift 1239153
  have htrace : WordTrace (prefixWord ++ tailWord_1239153) baseStart_1239153 baseEnd_1239153 := by
    simpa [prefixWord, tailWord_1239153, baseEnd_1239153] using wordTrace_append hprefix tailTrace_1239153
  have hstable : (prefixWord ++ tailWord_1239153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239153).length < 2 ^ (prefixWord ++ tailWord_1239153).sum := by decide
  have hdescent : baseEnd_1239153 < baseStart_1239153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239200 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 6]
def baseStart_1239200 : Nat := 118140960795 + 1239200 * 2 ^ 59
def prefixEnd_1239200 : Nat := 4983230072969 + 3 ^ 40 * 1239200 * 2
def baseEnd_1239200 : Nat := 70700580783517428666781

theorem tailTrace_1239200 : CollatzResearch.WordTrace tailWord_1239200 prefixEnd_1239200 70700580783517428666781 := by
  unfold tailWord_1239200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22598668555298756677853527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30131558073731675570471369 22598668555298756677853527)
  ·
    refine ⟨33898002832948135016780291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22598668555298756677853527 33898002832948135016780291)
    ·
      refine ⟨50847004249422202525170437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33898002832948135016780291 50847004249422202525170437)
      ·
        refine ⟨9533813296766662973469457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50847004249422202525170437 9533813296766662973469457)
        ·
          refine ⟨7150359972574997230102093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9533813296766662973469457 7150359972574997230102093)
          ·
            refine ⟨2681384989715623961288285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7150359972574997230102093 2681384989715623961288285)
            ·
              refine ⟨1005519371143358985483107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2681384989715623961288285 1005519371143358985483107)
              ·
                refine ⟨1508279056715038478224661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005519371143358985483107 1508279056715038478224661)
                ·
                  refine ⟨70700580783517428666781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1508279056715038478224661 70700580783517428666781)
                  ·
                    rfl

theorem cell23_1239200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 6].length) (baseStart_1239200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239200 prefixEnd_1239200 := by exact prefixLift 1239200
  have htrace : WordTrace (prefixWord ++ tailWord_1239200) baseStart_1239200 baseEnd_1239200 := by
    simpa [prefixWord, tailWord_1239200, baseEnd_1239200] using wordTrace_append hprefix tailTrace_1239200
  have hstable : (prefixWord ++ tailWord_1239200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239200).length < 2 ^ (prefixWord ++ tailWord_1239200).sum := by decide
  have hdescent : baseEnd_1239200 < baseStart_1239200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239221 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1239221 : Nat := 118140960795 + 1239221 * 2 ^ 59
def prefixEnd_1239221 : Nat := 4983230072969 + 3 ^ 40 * 1239221 * 2
def baseEnd_1239221 : Nat := 212105336715133758612811

theorem tailTrace_1239221 : CollatzResearch.WordTrace tailWord_1239221 prefixEnd_1239221 212105336715133758612811 := by
  unfold tailWord_1239221
  simp only [CollatzResearch.WordTrace]
  refine ⟨45198103043521433942221517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30132068695680955961481011 45198103043521433942221517)
  ·
    refine ⟨16949288641320537728333069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45198103043521433942221517 16949288641320537728333069)
    ·
      refine ⟨6355983240495201648124901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16949288641320537728333069 6355983240495201648124901)
      ·
        refine ⟨1191746857592850309023419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6355983240495201648124901 1191746857592850309023419)
        ·
          refine ⟨1787620286389275463535129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191746857592850309023419 1787620286389275463535129)
          ·
            refine ⟨1340715214791956597651347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787620286389275463535129 1340715214791956597651347)
            ·
              refine ⟨2011072822187934896477021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340715214791956597651347 2011072822187934896477021)
              ·
                refine ⟨754152308320475586178883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2011072822187934896477021 754152308320475586178883)
                ·
                  refine ⟨1131228462480713379268325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754152308320475586178883 1131228462480713379268325)
                  ·
                    refine ⟨212105336715133758612811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131228462480713379268325 212105336715133758612811)
                    ·
                      rfl

theorem cell23_1239221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1239221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239221 prefixEnd_1239221 := by exact prefixLift 1239221
  have htrace : WordTrace (prefixWord ++ tailWord_1239221) baseStart_1239221 baseEnd_1239221 := by
    simpa [prefixWord, tailWord_1239221, baseEnd_1239221] using wordTrace_append hprefix tailTrace_1239221
  have hstable : (prefixWord ++ tailWord_1239221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239221).length < 2 ^ (prefixWord ++ tailWord_1239221).sum := by decide
  have hdescent : baseEnd_1239221 < baseStart_1239221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239243 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 4, 4]
def baseStart_1239243 : Nat := 118140960795 + 1239243 * 2 ^ 59
def prefixEnd_1239243 : Nat := 4983230072969 + 3 ^ 40 * 1239243 * 2
def baseEnd_1239243 : Nat := 212109102239933396587777

theorem tailTrace_1239243 : CollatzResearch.WordTrace tailWord_1239243 prefixEnd_1239243 212109102239933396587777 := by
  unfold tailWord_1239243
  simp only [CollatzResearch.WordTrace]
  refine ⟨45198905449441731699522383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30132603632961154466348255 45198905449441731699522383)
  ·
    refine ⟨67798358174162597549283575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45198905449441731699522383 67798358174162597549283575)
    ·
      refine ⟨101697537261243896323925363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67798358174162597549283575 101697537261243896323925363)
      ·
        refine ⟨152546305891865844485888045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101697537261243896323925363 152546305891865844485888045)
        ·
          refine ⟨57204864709449691682208017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152546305891865844485888045 57204864709449691682208017)
          ·
            refine ⟨42903648532087268761656013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57204864709449691682208017 42903648532087268761656013)
            ·
              refine ⟨16088868199532725785621005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42903648532087268761656013 16088868199532725785621005)
              ·
                refine ⟨6033325574824772169607877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16088868199532725785621005 6033325574824772169607877)
                ·
                  refine ⟨1131248545279644781801477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6033325574824772169607877 1131248545279644781801477)
                  ·
                    refine ⟨212109102239933396587777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131248545279644781801477 212109102239933396587777)
                    ·
                      rfl

theorem cell23_1239243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 4].length) (baseStart_1239243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239243 prefixEnd_1239243 := by exact prefixLift 1239243
  have htrace : WordTrace (prefixWord ++ tailWord_1239243) baseStart_1239243 baseEnd_1239243 := by
    simpa [prefixWord, tailWord_1239243, baseEnd_1239243] using wordTrace_append hprefix tailTrace_1239243
  have hstable : (prefixWord ++ tailWord_1239243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239243).length < 2 ^ (prefixWord ++ tailWord_1239243).sum := by decide
  have hdescent : baseEnd_1239243 < baseStart_1239243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239263 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1239263 : Nat := 118140960795 + 1239263 * 2 ^ 59
def prefixEnd_1239263 : Nat := 4983230072969 + 3 ^ 40 * 1239263 * 2
def baseEnd_1239263 : Nat := 636337576332890111513239

theorem tailTrace_1239263 : CollatzResearch.WordTrace tailWord_1239263 prefixEnd_1239263 636337576332890111513239 := by
  unfold tailWord_1239263
  simp only [CollatzResearch.WordTrace]
  refine ⟨45199634909369275115250443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30133089939579516743500295 45199634909369275115250443)
  ·
    refine ⟨67799452364053912672875665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45199634909369275115250443 67799452364053912672875665)
    ·
      refine ⟨50849589273040434504656749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67799452364053912672875665 50849589273040434504656749)
      ·
        refine ⟨19068595977390162939246281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50849589273040434504656749 19068595977390162939246281)
        ·
          refine ⟨14301446983042622204434711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19068595977390162939246281 14301446983042622204434711)
          ·
            refine ⟨21452170474563933306652067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301446983042622204434711 21452170474563933306652067)
            ·
              refine ⟨32178255711845899959978101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21452170474563933306652067 32178255711845899959978101)
              ·
                refine ⟨3016711472985553121247947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32178255711845899959978101 3016711472985553121247947)
                ·
                  refine ⟨4525067209478329681871921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016711472985553121247947 4525067209478329681871921)
                  ·
                    refine ⟨3393800407108747261403941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4525067209478329681871921 3393800407108747261403941)
                    ·
                      refine ⟨636337576332890111513239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3393800407108747261403941 636337576332890111513239)
                      ·
                        rfl

theorem cell23_1239263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1239263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239263 prefixEnd_1239263 := by exact prefixLift 1239263
  have htrace : WordTrace (prefixWord ++ tailWord_1239263) baseStart_1239263 baseEnd_1239263 := by
    simpa [prefixWord, tailWord_1239263, baseEnd_1239263] using wordTrace_append hprefix tailTrace_1239263
  have hstable : (prefixWord ++ tailWord_1239263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239263).length < 2 ^ (prefixWord ++ tailWord_1239263).sum := by decide
  have hdescent : baseEnd_1239263 < baseStart_1239263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239267 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1239267 : Nat := 118140960795 + 1239267 * 2 ^ 59
def prefixEnd_1239267 : Nat := 4983230072969 + 3 ^ 40 * 1239267 * 2
def baseEnd_1239267 : Nat := 636339630255508095863221

theorem tailTrace_1239267 : CollatzResearch.WordTrace tailWord_1239267 prefixEnd_1239267 636339630255508095863221 := by
  unfold tailWord_1239267
  simp only [CollatzResearch.WordTrace]
  refine ⟨45199780801354783798396055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30133187200903189198930703 45199780801354783798396055)
  ·
    refine ⟨67799671202032175697594083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45199780801354783798396055 67799671202032175697594083)
    ·
      refine ⟨101699506803048263546391125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67799671202032175697594083 101699506803048263546391125)
      ·
        refine ⟨1191791095348221838434271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 101699506803048263546391125 1191791095348221838434271)
        ·
          refine ⟨1787686643022332757651407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191791095348221838434271 1787686643022332757651407)
          ·
            refine ⟨2681529964533499136477111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787686643022332757651407 2681529964533499136477111)
            ·
              refine ⟨4022294946800248704715667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681529964533499136477111 4022294946800248704715667)
              ·
                refine ⟨6033442420200373057073501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022294946800248704715667 6033442420200373057073501)
                ·
                  refine ⟨2262540907575139896402563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6033442420200373057073501 2262540907575139896402563)
                  ·
                    refine ⟨3393811361362709844603845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2262540907575139896402563 3393811361362709844603845)
                    ·
                      refine ⟨636339630255508095863221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3393811361362709844603845 636339630255508095863221)
                      ·
                        rfl

theorem cell23_1239267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1239267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239267 prefixEnd_1239267 := by exact prefixLift 1239267
  have htrace : WordTrace (prefixWord ++ tailWord_1239267) baseStart_1239267 baseEnd_1239267 := by
    simpa [prefixWord, tailWord_1239267, baseEnd_1239267] using wordTrace_append hprefix tailTrace_1239267
  have hstable : (prefixWord ++ tailWord_1239267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239267).length < 2 ^ (prefixWord ++ tailWord_1239267).sum := by decide
  have hdescent : baseEnd_1239267 < baseStart_1239267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239317 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_1239317 : Nat := 118140960795 + 1239317 * 2 ^ 59
def prefixEnd_1239317 : Nat := 4983230072969 + 3 ^ 40 * 1239317 * 2
def baseEnd_1239317 : Nat := 636365304288232900237991

theorem tailTrace_1239317 : CollatzResearch.WordTrace tailWord_1239317 prefixEnd_1239317 636365304288232900237991 := by
  unfold tailWord_1239317
  simp only [CollatzResearch.WordTrace]
  refine ⟨45201604451173642337716205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30134402967449094891810803 45201604451173642337716205)
  ·
    refine ⟨16950601669190115876643577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45201604451173642337716205 16950601669190115876643577)
    ·
      refine ⟨12712951251892586907482683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16950601669190115876643577 12712951251892586907482683)
      ·
        refine ⟨19069426877838880361224025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12712951251892586907482683 19069426877838880361224025)
        ·
          refine ⟨14302070158379160270918019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19069426877838880361224025 14302070158379160270918019)
          ·
            refine ⟨21453105237568740406377029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14302070158379160270918019 21453105237568740406377029)
            ·
              refine ⟨4022457232044138826195693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21453105237568740406377029 4022457232044138826195693)
              ·
                refine ⟨1508421462016552059823385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4022457232044138826195693 1508421462016552059823385)
                ·
                  refine ⟨1131316096512414044867539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1508421462016552059823385 1131316096512414044867539)
                  ·
                    refine ⟨1696974144768621067301309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1131316096512414044867539 1696974144768621067301309)
                    ·
                      refine ⟨636365304288232900237991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1696974144768621067301309 636365304288232900237991)
                      ·
                        rfl

theorem cell23_1239317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_1239317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239317 prefixEnd_1239317 := by exact prefixLift 1239317
  have htrace : WordTrace (prefixWord ++ tailWord_1239317) baseStart_1239317 baseEnd_1239317 := by
    simpa [prefixWord, tailWord_1239317, baseEnd_1239317] using wordTrace_append hprefix tailTrace_1239317
  have hstable : (prefixWord ++ tailWord_1239317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239317).length < 2 ^ (prefixWord ++ tailWord_1239317).sum := by decide
  have hdescent : baseEnd_1239317 < baseStart_1239317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239327 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 3, 3, 2]
def baseStart_1239327 : Nat := 118140960795 + 1239327 * 2 ^ 59
def prefixEnd_1239327 : Nat := 4983230072969 + 3 ^ 40 * 1239327 * 2
def baseEnd_1239327 : Nat := 636370439094777861112945

theorem tailTrace_1239327 : CollatzResearch.WordTrace tailWord_1239327 prefixEnd_1239327 636370439094777861112945 := by
  unfold tailWord_1239327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45201969181137414045580235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30134646120758276030386823 45201969181137414045580235)
  ·
    refine ⟨67802953771706121068370353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45201969181137414045580235 67802953771706121068370353)
    ·
      refine ⟨50852215328779590801277765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67802953771706121068370353 50852215328779590801277765)
      ·
        refine ⟨9534790374146173275239581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50852215328779590801277765 9534790374146173275239581)
        ·
          refine ⟨3575546390304814978214843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9534790374146173275239581 3575546390304814978214843)
          ·
            refine ⟨5363319585457222467322265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575546390304814978214843 5363319585457222467322265)
            ·
              refine ⟨4022489689092916850491699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363319585457222467322265 4022489689092916850491699)
              ·
                refine ⟨6033734533639375275737549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022489689092916850491699 6033734533639375275737549)
                ·
                  refine ⟨2262650450114765728401581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6033734533639375275737549 2262650450114765728401581)
                  ·
                    refine ⟨848493918793037148150593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262650450114765728401581 848493918793037148150593)
                    ·
                      refine ⟨636370439094777861112945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848493918793037148150593 636370439094777861112945)
                      ·
                        rfl

theorem cell23_1239327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_1239327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239327 prefixEnd_1239327 := by exact prefixLift 1239327
  have htrace : WordTrace (prefixWord ++ tailWord_1239327) baseStart_1239327 baseEnd_1239327 := by
    simpa [prefixWord, tailWord_1239327, baseEnd_1239327] using wordTrace_append hprefix tailTrace_1239327
  have hstable : (prefixWord ++ tailWord_1239327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239327).length < 2 ^ (prefixWord ++ tailWord_1239327).sum := by decide
  have hdescent : baseEnd_1239327 < baseStart_1239327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239335 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1239335 : Nat := 118140960795 + 1239335 * 2 ^ 59
def prefixEnd_1239335 : Nat := 4983230072969 + 3 ^ 40 * 1239335 * 2
def baseEnd_1239335 : Nat := 636374546940013829812909

theorem tailTrace_1239335 : CollatzResearch.WordTrace tailWord_1239335 prefixEnd_1239335 636374546940013829812909 := by
  unfold tailWord_1239335
  simp only [CollatzResearch.WordTrace]
  refine ⟨45202260965108431411871459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30134840643405620941247639 45202260965108431411871459)
  ·
    refine ⟨67803391447662647117807189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45202260965108431411871459 67803391447662647117807189)
    ·
      refine ⟨794570993527296645911803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 67803391447662647117807189 794570993527296645911803)
      ·
        refine ⟨1191856490290944968867705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794570993527296645911803 1191856490290944968867705)
        ·
          refine ⟨893892367718208726650779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191856490290944968867705 893892367718208726650779)
          ·
            refine ⟨1340838551577313089976169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893892367718208726650779 1340838551577313089976169)
            ·
              refine ⟨1005628913682984817482127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340838551577313089976169 1005628913682984817482127)
              ·
                refine ⟨1508443370524477226223191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005628913682984817482127 1508443370524477226223191)
                ·
                  refine ⟨2262665055786715839334787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508443370524477226223191 2262665055786715839334787)
                  ·
                    refine ⟨3393997583680073759002181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2262665055786715839334787 3393997583680073759002181)
                    ·
                      refine ⟨636374546940013829812909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3393997583680073759002181 636374546940013829812909)
                      ·
                        rfl

theorem cell23_1239335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1239335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239335 prefixEnd_1239335 := by exact prefixLift 1239335
  have htrace : WordTrace (prefixWord ++ tailWord_1239335) baseStart_1239335 baseEnd_1239335 := by
    simpa [prefixWord, tailWord_1239335, baseEnd_1239335] using wordTrace_append hprefix tailTrace_1239335
  have hstable : (prefixWord ++ tailWord_1239335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239335).length < 2 ^ (prefixWord ++ tailWord_1239335).sum := by decide
  have hdescent : baseEnd_1239335 < baseStart_1239335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239338 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1239338 : Nat := 118140960795 + 1239338 * 2 ^ 59
def prefixEnd_1239338 : Nat := 4983230072969 + 3 ^ 40 * 1239338 * 2
def baseEnd_1239338 : Nat := 636376087381977318075395

theorem tailTrace_1239338 : CollatzResearch.WordTrace tailWord_1239338 prefixEnd_1239338 636376087381977318075395 := by
  unfold tailWord_1239338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11300592596024390731057667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30134913589398375282820445 11300592596024390731057667)
  ·
    refine ⟨16950888894036586096586501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11300592596024390731057667 16950888894036586096586501)
    ·
      refine ⟨3178291667631859893109969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16950888894036586096586501 3178291667631859893109969)
      ·
        refine ⟨2383718750723894919832477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3178291667631859893109969 2383718750723894919832477)
        ·
          refine ⟨893894531521460594937179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2383718750723894919832477 893894531521460594937179)
          ·
            refine ⟨1340841797282190892405769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893894531521460594937179 1340841797282190892405769)
            ·
              refine ⟨1005631347961643169304327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340841797282190892405769 1005631347961643169304327)
              ·
                refine ⟨1508447021942464753956491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005631347961643169304327 1508447021942464753956491)
                ·
                  refine ⟨2262670532913697130934737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508447021942464753956491 2262670532913697130934737)
                  ·
                    refine ⟨1697002899685272848201053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262670532913697130934737 1697002899685272848201053)
                    ·
                      refine ⟨636376087381977318075395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697002899685272848201053 636376087381977318075395)
                      ·
                        rfl

theorem cell23_1239338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1239338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239338 prefixEnd_1239338 := by exact prefixLift 1239338
  have htrace : WordTrace (prefixWord ++ tailWord_1239338) baseStart_1239338 baseEnd_1239338 := by
    simpa [prefixWord, tailWord_1239338, baseEnd_1239338] using wordTrace_append hprefix tailTrace_1239338
  have hstable : (prefixWord ++ tailWord_1239338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239338).length < 2 ^ (prefixWord ++ tailWord_1239338).sum := by decide
  have hdescent : baseEnd_1239338 < baseStart_1239338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239343 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_1239343 : Nat := 118140960795 + 1239343 * 2 ^ 59
def prefixEnd_1239343 : Nat := 4983230072969 + 3 ^ 40 * 1239343 * 2
def baseEnd_1239343 : Nat := 636378654785249798512871

theorem tailTrace_1239343 : CollatzResearch.WordTrace tailWord_1239343 prefixEnd_1239343 636378654785249798512871 := by
  unfold tailWord_1239343
  simp only [CollatzResearch.WordTrace]
  refine ⟨45202552749079448778162683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30135035166052965852108455 45202552749079448778162683)
  ·
    refine ⟨67803829123619173167244025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45202552749079448778162683 67803829123619173167244025)
    ·
      refine ⟨50852871842714379875433019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67803829123619173167244025 50852871842714379875433019)
      ·
        refine ⟨76279307764071569813149529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50852871842714379875433019 76279307764071569813149529)
        ·
          refine ⟨57209480823053677359862147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76279307764071569813149529 57209480823053677359862147)
          ·
            refine ⟨85814221234580516039793221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57209480823053677359862147 85814221234580516039793221)
            ·
              refine ⟨16090166481483846757461229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85814221234580516039793221 16090166481483846757461229)
              ·
                refine ⟨6033812430556442534047961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16090166481483846757461229 6033812430556442534047961)
                ·
                  refine ⟨4525359322917331900535971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033812430556442534047961 4525359322917331900535971)
                  ·
                    refine ⟨6788038984375997850803957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525359322917331900535971 6788038984375997850803957)
                    ·
                      refine ⟨636378654785249798512871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6788038984375997850803957 636378654785249798512871)
                      ·
                        rfl

theorem cell23_1239343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_1239343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239343 prefixEnd_1239343 := by exact prefixLift 1239343
  have htrace : WordTrace (prefixWord ++ tailWord_1239343) baseStart_1239343 baseEnd_1239343 := by
    simpa [prefixWord, tailWord_1239343, baseEnd_1239343] using wordTrace_append hprefix tailTrace_1239343
  have hstable : (prefixWord ++ tailWord_1239343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239343).length < 2 ^ (prefixWord ++ tailWord_1239343).sum := by decide
  have hdescent : baseEnd_1239343 < baseStart_1239343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239363 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 7]
def baseStart_1239363 : Nat := 118140960795 + 1239363 * 2 ^ 59
def prefixEnd_1239363 : Nat := 4983230072969 + 3 ^ 40 * 1239363 * 2
def baseEnd_1239363 : Nat := 70709880488704413362531

theorem tailTrace_1239363 : CollatzResearch.WordTrace tailWord_1239363 prefixEnd_1239363 70709880488704413362531 := by
  unfold tailWord_1239363
  simp only [CollatzResearch.WordTrace]
  refine ⟨45203282209006992193890743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30135521472671328129260495 45203282209006992193890743)
  ·
    refine ⟨67804923313510488290836115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45203282209006992193890743 67804923313510488290836115)
    ·
      refine ⟨101707384970265732436254173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67804923313510488290836115 101707384970265732436254173)
      ·
        refine ⟨38140269363849649663595315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101707384970265732436254173 38140269363849649663595315)
        ·
          refine ⟨57210404045774474495392973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38140269363849649663595315 57210404045774474495392973)
          ·
            refine ⟨21453901517165427935772365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57210404045774474495392973 21453901517165427935772365)
            ·
              refine ⟨8045213068937035475914637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21453901517165427935772365 8045213068937035475914637)
              ·
                refine ⟨3016954900851388303467989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8045213068937035475914637 3016954900851388303467989)
                ·
                  refine ⟨70709880488704413362531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3016954900851388303467989 70709880488704413362531)
                  ·
                    rfl

theorem cell23_1239363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 7].length) (baseStart_1239363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239363 prefixEnd_1239363 := by exact prefixLift 1239363
  have htrace : WordTrace (prefixWord ++ tailWord_1239363) baseStart_1239363 baseEnd_1239363 := by
    simpa [prefixWord, tailWord_1239363, baseEnd_1239363] using wordTrace_append hprefix tailTrace_1239363
  have hstable : (prefixWord ++ tailWord_1239363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239363).length < 2 ^ (prefixWord ++ tailWord_1239363).sum := by decide
  have hdescent : baseEnd_1239363 < baseStart_1239363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239380 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1239380 : Nat := 118140960795 + 1239380 * 2 ^ 59
def prefixEnd_1239380 : Nat := 4983230072969 + 3 ^ 40 * 1239380 * 2
def baseEnd_1239380 : Nat := 70710850396607350416689

theorem tailTrace_1239380 : CollatzResearch.WordTrace tailWord_1239380 prefixEnd_1239380 70710850396607350416689 := by
  unfold tailWord_1239380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22601951124972702048629797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30135934833296936064839729 22601951124972702048629797)
  ·
    refine ⟨4237865835932381634118087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22601951124972702048629797 4237865835932381634118087)
    ·
      refine ⟨6356798753898572451177131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4237865835932381634118087 6356798753898572451177131)
      ·
        refine ⟨9535198130847858676765697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6356798753898572451177131 9535198130847858676765697)
        ·
          refine ⟨7151398598135894007574273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9535198130847858676765697 7151398598135894007574273)
          ·
            refine ⟨5363548948601920505680705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7151398598135894007574273 5363548948601920505680705)
            ·
              refine ⟨4022661711451440379260529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363548948601920505680705 4022661711451440379260529)
              ·
                refine ⟨3016996283588580284445397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022661711451440379260529 3016996283588580284445397)
                ·
                  refine ⟨70710850396607350416689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3016996283588580284445397 70710850396607350416689)
                  ·
                    rfl

theorem cell23_1239380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1239380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239380 prefixEnd_1239380 := by exact prefixLift 1239380
  have htrace : WordTrace (prefixWord ++ tailWord_1239380) baseStart_1239380 baseEnd_1239380 := by
    simpa [prefixWord, tailWord_1239380, baseEnd_1239380] using wordTrace_append hprefix tailTrace_1239380
  have hstable : (prefixWord ++ tailWord_1239380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239380).length < 2 ^ (prefixWord ++ tailWord_1239380).sum := by decide
  have hdescent : baseEnd_1239380 < baseStart_1239380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239397 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 5]
def baseStart_1239397 : Nat := 118140960795 + 1239397 * 2 ^ 59
def prefixEnd_1239397 : Nat := 4983230072969 + 3 ^ 40 * 1239397 * 2
def baseEnd_1239397 : Nat := 70711820304510287470847

theorem tailTrace_1239397 : CollatzResearch.WordTrace tailWord_1239397 prefixEnd_1239397 70711820304510287470847 := by
  unfold tailWord_1239397
  simp only [CollatzResearch.WordTrace]
  refine ⟨45204522290883816000628445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30136348193922544000418963 45204522290883816000628445)
  ·
    refine ⟨16951695859081431000235667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45204522290883816000628445 16951695859081431000235667)
    ·
      refine ⟨25427543788622146500353501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16951695859081431000235667 25427543788622146500353501)
      ·
        refine ⟨9535328920733304937632563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25427543788622146500353501 9535328920733304937632563)
        ·
          refine ⟨14302993381099957406448845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9535328920733304937632563 14302993381099957406448845)
          ·
            refine ⟨5363622517912484027418317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14302993381099957406448845 5363622517912484027418317)
            ·
              refine ⟨2011358444217181510281869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5363622517912484027418317 2011358444217181510281869)
              ·
                refine ⟨754259416581443066355701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2011358444217181510281869 754259416581443066355701)
                ·
                  refine ⟨70711820304510287470847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 754259416581443066355701 70711820304510287470847)
                  ·
                    rfl

theorem cell23_1239397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_1239397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239397 prefixEnd_1239397 := by exact prefixLift 1239397
  have htrace : WordTrace (prefixWord ++ tailWord_1239397) baseStart_1239397 baseEnd_1239397 := by
    simpa [prefixWord, tailWord_1239397, baseEnd_1239397] using wordTrace_append hprefix tailTrace_1239397
  have hstable : (prefixWord ++ tailWord_1239397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239397).length < 2 ^ (prefixWord ++ tailWord_1239397).sum := by decide
  have hdescent : baseEnd_1239397 < baseStart_1239397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239403 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_1239403 : Nat := 118140960795 + 1239403 * 2 ^ 59
def prefixEnd_1239403 : Nat := 4983230072969 + 3 ^ 40 * 1239403 * 2
def baseEnd_1239403 : Nat := 636409463624519563762595

theorem tailTrace_1239403 : CollatzResearch.WordTrace tailWord_1239403 prefixEnd_1239403 636409463624519563762595 := by
  unfold tailWord_1239403
  simp only [CollatzResearch.WordTrace]
  refine ⟨45204741128862079025346863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30136494085908052683564575 45204741128862079025346863)
  ·
    refine ⟨67807111693293118538020295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45204741128862079025346863 67807111693293118538020295)
    ·
      refine ⟨101710667539939677807030443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67807111693293118538020295 101710667539939677807030443)
      ·
        refine ⟨152566001309909516710545665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101710667539939677807030443 152566001309909516710545665)
        ·
          refine ⟨114424500982432137532909249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152566001309909516710545665 114424500982432137532909249)
          ·
            refine ⟨85818375736824103149681937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114424500982432137532909249 85818375736824103149681937)
            ·
              refine ⟨64363781802618077362261453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85818375736824103149681937 64363781802618077362261453)
              ·
                refine ⟨24136418175981779010848045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64363781802618077362261453 24136418175981779010848045)
                ·
                  refine ⟨9051156815993167129068017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24136418175981779010848045 9051156815993167129068017)
                  ·
                    refine ⟨6788367611994875346801013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9051156815993167129068017 6788367611994875346801013)
                    ·
                      refine ⟨636409463624519563762595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6788367611994875346801013 636409463624519563762595)
                      ·
                        rfl

theorem cell23_1239403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_1239403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239403 prefixEnd_1239403 := by exact prefixLift 1239403
  have htrace : WordTrace (prefixWord ++ tailWord_1239403) baseStart_1239403 baseEnd_1239403 := by
    simpa [prefixWord, tailWord_1239403, baseEnd_1239403] using wordTrace_append hprefix tailTrace_1239403
  have hstable : (prefixWord ++ tailWord_1239403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239403).length < 2 ^ (prefixWord ++ tailWord_1239403).sum := by decide
  have hdescent : baseEnd_1239403 < baseStart_1239403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239410 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1239410 : Nat := 118140960795 + 1239410 * 2 ^ 59
def prefixEnd_1239410 : Nat := 4983230072969 + 3 ^ 40 * 1239410 * 2
def baseEnd_1239410 : Nat := 212137685996367012125021

theorem tailTrace_1239410 : CollatzResearch.WordTrace tailWord_1239410 prefixEnd_1239410 212137685996367012125021 := by
  unfold tailWord_1239410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11301249109959179805212921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30136664293224479480567789 11301249109959179805212921)
  ·
    refine ⟨8475936832469384853909691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11301249109959179805212921 8475936832469384853909691)
    ·
      refine ⟨12713905248704077280864537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8475936832469384853909691 12713905248704077280864537)
      ·
        refine ⟨9535428936528057960648403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12713905248704077280864537 9535428936528057960648403)
        ·
          refine ⟨14303143404792086940972605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9535428936528057960648403 14303143404792086940972605)
          ·
            refine ⟨5363678776797032602864727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14303143404792086940972605 5363678776797032602864727)
            ·
              refine ⟨8045518165195548904297091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363678776797032602864727 8045518165195548904297091)
              ·
                refine ⟨12068277247793323356445637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8045518165195548904297091 12068277247793323356445637)
                ·
                  refine ⟨2262801983961248129333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12068277247793323356445637 2262801983961248129333557)
                  ·
                    refine ⟨212137685996367012125021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2262801983961248129333557 212137685996367012125021)
                    ·
                      rfl

theorem cell23_1239410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1239410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239410 prefixEnd_1239410 := by exact prefixLift 1239410
  have htrace : WordTrace (prefixWord ++ tailWord_1239410) baseStart_1239410 baseEnd_1239410 := by
    simpa [prefixWord, tailWord_1239410, baseEnd_1239410] using wordTrace_append hprefix tailTrace_1239410
  have hstable : (prefixWord ++ tailWord_1239410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239410).length < 2 ^ (prefixWord ++ tailWord_1239410).sum := by decide
  have hdescent : baseEnd_1239410 < baseStart_1239410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239444 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1239444 : Nat := 118140960795 + 1239444 * 2 ^ 59
def prefixEnd_1239444 : Nat := 4983230072969 + 3 ^ 40 * 1239444 * 2
def baseEnd_1239444 : Nat := 212143505443784634449969

theorem tailTrace_1239444 : CollatzResearch.WordTrace tailWord_1239444 prefixEnd_1239444 212143505443784634449969 := by
  unfold tailWord_1239444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22603118260856771513794693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30137491014475695351726257 22603118260856771513794693)
  ·
    refine ⟨4238084673910644658836505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22603118260856771513794693 4238084673910644658836505)
    ·
      refine ⟨3178563505432983494127379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4238084673910644658836505 3178563505432983494127379)
      ·
        refine ⟨4767845258149475241191069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178563505432983494127379 4767845258149475241191069)
        ·
          refine ⟨1787941971806053215446651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4767845258149475241191069 1787941971806053215446651)
          ·
            refine ⟨2681912957709079823169977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787941971806053215446651 2681912957709079823169977)
            ·
              refine ⟨2011434718281809867377483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681912957709079823169977 2011434718281809867377483)
              ·
                refine ⟨3017152077422714801066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011434718281809867377483 3017152077422714801066225)
                ·
                  refine ⟨2262864058067036100799669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3017152077422714801066225 2262864058067036100799669)
                  ·
                    refine ⟨212143505443784634449969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2262864058067036100799669 212143505443784634449969)
                    ·
                      rfl

theorem cell23_1239444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1239444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239444 prefixEnd_1239444 := by exact prefixLift 1239444
  have htrace : WordTrace (prefixWord ++ tailWord_1239444) baseStart_1239444 baseEnd_1239444 := by
    simpa [prefixWord, tailWord_1239444, baseEnd_1239444] using wordTrace_append hprefix tailTrace_1239444
  have hstable : (prefixWord ++ tailWord_1239444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239444).length < 2 ^ (prefixWord ++ tailWord_1239444).sum := by decide
  have hdescent : baseEnd_1239444 < baseStart_1239444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239464 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1239464 : Nat := 118140960795 + 1239464 * 2 ^ 59
def prefixEnd_1239464 : Nat := 4983230072969 + 3 ^ 40 * 1239464 * 2
def baseEnd_1239464 : Nat := 636440785944443825099815

theorem tailTrace_1239464 : CollatzResearch.WordTrace tailWord_1239464 prefixEnd_1239464 636440785944443825099815 := by
  unfold tailWord_1239464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22603482990820543221658723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30137977321094057628878297 22603482990820543221658723)
  ·
    refine ⟨33905224486230814832488085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22603482990820543221658723 33905224486230814832488085)
    ·
      refine ⟨1589307397792069445272879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33905224486230814832488085 1589307397792069445272879)
      ·
        refine ⟨2383961096688104167909319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589307397792069445272879 2383961096688104167909319)
        ·
          refine ⟨3575941645032156251863979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383961096688104167909319 3575941645032156251863979)
          ·
            refine ⟨5363912467548234377795969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575941645032156251863979 5363912467548234377795969)
            ·
              refine ⟨4022934350661175783346977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363912467548234377795969 4022934350661175783346977)
              ·
                refine ⟨3017200762995881837510233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022934350661175783346977 3017200762995881837510233)
                ·
                  refine ⟨2262900572246911378132675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3017200762995881837510233 2262900572246911378132675)
                  ·
                    refine ⟨3394350858370367067199013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2262900572246911378132675 3394350858370367067199013)
                    ·
                      refine ⟨636440785944443825099815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3394350858370367067199013 636440785944443825099815)
                      ·
                        rfl

theorem cell23_1239464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1239464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239464 prefixEnd_1239464 := by exact prefixLift 1239464
  have htrace : WordTrace (prefixWord ++ tailWord_1239464) baseStart_1239464 baseEnd_1239464 := by
    simpa [prefixWord, tailWord_1239464, baseEnd_1239464] using wordTrace_append hprefix tailTrace_1239464
  have hstable : (prefixWord ++ tailWord_1239464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239464).length < 2 ^ (prefixWord ++ tailWord_1239464).sum := by decide
  have hdescent : baseEnd_1239464 < baseStart_1239464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239474 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_1239474 : Nat := 118140960795 + 1239474 * 2 ^ 59
def prefixEnd_1239474 : Nat := 4983230072969 + 3 ^ 40 * 1239474 * 2
def baseEnd_1239474 : Nat := 212148640250329595324923

theorem tailTrace_1239474 : CollatzResearch.WordTrace tailWord_1239474 prefixEnd_1239474 212148640250329595324923 := by
  unfold tailWord_1239474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11301832677901214537795369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30138220474403238767454317 11301832677901214537795369)
  ·
    refine ⟨8476374508425910903346527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11301832677901214537795369 8476374508425910903346527)
    ·
      refine ⟨12714561762638866355019791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8476374508425910903346527 12714561762638866355019791)
      ·
        refine ⟨19071842643958299532529687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12714561762638866355019791 19071842643958299532529687)
        ·
          refine ⟨28607763965937449298794531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19071842643958299532529687 28607763965937449298794531)
          ·
            refine ⟨42911645948906173948191797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28607763965937449298794531 42911645948906173948191797)
            ·
              refine ⟨4022966807709953807642981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42911645948906173948191797 4022966807709953807642981)
              ·
                refine ⟨754306276445616338933059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4022966807709953807642981 754306276445616338933059)
                ·
                  refine ⟨1131459414668424508399589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754306276445616338933059 1131459414668424508399589)
                  ·
                    refine ⟨212148640250329595324923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131459414668424508399589 212148640250329595324923)
                    ·
                      rfl

theorem cell23_1239474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_1239474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239474 prefixEnd_1239474 := by exact prefixLift 1239474
  have htrace : WordTrace (prefixWord ++ tailWord_1239474) baseStart_1239474 baseEnd_1239474 := by
    simpa [prefixWord, tailWord_1239474, baseEnd_1239474] using wordTrace_append hprefix tailTrace_1239474
  have hstable : (prefixWord ++ tailWord_1239474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239474).length < 2 ^ (prefixWord ++ tailWord_1239474).sum := by decide
  have hdescent : baseEnd_1239474 < baseStart_1239474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239480 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_1239480 : Nat := 118140960795 + 1239480 * 2 ^ 59
def prefixEnd_1239480 : Nat := 4983230072969 + 3 ^ 40 * 1239480 * 2
def baseEnd_1239480 : Nat := 636449001634915762499741

theorem tailTrace_1239480 : CollatzResearch.WordTrace tailWord_1239480 prefixEnd_1239480 636449001634915762499741 := by
  unfold tailWord_1239480
  simp only [CollatzResearch.WordTrace]
  refine ⟨22603774774791560587949947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30138366366388747450599929 22603774774791560587949947)
  ·
    refine ⟨33905662162187340881924921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22603774774791560587949947 33905662162187340881924921)
    ·
      refine ⟨25429246621640505661443691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33905662162187340881924921 25429246621640505661443691)
      ·
        refine ⟨38143869932460758492165537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25429246621640505661443691 38143869932460758492165537)
        ·
          refine ⟨28607902449345568869124153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38143869932460758492165537 28607902449345568869124153)
          ·
            refine ⟨21455926837009176651843115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28607902449345568869124153 21455926837009176651843115)
            ·
              refine ⟨32183890255513764977764673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21455926837009176651843115 32183890255513764977764673)
              ·
                refine ⟨24137917691635323733323505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32183890255513764977764673 24137917691635323733323505)
                ·
                  refine ⟨18103438268726492799992629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24137917691635323733323505 18103438268726492799992629)
                  ·
                    refine ⟨1697197337693108699999309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18103438268726492799992629 1697197337693108699999309)
                    ·
                      refine ⟨636449001634915762499741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697197337693108699999309 636449001634915762499741)
                      ·
                        rfl

theorem cell23_1239480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_1239480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239480 prefixEnd_1239480 := by exact prefixLift 1239480
  have htrace : WordTrace (prefixWord ++ tailWord_1239480) baseStart_1239480 baseEnd_1239480 := by
    simpa [prefixWord, tailWord_1239480, baseEnd_1239480] using wordTrace_append hprefix tailTrace_1239480
  have hstable : (prefixWord ++ tailWord_1239480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239480).length < 2 ^ (prefixWord ++ tailWord_1239480).sum := by decide
  have hdescent : baseEnd_1239480 < baseStart_1239480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239497 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 3]
def baseStart_1239497 : Nat := 118140960795 + 1239497 * 2 ^ 59
def prefixEnd_1239497 : Nat := 4983230072969 + 3 ^ 40 * 1239497 * 2
def baseEnd_1239497 : Nat := 636457730806042195987163

theorem tailTrace_1239497 : CollatzResearch.WordTrace tailWord_1239497 prefixEnd_1239497 636457730806042195987163 := by
  unfold tailWord_1239497
  simp only [CollatzResearch.WordTrace]
  refine ⟨45208169590521533079268745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30138779727014355386179163 45208169590521533079268745)
  ·
    refine ⟨33906127192891149809451559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45208169590521533079268745 33906127192891149809451559)
    ·
      refine ⟨50859190789336724714177339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33906127192891149809451559 50859190789336724714177339)
      ·
        refine ⟨76288786184005087071266009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50859190789336724714177339 76288786184005087071266009)
        ·
          refine ⟨57216589638003815303449507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76288786184005087071266009 57216589638003815303449507)
          ·
            refine ⟨85824884457005722955174261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57216589638003815303449507 85824884457005722955174261)
            ·
              refine ⟨8046082917844286527047587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85824884457005722955174261 8046082917844286527047587)
              ·
                refine ⟨12069124376766429790571381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8046082917844286527047587 12069124376766429790571381)
                ·
                  refine ⟨1131480410321852792866067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12069124376766429790571381 1131480410321852792866067)
                  ·
                    refine ⟨1697220615482779189299101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1131480410321852792866067 1697220615482779189299101)
                    ·
                      refine ⟨636457730806042195987163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697220615482779189299101 636457730806042195987163)
                      ·
                        rfl

theorem cell23_1239497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_1239497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239497 prefixEnd_1239497 := by exact prefixLift 1239497
  have htrace : WordTrace (prefixWord ++ tailWord_1239497) baseStart_1239497 baseEnd_1239497 := by
    simpa [prefixWord, tailWord_1239497, baseEnd_1239497] using wordTrace_append hprefix tailTrace_1239497
  have hstable : (prefixWord ++ tailWord_1239497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239497).length < 2 ^ (prefixWord ++ tailWord_1239497).sum := by decide
  have hdescent : baseEnd_1239497 < baseStart_1239497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239557 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_1239557 : Nat := 118140960795 + 1239557 * 2 ^ 59
def prefixEnd_1239557 : Nat := 4983230072969 + 3 ^ 40 * 1239557 * 2
def baseEnd_1239557 : Nat := 636488539645311961236887

theorem tailTrace_1239557 : CollatzResearch.WordTrace tailWord_1239557 prefixEnd_1239557 636488539645311961236887 := by
  unfold tailWord_1239557
  simp only [CollatzResearch.WordTrace]
  refine ⟨45210357970304163326452925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30140238646869442217635283 45210357970304163326452925)
  ·
    refine ⟨16953884238864061247419847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45210357970304163326452925 16953884238864061247419847)
    ·
      refine ⟨25430826358296091871129771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16953884238864061247419847 25430826358296091871129771)
      ·
        refine ⟨38146239537444137806694657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25430826358296091871129771 38146239537444137806694657)
        ·
          refine ⟨28609679653083103355020993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38146239537444137806694657 28609679653083103355020993)
          ·
            refine ⟨21457259739812327516265745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28609679653083103355020993 21457259739812327516265745)
            ·
              refine ⟨16092944804859245637199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21457259739812327516265745 16092944804859245637199309)
              ·
                refine ⟨6034854301822217113949741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16092944804859245637199309 6034854301822217113949741)
                ·
                  refine ⟨2263070363183331417731153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6034854301822217113949741 2263070363183331417731153)
                  ·
                    refine ⟨1697302772387498563298365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2263070363183331417731153 1697302772387498563298365)
                    ·
                      refine ⟨636488539645311961236887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697302772387498563298365 636488539645311961236887)
                      ·
                        rfl

theorem cell23_1239557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_1239557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239557 prefixEnd_1239557 := by exact prefixLift 1239557
  have htrace : WordTrace (prefixWord ++ tailWord_1239557) baseStart_1239557 baseEnd_1239557 := by
    simpa [prefixWord, tailWord_1239557, baseEnd_1239557] using wordTrace_append hprefix tailTrace_1239557
  have hstable : (prefixWord ++ tailWord_1239557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239557).length < 2 ^ (prefixWord ++ tailWord_1239557).sum := by decide
  have hdescent : baseEnd_1239557 < baseStart_1239557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239661 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1239661 : Nat := 118140960795 + 1239661 * 2 ^ 59
def prefixEnd_1239661 : Nat := 4983230072969 + 3 ^ 40 * 1239661 * 2
def baseEnd_1239661 : Nat := 636541941633379554336409

theorem tailTrace_1239661 : CollatzResearch.WordTrace tailWord_1239661 prefixEnd_1239661 636541941633379554336409 := by
  unfold tailWord_1239661
  simp only [CollatzResearch.WordTrace]
  refine ⟨45214151161927389088238837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30142767441284926058825891 45214151161927389088238837)
  ·
    refine ⟨4238826671430692727022391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45214151161927389088238837 4238826671430692727022391)
    ·
      refine ⟨6358240007146039090533587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238826671430692727022391 6358240007146039090533587)
      ·
        refine ⟨9537360010719058635800381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6358240007146039090533587 9537360010719058635800381)
        ·
          refine ⟨3576510004019646988425143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9537360010719058635800381 3576510004019646988425143)
          ·
            refine ⟨5364765006029470482637715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576510004019646988425143 5364765006029470482637715)
            ·
              refine ⟨8047147509044205723956573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364765006029470482637715 8047147509044205723956573)
              ·
                refine ⟨3017680315891577146483715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8047147509044205723956573 3017680315891577146483715)
                ·
                  refine ⟨4526520473837365719725573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017680315891577146483715 4526520473837365719725573)
                  ·
                    refine ⟨848722588844506072448545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526520473837365719725573 848722588844506072448545)
                    ·
                      refine ⟨636541941633379554336409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848722588844506072448545 636541941633379554336409)
                      ·
                        rfl

theorem cell23_1239661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1239661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239661 prefixEnd_1239661 := by exact prefixLift 1239661
  have htrace : WordTrace (prefixWord ++ tailWord_1239661) baseStart_1239661 baseEnd_1239661 := by
    simpa [prefixWord, tailWord_1239661, baseEnd_1239661] using wordTrace_append hprefix tailTrace_1239661
  have hstable : (prefixWord ++ tailWord_1239661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239661).length < 2 ^ (prefixWord ++ tailWord_1239661).sum := by decide
  have hdescent : baseEnd_1239661 < baseStart_1239661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239694 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1239694 : Nat := 118140960795 + 1239694 * 2 ^ 59
def prefixEnd_1239694 : Nat := 4983230072969 + 3 ^ 40 * 1239694 * 2
def baseEnd_1239694 : Nat := 636558886494977925223757

theorem tailTrace_1239694 : CollatzResearch.WordTrace tailWord_1239694 prefixEnd_1239694 636558886494977925223757 := by
  unfold tailWord_1239694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651919346350979465523767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30143569847205223816126757 5651919346350979465523767)
  ·
    refine ⟨8477879019526469198285651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5651919346350979465523767 8477879019526469198285651)
    ·
      refine ⟨12716818529289703797428477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8477879019526469198285651 12716818529289703797428477)
      ·
        refine ⟨4768806948483638924035679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12716818529289703797428477 4768806948483638924035679)
        ·
          refine ⟨7153210422725458386053519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4768806948483638924035679 7153210422725458386053519)
          ·
            refine ⟨10729815634088187579080279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7153210422725458386053519 10729815634088187579080279)
            ·
              refine ⟨16094723451132281368620419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729815634088187579080279 16094723451132281368620419)
              ·
                refine ⟨24142085176698422052930629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16094723451132281368620419 24142085176698422052930629)
                ·
                  refine ⟨4526640970630954134924493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24142085176698422052930629 4526640970630954134924493)
                  ·
                    refine ⟨1697490363986607800596685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4526640970630954134924493 1697490363986607800596685)
                    ·
                      refine ⟨636558886494977925223757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697490363986607800596685 636558886494977925223757)
                      ·
                        rfl

theorem cell23_1239694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1239694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239694 prefixEnd_1239694 := by exact prefixLift 1239694
  have htrace : WordTrace (prefixWord ++ tailWord_1239694) baseStart_1239694 baseEnd_1239694 := by
    simpa [prefixWord, tailWord_1239694, baseEnd_1239694] using wordTrace_append hprefix tailTrace_1239694
  have hstable : (prefixWord ++ tailWord_1239694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239694).length < 2 ^ (prefixWord ++ tailWord_1239694).sum := by decide
  have hdescent : baseEnd_1239694 < baseStart_1239694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239737 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1239737 : Nat := 118140960795 + 1239737 * 2 ^ 59
def prefixEnd_1239737 : Nat := 4983230072969 + 3 ^ 40 * 1239737 * 2
def baseEnd_1239737 : Nat := 636580966163121256986059

theorem tailTrace_1239737 : CollatzResearch.WordTrace tailWord_1239737 prefixEnd_1239737 636580966163121256986059 := by
  unfold tailWord_1239737
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216923109652054068005465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30144615406434702712003643 45216923109652054068005465)
  ·
    refine ⟨33912692332239040551004099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45216923109652054068005465 33912692332239040551004099)
    ·
      refine ⟨50869038498358560826506149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33912692332239040551004099 50869038498358560826506149)
      ·
        refine ⟨9537944718442230154969903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50869038498358560826506149 9537944718442230154969903)
        ·
          refine ⟨14306917077663345232454855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9537944718442230154969903 14306917077663345232454855)
          ·
            refine ⟨21460375616495017848682283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14306917077663345232454855 21460375616495017848682283)
            ·
              refine ⟨32190563424742526773023425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21460375616495017848682283 32190563424742526773023425)
              ·
                refine ⟨24142922568556895079767569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32190563424742526773023425 24142922568556895079767569)
                ·
                  refine ⟨18107191926417671309825677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24142922568556895079767569 18107191926417671309825677)
                  ·
                    refine ⟨6790196972406626741184629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18107191926417671309825677 6790196972406626741184629)
                    ·
                      refine ⟨636580966163121256986059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6790196972406626741184629 636580966163121256986059)
                      ·
                        rfl

theorem cell23_1239737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1239737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239737 prefixEnd_1239737 := by exact prefixLift 1239737
  have htrace : WordTrace (prefixWord ++ tailWord_1239737) baseStart_1239737 baseEnd_1239737 := by
    simpa [prefixWord, tailWord_1239737, baseEnd_1239737] using wordTrace_append hprefix tailTrace_1239737
  have hstable : (prefixWord ++ tailWord_1239737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239737).length < 2 ^ (prefixWord ++ tailWord_1239737).sum := by decide
  have hdescent : baseEnd_1239737 < baseStart_1239737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239841 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1239841 : Nat := 118140960795 + 1239841 * 2 ^ 59
def prefixEnd_1239841 : Nat := 4983230072969 + 3 ^ 40 * 1239841 * 2
def baseEnd_1239841 : Nat := 636634368151188850085581

theorem tailTrace_1239841 : CollatzResearch.WordTrace tailWord_1239841 prefixEnd_1239841 636634368151188850085581 := by
  unfold tailWord_1239841
  simp only [CollatzResearch.WordTrace]
  refine ⟨45220716301275279829791377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30147144200850186553194251 45220716301275279829791377)
  ·
    refine ⟨33915537225956459872343533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45220716301275279829791377 33915537225956459872343533)
    ·
      refine ⟨12718326459733672452128825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33915537225956459872343533 12718326459733672452128825)
      ·
        refine ⟨9538744844800254339096619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12718326459733672452128825 9538744844800254339096619)
        ·
          refine ⟨14308117267200381508644929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538744844800254339096619 14308117267200381508644929)
          ·
            refine ⟨10731087950400286131483697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14308117267200381508644929 10731087950400286131483697)
            ·
              refine ⟨8048315962800214598612773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10731087950400286131483697 8048315962800214598612773)
              ·
                refine ⟨1509059243025040237239895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8048315962800214598612773 1509059243025040237239895)
                ·
                  refine ⟨2263588864537560355859843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509059243025040237239895 2263588864537560355859843)
                  ·
                    refine ⟨3395383296806340533789765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2263588864537560355859843 3395383296806340533789765)
                    ·
                      refine ⟨636634368151188850085581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3395383296806340533789765 636634368151188850085581)
                      ·
                        rfl

theorem cell23_1239841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1239841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239841 prefixEnd_1239841 := by exact prefixLift 1239841
  have htrace : WordTrace (prefixWord ++ tailWord_1239841) baseStart_1239841 baseEnd_1239841 := by
    simpa [prefixWord, tailWord_1239841, baseEnd_1239841] using wordTrace_append hprefix tailTrace_1239841
  have hstable : (prefixWord ++ tailWord_1239841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239841).length < 2 ^ (prefixWord ++ tailWord_1239841).sum := by decide
  have hdescent : baseEnd_1239841 < baseStart_1239841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239858 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_1239858 : Nat := 118140960795 + 1239858 * 2 ^ 59
def prefixEnd_1239858 : Nat := 4983230072969 + 3 ^ 40 * 1239858 * 2
def baseEnd_1239858 : Nat := 636643097322315283573003

theorem tailTrace_1239858 : CollatzResearch.WordTrace tailWord_1239858 prefixEnd_1239858 636643097322315283573003 := by
  unfold tailWord_1239858
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305334085553422933290057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30147557561475794488773485 11305334085553422933290057)
  ·
    refine ⟨8479000564165067199967543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11305334085553422933290057 8479000564165067199967543)
    ·
      refine ⟨12718500846247600799951315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479000564165067199967543 12718500846247600799951315)
      ·
        refine ⟨19077751269371401199926973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12718500846247600799951315 19077751269371401199926973)
        ·
          refine ⟨7154156726014275449972615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19077751269371401199926973 7154156726014275449972615)
          ·
            refine ⟨10731235089021413174958923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154156726014275449972615 10731235089021413174958923)
            ·
              refine ⟨16096852633532119762438385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731235089021413174958923 16096852633532119762438385)
              ·
                refine ⟨12072639475149089821828789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16096852633532119762438385 12072639475149089821828789)
                ·
                  refine ⟨1131809950795227170796449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12072639475149089821828789 1131809950795227170796449)
                  ·
                    refine ⟨848857463096420378097337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1131809950795227170796449 848857463096420378097337)
                    ·
                      refine ⟨636643097322315283573003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848857463096420378097337 636643097322315283573003)
                      ·
                        rfl

theorem cell23_1239858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_1239858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239858 prefixEnd_1239858 := by exact prefixLift 1239858
  have htrace : WordTrace (prefixWord ++ tailWord_1239858) baseStart_1239858 baseEnd_1239858 := by
    simpa [prefixWord, tailWord_1239858, baseEnd_1239858] using wordTrace_append hprefix tailTrace_1239858
  have hstable : (prefixWord ++ tailWord_1239858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239858).length < 2 ^ (prefixWord ++ tailWord_1239858).sum := by decide
  have hdescent : baseEnd_1239858 < baseStart_1239858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239875 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 1, 2, 2]
def baseStart_1239875 : Nat := 118140960795 + 1239875 * 2 ^ 59
def prefixEnd_1239875 : Nat := 4983230072969 + 3 ^ 40 * 1239875 * 2
def baseEnd_1239875 : Nat := 636651826493441717060425

theorem tailTrace_1239875 : CollatzResearch.WordTrace tailWord_1239875 prefixEnd_1239875 636651826493441717060425 := by
  unfold tailWord_1239875
  simp only [CollatzResearch.WordTrace]
  refine ⟨45221956383152103636529079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30147970922101402424352719 45221956383152103636529079)
  ·
    refine ⟨67832934574728155454793619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45221956383152103636529079 67832934574728155454793619)
    ·
      refine ⟨101749401862092233182190429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67832934574728155454793619 101749401862092233182190429)
      ·
        refine ⟨38156025698284587443321411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101749401862092233182190429 38156025698284587443321411)
        ·
          refine ⟨57234038547426881164982117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38156025698284587443321411 57234038547426881164982117)
          ·
            refine ⟨10731382227642540218434147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57234038547426881164982117 10731382227642540218434147)
            ·
              refine ⟨16097073341463810327651221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731382227642540218434147 16097073341463810327651221)
              ·
                refine ⟨754550312881116109108651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16097073341463810327651221 754550312881116109108651)
                ·
                  refine ⟨1131825469321674163662977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754550312881116109108651 1131825469321674163662977)
                  ·
                    refine ⟨848869101991255622747233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1131825469321674163662977 848869101991255622747233)
                    ·
                      refine ⟨636651826493441717060425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848869101991255622747233 636651826493441717060425)
                      ·
                        rfl

theorem cell23_1239875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_1239875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239875 prefixEnd_1239875 := by exact prefixLift 1239875
  have htrace : WordTrace (prefixWord ++ tailWord_1239875) baseStart_1239875 baseEnd_1239875 := by
    simpa [prefixWord, tailWord_1239875, baseEnd_1239875] using wordTrace_append hprefix tailTrace_1239875
  have hstable : (prefixWord ++ tailWord_1239875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239875).length < 2 ^ (prefixWord ++ tailWord_1239875).sum := by decide
  have hdescent : baseEnd_1239875 < baseStart_1239875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239885 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1239885 : Nat := 118140960795 + 1239885 * 2 ^ 59
def prefixEnd_1239885 : Nat := 4983230072969 + 3 ^ 40 * 1239885 * 2
def baseEnd_1239885 : Nat := 212218987099995559311793

theorem tailTrace_1239885 : CollatzResearch.WordTrace tailWord_1239885 prefixEnd_1239885 212218987099995559311793 := by
  unfold tailWord_1239885
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222321113115875344393109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30148214075410583562928739 45222321113115875344393109)
  ·
    refine ⟨2119796302177306656768427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45222321113115875344393109 2119796302177306656768427)
    ·
      refine ⟨3179694453265959985152641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119796302177306656768427 3179694453265959985152641)
      ·
        refine ⟨2384770839949469988864481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3179694453265959985152641 2384770839949469988864481)
        ·
          refine ⟨1788578129962102491648361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384770839949469988864481 1788578129962102491648361)
          ·
            refine ⟨1341433597471576868736271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788578129962102491648361 1341433597471576868736271)
            ·
              refine ⟨2012150396207365303104407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341433597471576868736271 2012150396207365303104407)
              ·
                refine ⟨3018225594311047954656611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012150396207365303104407 3018225594311047954656611)
                ·
                  refine ⟨4527338391466571931984917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018225594311047954656611 4527338391466571931984917)
                  ·
                    refine ⟨212218987099995559311793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4527338391466571931984917 212218987099995559311793)
                    ·
                      rfl

theorem cell23_1239885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1239885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239885 prefixEnd_1239885 := by exact prefixLift 1239885
  have htrace : WordTrace (prefixWord ++ tailWord_1239885) baseStart_1239885 baseEnd_1239885 := by
    simpa [prefixWord, tailWord_1239885, baseEnd_1239885] using wordTrace_append hprefix tailTrace_1239885
  have hstable : (prefixWord ++ tailWord_1239885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239885).length < 2 ^ (prefixWord ++ tailWord_1239885).sum := by decide
  have hdescent : baseEnd_1239885 < baseStart_1239885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239904 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1239904 : Nat := 118140960795 + 1239904 * 2 ^ 59
def prefixEnd_1239904 : Nat := 4983230072969 + 3 ^ 40 * 1239904 * 2
def baseEnd_1239904 : Nat := 636666717432422103597791

theorem tailTrace_1239904 : CollatzResearch.WordTrace tailWord_1239904 prefixEnd_1239904 636666717432422103597791 := by
  unfold tailWord_1239904
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611507050023520794667383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30148676066698027726223177 22611507050023520794667383)
  ·
    refine ⟨33917260575035281192001075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22611507050023520794667383 33917260575035281192001075)
    ·
      refine ⟨50875890862552921788001613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33917260575035281192001075 50875890862552921788001613)
      ·
        refine ⟨19078459073457345670500605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50875890862552921788001613 19078459073457345670500605)
        ·
          refine ⟨7154422152546504626437727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19078459073457345670500605 7154422152546504626437727)
          ·
            refine ⟨10731633228819756939656591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154422152546504626437727 10731633228819756939656591)
            ·
              refine ⟨16097449843229635409484887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731633228819756939656591 16097449843229635409484887)
              ·
                refine ⟨24146174764844453114227331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16097449843229635409484887 24146174764844453114227331)
                ·
                  refine ⟨36219262147266679671340997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24146174764844453114227331 36219262147266679671340997)
                  ·
                    refine ⟨6791111652612502438376437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36219262147266679671340997 6791111652612502438376437)
                    ·
                      refine ⟨636666717432422103597791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6791111652612502438376437 636666717432422103597791)
                      ·
                        rfl

theorem cell23_1239904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1239904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239904 prefixEnd_1239904 := by exact prefixLift 1239904
  have htrace : WordTrace (prefixWord ++ tailWord_1239904) baseStart_1239904 baseEnd_1239904 := by
    simpa [prefixWord, tailWord_1239904, baseEnd_1239904] using wordTrace_append hprefix tailTrace_1239904
  have hstable : (prefixWord ++ tailWord_1239904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239904).length < 2 ^ (prefixWord ++ tailWord_1239904).sum := by decide
  have hdescent : baseEnd_1239904 < baseStart_1239904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239908 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_1239908 : Nat := 118140960795 + 1239908 * 2 ^ 59
def prefixEnd_1239908 : Nat := 4983230072969 + 3 ^ 40 * 1239908 * 2
def baseEnd_1239908 : Nat := 636668771355040087947773

theorem tailTrace_1239908 : CollatzResearch.WordTrace tailWord_1239908 prefixEnd_1239908 636668771355040087947773 := by
  unfold tailWord_1239908
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611579996016275136240189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30148773328021700181653585 22611579996016275136240189)
  ·
    refine ⟨8479342498506103176090071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22611579996016275136240189 8479342498506103176090071)
    ·
      refine ⟨12719013747759154764135107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479342498506103176090071 12719013747759154764135107)
      ·
        refine ⟨19078520621638732146202661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719013747759154764135107 19078520621638732146202661)
        ·
          refine ⟨3577222616557262277412999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19078520621638732146202661 3577222616557262277412999)
          ·
            refine ⟨5365833924835893416119499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577222616557262277412999 5365833924835893416119499)
            ·
              refine ⟨8048750887253840124179249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365833924835893416119499 8048750887253840124179249)
              ·
                refine ⟨6036563165440380093134437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8048750887253840124179249 6036563165440380093134437)
                ·
                  refine ⟨1131855593520071267462707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6036563165440380093134437 1131855593520071267462707)
                  ·
                    refine ⟨1697783390280106901194061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1131855593520071267462707 1697783390280106901194061)
                    ·
                      refine ⟨636668771355040087947773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697783390280106901194061 636668771355040087947773)
                      ·
                        rfl

theorem cell23_1239908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_1239908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239908 prefixEnd_1239908 := by exact prefixLift 1239908
  have htrace : WordTrace (prefixWord ++ tailWord_1239908) baseStart_1239908 baseEnd_1239908 := by
    simpa [prefixWord, tailWord_1239908, baseEnd_1239908] using wordTrace_append hprefix tailTrace_1239908
  have hstable : (prefixWord ++ tailWord_1239908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239908).length < 2 ^ (prefixWord ++ tailWord_1239908).sum := by decide
  have hdescent : baseEnd_1239908 < baseStart_1239908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239926 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1239926 : Nat := 118140960795 + 1239926 * 2 ^ 59
def prefixEnd_1239926 : Nat := 4983230072969 + 3 ^ 40 * 1239926 * 2
def baseEnd_1239926 : Nat := 636678014006821017522691

theorem tailTrace_1239926 : CollatzResearch.WordTrace tailWord_1239926 prefixEnd_1239926 636678014006821017522691 := by
  unfold tailWord_1239926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826488531622958709164727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30149211003978226231090421 2826488531622958709164727)
  ·
    refine ⟨4239732797434438063747091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2826488531622958709164727 4239732797434438063747091)
    ·
      refine ⟨6359599196151657095620637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239732797434438063747091 6359599196151657095620637)
      ·
        refine ⟨2384849698556871410857739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6359599196151657095620637 2384849698556871410857739)
        ·
          refine ⟨3577274547835307116286609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384849698556871410857739 3577274547835307116286609)
          ·
            refine ⟨2682955910876480337214957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3577274547835307116286609 2682955910876480337214957)
            ·
              refine ⟨1006108466578680126455609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682955910876480337214957 1006108466578680126455609)
              ·
                refine ⟨754581349934010094841707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006108466578680126455609 754581349934010094841707)
                ·
                  refine ⟨1131872024901015142262561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754581349934010094841707 1131872024901015142262561)
                  ·
                    refine ⟨848904018675761356696921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1131872024901015142262561 848904018675761356696921)
                    ·
                      refine ⟨636678014006821017522691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 848904018675761356696921 636678014006821017522691)
                      ·
                        rfl

theorem cell23_1239926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1239926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239926 prefixEnd_1239926 := by exact prefixLift 1239926
  have htrace : WordTrace (prefixWord ++ tailWord_1239926) baseStart_1239926 baseEnd_1239926 := by
    simpa [prefixWord, tailWord_1239926, baseEnd_1239926] using wordTrace_append hprefix tailTrace_1239926
  have hstable : (prefixWord ++ tailWord_1239926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239926).length < 2 ^ (prefixWord ++ tailWord_1239926).sum := by decide
  have hdescent : baseEnd_1239926 < baseStart_1239926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239998 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1239998 : Nat := 118140960795 + 1239998 * 2 ^ 59
def prefixEnd_1239998 : Nat := 4983230072969 + 3 ^ 40 * 1239998 * 2
def baseEnd_1239998 : Nat := 636714984613944735822359

theorem tailTrace_1239998 : CollatzResearch.WordTrace tailWord_1239998 prefixEnd_1239998 636714984613944735822359 := by
  unfold tailWord_1239998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5653305320213311955407081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30150961707804330428837765 5653305320213311955407081)
  ·
    refine ⟨4239978990159983966555311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5653305320213311955407081 4239978990159983966555311)
    ·
      refine ⟨6359968485239975949832967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239978990159983966555311 6359968485239975949832967)
      ·
        refine ⟨9539952727859963924749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6359968485239975949832967 9539952727859963924749451)
        ·
          refine ⟨14309929091789945887124177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9539952727859963924749451 14309929091789945887124177)
          ·
            refine ⟨10732446818842459415343133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14309929091789945887124177 10732446818842459415343133)
            ·
              refine ⟨4024667557065922280753675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10732446818842459415343133 4024667557065922280753675)
              ·
                refine ⟨6037001335598883421130513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024667557065922280753675 6037001335598883421130513)
                ·
                  refine ⟨4527751001699162565847885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037001335598883421130513 4527751001699162565847885)
                  ·
                    refine ⟨1697906625637185962192957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4527751001699162565847885 1697906625637185962192957)
                    ·
                      refine ⟨636714984613944735822359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1697906625637185962192957 636714984613944735822359)
                      ·
                        rfl

theorem cell23_1239998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1239998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1239998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1239998 prefixEnd_1239998 := by exact prefixLift 1239998
  have htrace : WordTrace (prefixWord ++ tailWord_1239998) baseStart_1239998 baseEnd_1239998 := by
    simpa [prefixWord, tailWord_1239998, baseEnd_1239998] using wordTrace_append hprefix tailTrace_1239998
  have hstable : (prefixWord ++ tailWord_1239998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239998).length < 2 ^ (prefixWord ++ tailWord_1239998).sum := by decide
  have hdescent : baseEnd_1239998 < baseStart_1239998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240018 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1240018 : Nat := 118140960795 + 1240018 * 2 ^ 59
def prefixEnd_1240018 : Nat := 4983230072969 + 3 ^ 40 * 1240018 * 2
def baseEnd_1240018 : Nat := 212241751409011552524089

theorem tailTrace_1240018 : CollatzResearch.WordTrace tailWord_1240018 prefixEnd_1240018 212241751409011552524089 := by
  unfold tailWord_1240018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306793005408509764746177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30151448014422692705989805 11306793005408509764746177)
  ·
    refine ⟨8480094754056382323559633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11306793005408509764746177 8480094754056382323559633)
    ·
      refine ⟨6360071065542286742669725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8480094754056382323559633 6360071065542286742669725)
      ·
        refine ⟨2385026649578357528501147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6360071065542286742669725 2385026649578357528501147)
        ·
          refine ⟨3577539974367536292751721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385026649578357528501147 3577539974367536292751721)
          ·
            refine ⟨2683154980775652219563791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3577539974367536292751721 2683154980775652219563791)
            ·
              refine ⟨4024732471163478329345687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683154980775652219563791 4024732471163478329345687)
              ·
                refine ⟨6037098706745217494018531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024732471163478329345687 6037098706745217494018531)
                ·
                  refine ⟨9055648060117826241027797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037098706745217494018531 9055648060117826241027797)
                  ·
                    refine ⟨212241751409011552524089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9055648060117826241027797 212241751409011552524089)
                    ·
                      rfl

theorem cell23_1240018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1240018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240018 prefixEnd_1240018 := by exact prefixLift 1240018
  have htrace : WordTrace (prefixWord ++ tailWord_1240018) baseStart_1240018 baseEnd_1240018 := by
    simpa [prefixWord, tailWord_1240018, baseEnd_1240018] using wordTrace_append hprefix tailTrace_1240018
  have hstable : (prefixWord ++ tailWord_1240018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240018).length < 2 ^ (prefixWord ++ tailWord_1240018).sum := by decide
  have hdescent : baseEnd_1240018 < baseStart_1240018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240022 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_1240022 : Nat := 118140960795 + 1240022 * 2 ^ 59
def prefixEnd_1240022 : Nat := 4983230072969 + 3 ^ 40 * 1240022 * 2
def baseEnd_1240022 : Nat := 70747478683294737991361

theorem tailTrace_1240022 : CollatzResearch.WordTrace tailWord_1240022 prefixEnd_1240022 70747478683294737991361 := by
  unfold tailWord_1240022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826707369601221733883145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30151545275746365161420213 2826707369601221733883145)
  ·
    refine ⟨2120030527200916300412359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2826707369601221733883145 2120030527200916300412359)
    ·
      refine ⟨3180045790801374450618539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120030527200916300412359 3180045790801374450618539)
      ·
        refine ⟨4770068686202061675927809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3180045790801374450618539 4770068686202061675927809)
        ·
          refine ⟨3577551514651546256945857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770068686202061675927809 3577551514651546256945857)
          ·
            refine ⟨2683163635988659692709393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3577551514651546256945857 2683163635988659692709393)
            ·
              refine ⟨2012372726991494769532045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683163635988659692709393 2012372726991494769532045)
              ·
                refine ⟨754639772621810538574517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012372726991494769532045 754639772621810538574517)
                ·
                  refine ⟨70747478683294737991361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 754639772621810538574517 70747478683294737991361)
                  ·
                    rfl

theorem cell23_1240022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_1240022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240022 prefixEnd_1240022 := by exact prefixLift 1240022
  have htrace : WordTrace (prefixWord ++ tailWord_1240022) baseStart_1240022 baseEnd_1240022 := by
    simpa [prefixWord, tailWord_1240022, baseEnd_1240022] using wordTrace_append hprefix tailTrace_1240022
  have hstable : (prefixWord ++ tailWord_1240022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240022).length < 2 ^ (prefixWord ++ tailWord_1240022).sum := by decide
  have hdescent : baseEnd_1240022 < baseStart_1240022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240125 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1240125 : Nat := 118140960795 + 1240125 * 2 ^ 59
def prefixEnd_1240125 : Nat := 4983230072969 + 3 ^ 40 * 1240125 * 2
def baseEnd_1240125 : Nat := 212260065552355246311425

theorem tailTrace_1240125 : CollatzResearch.WordTrace tailWord_1240125 prefixEnd_1240125 212260065552355246311425 := by
  unfold tailWord_1240125
  simp only [CollatzResearch.WordTrace]
  refine ⟨45231074632246396333129829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30154049754830930888753219 45231074632246396333129829)
  ·
    refine ⟨8480826493546199312461843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45231074632246396333129829 8480826493546199312461843)
    ·
      refine ⟨12721239740319298968692765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8480826493546199312461843 12721239740319298968692765)
      ·
        refine ⟨4770464902619737113259787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12721239740319298968692765 4770464902619737113259787)
        ·
          refine ⟨7155697353929605669889681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4770464902619737113259787 7155697353929605669889681)
          ·
            refine ⟨5366773015447204252417261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7155697353929605669889681 5366773015447204252417261)
            ·
              refine ⟨2012539880792701594656473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5366773015447204252417261 2012539880792701594656473)
              ·
                refine ⟨1509404910594526195992355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012539880792701594656473 1509404910594526195992355)
                ·
                  refine ⟨2264107365891789293988533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509404910594526195992355 2264107365891789293988533)
                  ·
                    refine ⟨212260065552355246311425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2264107365891789293988533 212260065552355246311425)
                    ·
                      rfl

theorem cell23_1240125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1240125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240125 prefixEnd_1240125 := by exact prefixLift 1240125
  have htrace : WordTrace (prefixWord ++ tailWord_1240125) baseStart_1240125 baseEnd_1240125 := by
    simpa [prefixWord, tailWord_1240125, baseEnd_1240125] using wordTrace_append hprefix tailTrace_1240125
  have hstable : (prefixWord ++ tailWord_1240125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240125).length < 2 ^ (prefixWord ++ tailWord_1240125).sum := by decide
  have hdescent : baseEnd_1240125 < baseStart_1240125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240128 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_1240128 : Nat := 118140960795 + 1240128 * 2 ^ 59
def prefixEnd_1240128 : Nat := 4983230072969 + 3 ^ 40 * 1240128 * 2
def baseEnd_1240128 : Nat := 636781737099029227196761

theorem tailTrace_1240128 : CollatzResearch.WordTrace tailWord_1240128 prefixEnd_1240128 636781737099029227196761 := by
  unfold tailWord_1240128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22615592025617763922744519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30154122700823685230326025 22615592025617763922744519)
  ·
    refine ⟨33923388038426645884116779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22615592025617763922744519 33923388038426645884116779)
    ·
      refine ⟨50885082057639968826175169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33923388038426645884116779 50885082057639968826175169)
      ·
        refine ⟨38163811543229976619631377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50885082057639968826175169 38163811543229976619631377)
        ·
          refine ⟨28622858657422482464723533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38163811543229976619631377 28622858657422482464723533)
          ·
            refine ⟨10733571996533430924271325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28622858657422482464723533 10733571996533430924271325)
            ·
              refine ⟨4025089498700036596601747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10733571996533430924271325 4025089498700036596601747)
              ·
                refine ⟨6037634248050054894902621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025089498700036596601747 6037634248050054894902621)
                ·
                  refine ⟨2264112843018770585588483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6037634248050054894902621 2264112843018770585588483)
                  ·
                    refine ⟨3396169264528155878382725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264112843018770585588483 3396169264528155878382725)
                    ·
                      refine ⟨636781737099029227196761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3396169264528155878382725 636781737099029227196761)
                      ·
                        rfl

theorem cell23_1240128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_1240128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240128 prefixEnd_1240128 := by exact prefixLift 1240128
  have htrace : WordTrace (prefixWord ++ tailWord_1240128) baseStart_1240128 baseEnd_1240128 := by
    simpa [prefixWord, tailWord_1240128, baseEnd_1240128] using wordTrace_append hprefix tailTrace_1240128
  have hstable : (prefixWord ++ tailWord_1240128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240128).length < 2 ^ (prefixWord ++ tailWord_1240128).sum := by decide
  have hdescent : baseEnd_1240128 < baseStart_1240128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240138 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_1240138 : Nat := 118140960795 + 1240138 * 2 ^ 59
def prefixEnd_1240138 : Nat := 4983230072969 + 3 ^ 40 * 1240138 * 2
def baseEnd_1240138 : Nat := 212262290635191396023905

theorem tailTrace_1240138 : CollatzResearch.WordTrace tailWord_1240138 prefixEnd_1240138 212262290635191396023905 := by
  unfold tailWord_1240138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11307887195299824888338267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30154365854132866368902045 11307887195299824888338267)
  ·
    refine ⟨16961830792949737332507401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11307887195299824888338267 16961830792949737332507401)
    ·
      refine ⟨12721373094712302999380551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16961830792949737332507401 12721373094712302999380551)
      ·
        refine ⟨19082059642068454499070827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12721373094712302999380551 19082059642068454499070827)
        ·
          refine ⟨28623089463102681748606241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19082059642068454499070827 28623089463102681748606241)
          ·
            refine ⟨21467317097327011311454681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28623089463102681748606241 21467317097327011311454681)
            ·
              refine ⟨16100487822995258483591011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21467317097327011311454681 16100487822995258483591011)
              ·
                refine ⟨24150731734492887725386517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16100487822995258483591011 24150731734492887725386517)
                ·
                  refine ⟨1132065550054354112127493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24150731734492887725386517 1132065550054354112127493)
                  ·
                    refine ⟨212262290635191396023905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132065550054354112127493 212262290635191396023905)
                    ·
                      rfl

theorem cell23_1240138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_1240138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240138 prefixEnd_1240138 := by exact prefixLift 1240138
  have htrace : WordTrace (prefixWord ++ tailWord_1240138) baseStart_1240138 baseEnd_1240138 := by
    simpa [prefixWord, tailWord_1240138, baseEnd_1240138] using wordTrace_append hprefix tailTrace_1240138
  have hstable : (prefixWord ++ tailWord_1240138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240138).length < 2 ^ (prefixWord ++ tailWord_1240138).sum := by decide
  have hdescent : baseEnd_1240138 < baseStart_1240138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240150 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1240150 : Nat := 118140960795 + 1240150 * 2 ^ 59
def prefixEnd_1240150 : Nat := 4983230072969 + 3 ^ 40 * 1240150 * 2
def baseEnd_1240150 : Nat := 212264344557809380373887

theorem tailTrace_1240150 : CollatzResearch.WordTrace tailWord_1240150 prefixEnd_1240150 212264344557809380373887 := by
  unfold tailWord_1240150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826999153572239100174369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30154657638103883735193269 2826999153572239100174369)
  ·
    refine ⟨2120249365179179325130777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2826999153572239100174369 2120249365179179325130777)
    ·
      refine ⟨1590187023884384493848083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2120249365179179325130777 1590187023884384493848083)
      ·
        refine ⟨2385280535826576740772125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590187023884384493848083 2385280535826576740772125)
        ·
          refine ⟨894480200934966277789547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2385280535826576740772125 894480200934966277789547)
          ·
            refine ⟨1341720301402449416684321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894480200934966277789547 1341720301402449416684321)
            ·
              refine ⟨1006290226051837062513241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1341720301402449416684321 1006290226051837062513241)
              ·
                refine ⟨754717669538877796884931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006290226051837062513241 754717669538877796884931)
                ·
                  refine ⟨1132076504308316695327397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754717669538877796884931 1132076504308316695327397)
                  ·
                    refine ⟨212264344557809380373887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132076504308316695327397 212264344557809380373887)
                    ·
                      rfl

theorem cell23_1240150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1240150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240150 prefixEnd_1240150 := by exact prefixLift 1240150
  have htrace : WordTrace (prefixWord ++ tailWord_1240150) baseStart_1240150 baseEnd_1240150 := by
    simpa [prefixWord, tailWord_1240150, baseEnd_1240150] using wordTrace_append hprefix tailTrace_1240150
  have hstable : (prefixWord ++ tailWord_1240150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240150).length < 2 ^ (prefixWord ++ tailWord_1240150).sum := by decide
  have hdescent : baseEnd_1240150 < baseStart_1240150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240182 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1240182 : Nat := 118140960795 + 1240182 * 2 ^ 59
def prefixEnd_1240182 : Nat := 4983230072969 + 3 ^ 40 * 1240182 * 2
def baseEnd_1240182 : Nat := 636809465054372015921513

theorem tailTrace_1240182 : CollatzResearch.WordTrace tailWord_1240182 prefixEnd_1240182 636809465054372015921513 := by
  unfold tailWord_1240182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827072099564993441747175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30155435728693263378636533 2827072099564993441747175)
  ·
    refine ⟨4240608149347490162620763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827072099564993441747175 4240608149347490162620763)
    ·
      refine ⟨6360912224021235243931145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240608149347490162620763 6360912224021235243931145)
      ·
        refine ⟨4770684168015926432948359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6360912224021235243931145 4770684168015926432948359)
        ·
          refine ⟨7156026252023889649422539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4770684168015926432948359 7156026252023889649422539)
          ·
            refine ⟨10734039378035834474133809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156026252023889649422539 10734039378035834474133809)
            ·
              refine ⟨8050529533526875855600357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10734039378035834474133809 8050529533526875855600357)
              ·
                refine ⟨1509474287536289222925067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8050529533526875855600357 1509474287536289222925067)
                ·
                  refine ⟨2264211431304433834387601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509474287536289222925067 2264211431304433834387601)
                  ·
                    refine ⟨1698158573478325375790701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2264211431304433834387601 1698158573478325375790701)
                    ·
                      refine ⟨636809465054372015921513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698158573478325375790701 636809465054372015921513)
                      ·
                        rfl

theorem cell23_1240182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1240182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240182 prefixEnd_1240182 := by exact prefixLift 1240182
  have htrace : WordTrace (prefixWord ++ tailWord_1240182) baseStart_1240182 baseEnd_1240182 := by
    simpa [prefixWord, tailWord_1240182, baseEnd_1240182] using wordTrace_append hprefix tailTrace_1240182
  have hstable : (prefixWord ++ tailWord_1240182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240182).length < 2 ^ (prefixWord ++ tailWord_1240182).sum := by decide
  have hdescent : baseEnd_1240182 < baseStart_1240182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240185 : List Nat := [1, 2, 1, 3, 5, 1, 3, 7]
def baseStart_1240185 : Nat := 118140960795 + 1240185 * 2 ^ 59
def prefixEnd_1240185 : Nat := 4983230072969 + 3 ^ 40 * 1240185 * 2
def baseEnd_1240185 : Nat := 23585592796160574229037

theorem tailTrace_1240185 : CollatzResearch.WordTrace tailWord_1240185 prefixEnd_1240185 23585592796160574229037 := by
  unfold tailWord_1240185
  simp only [CollatzResearch.WordTrace]
  refine ⟨45233263012029026580314009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30155508674686017720209339 45233263012029026580314009)
  ·
    refine ⟨33924947259021769935235507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45233263012029026580314009 33924947259021769935235507)
    ·
      refine ⟨50887420888532654902853261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33924947259021769935235507 50887420888532654902853261)
      ·
        refine ⟨19082782833199745588569973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50887420888532654902853261 19082782833199745588569973)
        ·
          refine ⟨1789010890612476148928435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19082782833199745588569973 1789010890612476148928435)
          ·
            refine ⟨2683516335918714223392653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789010890612476148928435 2683516335918714223392653)
            ·
              refine ⟨1006318625969517833772245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2683516335918714223392653 1006318625969517833772245)
              ·
                refine ⟨23585592796160574229037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1006318625969517833772245 23585592796160574229037)
                ·
                  rfl

theorem cell23_1240185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 7].length) (baseStart_1240185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240185 prefixEnd_1240185 := by exact prefixLift 1240185
  have htrace : WordTrace (prefixWord ++ tailWord_1240185) baseStart_1240185 baseEnd_1240185 := by
    simpa [prefixWord, tailWord_1240185, baseEnd_1240185] using wordTrace_append hprefix tailTrace_1240185
  have hstable : (prefixWord ++ tailWord_1240185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240185).length < 2 ^ (prefixWord ++ tailWord_1240185).sum := by decide
  have hdescent : baseEnd_1240185 < baseStart_1240185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240190 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1240190 : Nat := 118140960795 + 1240190 * 2 ^ 59
def prefixEnd_1240190 : Nat := 4983230072969 + 3 ^ 40 * 1240190 * 2
def baseEnd_1240190 : Nat := 636813572899607984621477

theorem tailTrace_1240190 : CollatzResearch.WordTrace tailWord_1240190 prefixEnd_1240190 636813572899607984621477 := by
  unfold tailWord_1240190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654180672126364054280753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30155630251340608289497349 5654180672126364054280753)
  ·
    refine ⟨4240635504094773040710565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5654180672126364054280753 4240635504094773040710565)
    ·
      refine ⟨795119157017769945133231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4240635504094773040710565 795119157017769945133231)
      ·
        refine ⟨1192678735526654917699847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795119157017769945133231 1192678735526654917699847)
        ·
          refine ⟨1789018103289982376549771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192678735526654917699847 1789018103289982376549771)
          ·
            refine ⟨2683527154934973564824657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789018103289982376549771 2683527154934973564824657)
            ·
              refine ⟨2012645366201230173618493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683527154934973564824657 2012645366201230173618493)
              ·
                refine ⟨754742012325461315106935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012645366201230173618493 754742012325461315106935)
                ·
                  refine ⟨1132113018488191972660403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754742012325461315106935 1132113018488191972660403)
                  ·
                    refine ⟨1698169527732287958990605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132113018488191972660403 1698169527732287958990605)
                    ·
                      refine ⟨636813572899607984621477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698169527732287958990605 636813572899607984621477)
                      ·
                        rfl

theorem cell23_1240190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1240190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240190 prefixEnd_1240190 := by exact prefixLift 1240190
  have htrace : WordTrace (prefixWord ++ tailWord_1240190) baseStart_1240190 baseEnd_1240190 := by
    simpa [prefixWord, tailWord_1240190, baseEnd_1240190] using wordTrace_append hprefix tailTrace_1240190
  have hstable : (prefixWord ++ tailWord_1240190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240190).length < 2 ^ (prefixWord ++ tailWord_1240190).sum := by decide
  have hdescent : baseEnd_1240190 < baseStart_1240190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240195 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 3]
def baseStart_1240195 : Nat := 118140960795 + 1240195 * 2 ^ 59
def prefixEnd_1240195 : Nat := 4983230072969 + 3 ^ 40 * 1240195 * 2
def baseEnd_1240195 : Nat := 636816140302880465058953

theorem tailTrace_1240195 : CollatzResearch.WordTrace tailWord_1240195 prefixEnd_1240195 636816140302880465058953 := by
  unfold tailWord_1240195
  simp only [CollatzResearch.WordTrace]
  refine ⟨45233627741992798288178039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30155751827995198858785359 45233627741992798288178039)
  ·
    refine ⟨67850441612989197432267059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45233627741992798288178039 67850441612989197432267059)
    ·
      refine ⟨101775662419483796148400589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67850441612989197432267059 101775662419483796148400589)
      ·
        refine ⟨38165873407306423555650221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101775662419483796148400589 38165873407306423555650221)
        ·
          refine ⟨14312202527739908833368833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38165873407306423555650221 14312202527739908833368833)
          ·
            refine ⟨10734151895804931625026625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14312202527739908833368833 10734151895804931625026625)
            ·
              refine ⟨8050613921853698718769969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10734151895804931625026625 8050613921853698718769969)
              ·
                refine ⟨6037960441390274039077477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050613921853698718769969 6037960441390274039077477)
                ·
                  refine ⟨1132117582760676382327027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6037960441390274039077477 1132117582760676382327027)
                  ·
                    refine ⟨1698176374141014573490541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132117582760676382327027 1698176374141014573490541)
                    ·
                      refine ⟨636816140302880465058953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698176374141014573490541 636816140302880465058953)
                      ·
                        rfl

theorem cell23_1240195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_1240195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240195 prefixEnd_1240195 := by exact prefixLift 1240195
  have htrace : WordTrace (prefixWord ++ tailWord_1240195) baseStart_1240195 baseEnd_1240195 := by
    simpa [prefixWord, tailWord_1240195, baseEnd_1240195] using wordTrace_append hprefix tailTrace_1240195
  have hstable : (prefixWord ++ tailWord_1240195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240195).length < 2 ^ (prefixWord ++ tailWord_1240195).sum := by decide
  have hdescent : baseEnd_1240195 < baseStart_1240195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240196 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_1240196 : Nat := 118140960795 + 1240196 * 2 ^ 59
def prefixEnd_1240196 : Nat := 4983230072969 + 3 ^ 40 * 1240196 * 2
def baseEnd_1240196 : Nat := 636816653783534961146449

theorem tailTrace_1240196 : CollatzResearch.WordTrace tailWord_1240196 prefixEnd_1240196 636816653783534961146449 := by
  unfold tailWord_1240196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616832107494587729482221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30155776143326116972642961 22616832107494587729482221)
  ·
    refine ⟨8481312040310470398555833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22616832107494587729482221 8481312040310470398555833)
    ·
      refine ⟨6360984030232852798916875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8481312040310470398555833 6360984030232852798916875)
      ·
        refine ⟨9541476045349279198375313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360984030232852798916875 9541476045349279198375313)
        ·
          refine ⟨7156107034011959398781485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9541476045349279198375313 7156107034011959398781485)
          ·
            refine ⟨2683540137754484774543057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7156107034011959398781485 2683540137754484774543057)
            ·
              refine ⟨2012655103315863580907293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683540137754484774543057 2012655103315863580907293)
              ·
                refine ⟨754745663743448842840235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012655103315863580907293 754745663743448842840235)
                ·
                  refine ⟨1132118495615173264260353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754745663743448842840235 1132118495615173264260353)
                  ·
                    refine ⟨849088871711379948195265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132118495615173264260353 849088871711379948195265)
                    ·
                      refine ⟨636816653783534961146449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849088871711379948195265 636816653783534961146449)
                      ·
                        rfl

theorem cell23_1240196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_1240196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240196 prefixEnd_1240196 := by exact prefixLift 1240196
  have htrace : WordTrace (prefixWord ++ tailWord_1240196) baseStart_1240196 baseEnd_1240196 := by
    simpa [prefixWord, tailWord_1240196, baseEnd_1240196] using wordTrace_append hprefix tailTrace_1240196
  have hstable : (prefixWord ++ tailWord_1240196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240196).length < 2 ^ (prefixWord ++ tailWord_1240196).sum := by decide
  have hdescent : baseEnd_1240196 < baseStart_1240196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240229 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_1240229 : Nat := 118140960795 + 1240229 * 2 ^ 59
def prefixEnd_1240229 : Nat := 4983230072969 + 3 ^ 40 * 1240229 * 2
def baseEnd_1240229 : Nat := 636833598645133332033797

theorem tailTrace_1240229 : CollatzResearch.WordTrace tailWord_1240229 prefixEnd_1240229 636833598645133332033797 := by
  unfold tailWord_1240229
  simp only [CollatzResearch.WordTrace]
  refine ⟨45234867823869622094915741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30156578549246414729943827 45234867823869622094915741)
  ·
    refine ⟨16963075433951108285593403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45234867823869622094915741 16963075433951108285593403)
    ·
      refine ⟨25444613150926662428390105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16963075433951108285593403 25444613150926662428390105)
      ·
        refine ⟨19083459863194996821292579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25444613150926662428390105 19083459863194996821292579)
        ·
          refine ⟨28625189794792495231938869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19083459863194996821292579 28625189794792495231938869)
          ·
            refine ⟨2683611543261796427994269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28625189794792495231938869 2683611543261796427994269)
            ·
              refine ⟨1006354328723173660497851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2683611543261796427994269 1006354328723173660497851)
              ·
                refine ⟨1509531493084760490746777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006354328723173660497851 1509531493084760490746777)
                ·
                  refine ⟨1132148619813570368060083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1509531493084760490746777 1132148619813570368060083)
                  ·
                    refine ⟨1698222929720355552090125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132148619813570368060083 1698222929720355552090125)
                    ·
                      refine ⟨636833598645133332033797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698222929720355552090125 636833598645133332033797)
                      ·
                        rfl

theorem cell23_1240229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_1240229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240229 prefixEnd_1240229 := by exact prefixLift 1240229
  have htrace : WordTrace (prefixWord ++ tailWord_1240229) baseStart_1240229 baseEnd_1240229 := by
    simpa [prefixWord, tailWord_1240229, baseEnd_1240229] using wordTrace_append hprefix tailTrace_1240229
  have hstable : (prefixWord ++ tailWord_1240229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240229).length < 2 ^ (prefixWord ++ tailWord_1240229).sum := by decide
  have hdescent : baseEnd_1240229 < baseStart_1240229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240248 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1240248 : Nat := 118140960795 + 1240248 * 2 ^ 59
def prefixEnd_1240248 : Nat := 4983230072969 + 3 ^ 40 * 1240248 * 2
def baseEnd_1240248 : Nat := 636843354777568757696209

theorem tailTrace_1240248 : CollatzResearch.WordTrace tailWord_1240248 prefixEnd_1240248 636843354777568757696209 := by
  unfold tailWord_1240248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22617780405400394169928699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30157040540533858893238265 22617780405400394169928699)
  ·
    refine ⟨33926670608100591254893049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22617780405400394169928699 33926670608100591254893049)
    ·
      refine ⟨25445002956075443441169787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33926670608100591254893049 25445002956075443441169787)
      ·
        refine ⟨38167504434113165161754681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25445002956075443441169787 38167504434113165161754681)
        ·
          refine ⟨28625628325584873871316011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38167504434113165161754681 28625628325584873871316011)
          ·
            refine ⟨42938442488377310806974017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28625628325584873871316011 42938442488377310806974017)
            ·
              refine ⟨32203831866282983105230513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42938442488377310806974017 32203831866282983105230513)
              ·
                refine ⟨24152873899712237328922885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32203831866282983105230513 24152873899712237328922885)
                ·
                  refine ⟨4528663856196044499173041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24152873899712237328922885 4528663856196044499173041)
                  ·
                    refine ⟨3396497892147033374379781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4528663856196044499173041 3396497892147033374379781)
                    ·
                      refine ⟨636843354777568757696209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3396497892147033374379781 636843354777568757696209)
                      ·
                        rfl

theorem cell23_1240248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1240248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240248 prefixEnd_1240248 := by exact prefixLift 1240248
  have htrace : WordTrace (prefixWord ++ tailWord_1240248) baseStart_1240248 baseEnd_1240248 := by
    simpa [prefixWord, tailWord_1240248, baseEnd_1240248] using wordTrace_append hprefix tailTrace_1240248
  have hstable : (prefixWord ++ tailWord_1240248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240248).length < 2 ^ (prefixWord ++ tailWord_1240248).sum := by decide
  have hdescent : baseEnd_1240248 < baseStart_1240248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240325 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_1240325 : Nat := 118140960795 + 1240325 * 2 ^ 59
def prefixEnd_1240325 : Nat := 4983230072969 + 3 ^ 40 * 1240325 * 2
def baseEnd_1240325 : Nat := 636882892787964956433355

theorem tailTrace_1240325 : CollatzResearch.WordTrace tailWord_1240325 prefixEnd_1240325 636882892787964956433355 := by
  unfold tailWord_1240325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45238369231521830490410429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30158912821014553660273619 45238369231521830490410429)
  ·
    refine ⟨16964388461820686433903911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45238369231521830490410429 16964388461820686433903911)
    ·
      refine ⟨25446582692731029650855867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16964388461820686433903911 25446582692731029650855867)
      ·
        refine ⟨38169874039096544476283801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25446582692731029650855867 38169874039096544476283801)
        ·
          refine ⟨28627405529322408357212851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38169874039096544476283801 28627405529322408357212851)
          ·
            refine ⟨42941108293983612535819277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28627405529322408357212851 42941108293983612535819277)
            ·
              refine ⟨16102915610243854700932229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42941108293983612535819277 16102915610243854700932229)
              ·
                refine ⟨3019296676920722756424793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16102915610243854700932229 3019296676920722756424793)
                ·
                  refine ⟨2264472507690542067318595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3019296676920722756424793 2264472507690542067318595)
                  ·
                    refine ⟨3396708761535813100977893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264472507690542067318595 3396708761535813100977893)
                    ·
                      refine ⟨636882892787964956433355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3396708761535813100977893 636882892787964956433355)
                      ·
                        rfl

theorem cell23_1240325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_1240325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240325 prefixEnd_1240325 := by exact prefixLift 1240325
  have htrace : WordTrace (prefixWord ++ tailWord_1240325) baseStart_1240325 baseEnd_1240325 := by
    simpa [prefixWord, tailWord_1240325, baseEnd_1240325] using wordTrace_append hprefix tailTrace_1240325
  have hstable : (prefixWord ++ tailWord_1240325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240325).length < 2 ^ (prefixWord ++ tailWord_1240325).sum := by decide
  have hdescent : baseEnd_1240325 < baseStart_1240325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240369 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 1, 4]
def baseStart_1240369 : Nat := 118140960795 + 1240369 * 2 ^ 59
def prefixEnd_1240369 : Nat := 4983230072969 + 3 ^ 40 * 1240369 * 2
def baseEnd_1240369 : Nat := 212301828645587594761051

theorem tailTrace_1240369 : CollatzResearch.WordTrace tailWord_1240369 prefixEnd_1240369 212301828645587594761051 := by
  unfold tailWord_1240369
  simp only [CollatzResearch.WordTrace]
  refine ⟨45239974043362426005012161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30159982695574950670008107 45239974043362426005012161)
  ·
    refine ⟨33929980532521819503759121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45239974043362426005012161 33929980532521819503759121)
    ·
      refine ⟨25447485399391364627819341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33929980532521819503759121 25447485399391364627819341)
      ·
        refine ⟨9542807024771761735432253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25447485399391364627819341 9542807024771761735432253)
        ·
          refine ⟨3578552634289410650787095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9542807024771761735432253 3578552634289410650787095)
          ·
            refine ⟨5367828951434115976180643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578552634289410650787095 5367828951434115976180643)
            ·
              refine ⟨8051743427151173964270965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5367828951434115976180643 8051743427151173964270965)
              ·
                refine ⟨754850946295422559150403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8051743427151173964270965 754850946295422559150403)
                ·
                  refine ⟨1132276419443133838725605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754850946295422559150403 1132276419443133838725605)
                  ·
                    refine ⟨212301828645587594761051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132276419443133838725605 212301828645587594761051)
                    ·
                      rfl

theorem cell23_1240369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_1240369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240369 prefixEnd_1240369 := by exact prefixLift 1240369
  have htrace : WordTrace (prefixWord ++ tailWord_1240369) baseStart_1240369 baseEnd_1240369 := by
    simpa [prefixWord, tailWord_1240369, baseEnd_1240369] using wordTrace_append hprefix tailTrace_1240369
  have hstable : (prefixWord ++ tailWord_1240369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240369).length < 2 ^ (prefixWord ++ tailWord_1240369).sum := by decide
  have hdescent : baseEnd_1240369 < baseStart_1240369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240432 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_1240432 : Nat := 118140960795 + 1240432 * 2 ^ 59
def prefixEnd_1240432 : Nat := 4983230072969 + 3 ^ 40 * 1240432 * 2
def baseEnd_1240432 : Nat := 636937835217996037795363

theorem tailTrace_1240432 : CollatzResearch.WordTrace tailWord_1240432 prefixEnd_1240432 636937835217996037795363 := by
  unfold tailWord_1240432
  simp only [CollatzResearch.WordTrace]
  refine ⟨22621135921067093882277775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30161514561422791843037033 22621135921067093882277775)
  ·
    refine ⟨33931703881600640823416663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22621135921067093882277775 33931703881600640823416663)
    ·
      refine ⟨50897555822400961235124995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33931703881600640823416663 50897555822400961235124995)
      ·
        refine ⟨76346333733601441852687493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50897555822400961235124995 76346333733601441852687493)
        ·
          refine ⟨14314937575050270347378905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76346333733601441852687493 14314937575050270347378905)
          ·
            refine ⟨10736203181287702760534179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14314937575050270347378905 10736203181287702760534179)
            ·
              refine ⟨16104304771931554140801269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10736203181287702760534179 16104304771931554140801269)
              ·
                refine ⟨1509778572368583200700119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16104304771931554140801269 1509778572368583200700119)
                ·
                  refine ⟨2264667858552874801050179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509778572368583200700119 2264667858552874801050179)
                  ·
                    refine ⟨3397001787829312201575269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264667858552874801050179 3397001787829312201575269)
                    ·
                      refine ⟨636937835217996037795363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3397001787829312201575269 636937835217996037795363)
                      ·
                        rfl

theorem cell23_1240432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_1240432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240432 prefixEnd_1240432 := by exact prefixLift 1240432
  have htrace : WordTrace (prefixWord ++ tailWord_1240432) baseStart_1240432 baseEnd_1240432 := by
    simpa [prefixWord, tailWord_1240432, baseEnd_1240432] using wordTrace_append hprefix tailTrace_1240432
  have hstable : (prefixWord ++ tailWord_1240432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240432).length < 2 ^ (prefixWord ++ tailWord_1240432).sum := by decide
  have hdescent : baseEnd_1240432 < baseStart_1240432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240445 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1240445 : Nat := 118140960795 + 1240445 * 2 ^ 59
def prefixEnd_1240445 : Nat := 4983230072969 + 3 ^ 40 * 1240445 * 2
def baseEnd_1240445 : Nat := 636944510466504486932803

theorem tailTrace_1240445 : CollatzResearch.WordTrace tailWord_1240445 prefixEnd_1240445 636944510466504486932803 := by
  unfold tailWord_1240445
  simp only [CollatzResearch.WordTrace]
  refine ⟨45242745991087090984778789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30161830660724727323185859 45242745991087090984778789)
  ·
    refine ⟨8483014873328829559646023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45242745991087090984778789 8483014873328829559646023)
    ·
      refine ⟨12724522309993244339469035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8483014873328829559646023 12724522309993244339469035)
      ·
        refine ⟨19086783464989866509203553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12724522309993244339469035 19086783464989866509203553)
        ·
          refine ⟨14315087598742399881902665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19086783464989866509203553 14315087598742399881902665)
          ·
            refine ⟨10736315699056799911426999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14315087598742399881902665 10736315699056799911426999)
            ·
              refine ⟨16104473548585199867140499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10736315699056799911426999 16104473548585199867140499)
              ·
                refine ⟨24156710322877799800710749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16104473548585199867140499 24156710322877799800710749)
                ·
                  refine ⟨9058766371079174925266531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24156710322877799800710749 9058766371079174925266531)
                  ·
                    refine ⟨13588149556618762387899797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9058766371079174925266531 13588149556618762387899797)
                    ·
                      refine ⟨636944510466504486932803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13588149556618762387899797 636944510466504486932803)
                      ·
                        rfl

theorem cell23_1240445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1240445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240445 prefixEnd_1240445 := by exact prefixLift 1240445
  have htrace : WordTrace (prefixWord ++ tailWord_1240445) baseStart_1240445 baseEnd_1240445 := by
    simpa [prefixWord, tailWord_1240445, baseEnd_1240445] using wordTrace_append hprefix tailTrace_1240445
  have hstable : (prefixWord ++ tailWord_1240445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240445).length < 2 ^ (prefixWord ++ tailWord_1240445).sum := by decide
  have hdescent : baseEnd_1240445 < baseStart_1240445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240452 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1240452 : Nat := 118140960795 + 1240452 * 2 ^ 59
def prefixEnd_1240452 : Nat := 4983230072969 + 3 ^ 40 * 1240452 * 2
def baseEnd_1240452 : Nat := 636948104831085959545271

theorem tailTrace_1240452 : CollatzResearch.WordTrace tailWord_1240452 prefixEnd_1240452 636948104831085959545271 := by
  unfold tailWord_1240452
  simp only [CollatzResearch.WordTrace]
  refine ⟨22621500651030865590141805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30162000868041154120189073 22621500651030865590141805)
  ·
    refine ⟨8483062744136574596303177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22621500651030865590141805 8483062744136574596303177)
    ·
      refine ⟨6362297058102430947227383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8483062744136574596303177 6362297058102430947227383)
      ·
        refine ⟨9543445587153646420841075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6362297058102430947227383 9543445587153646420841075)
        ·
          refine ⟨14315168380730469631261613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9543445587153646420841075 14315168380730469631261613)
          ·
            refine ⟨5368188142773926111723105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14315168380730469631261613 5368188142773926111723105)
            ·
              refine ⟨4026141107080444583792329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5368188142773926111723105 4026141107080444583792329)
              ·
                refine ⟨3019605830310333437844247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026141107080444583792329 3019605830310333437844247)
                ·
                  refine ⟨4529408745465500156766371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019605830310333437844247 4529408745465500156766371)
                  ·
                    refine ⟨6794113118198250235149557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4529408745465500156766371 6794113118198250235149557)
                    ·
                      refine ⟨636948104831085959545271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6794113118198250235149557 636948104831085959545271)
                      ·
                        rfl

theorem cell23_1240452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1240452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240452 prefixEnd_1240452 := by exact prefixLift 1240452
  have htrace : WordTrace (prefixWord ++ tailWord_1240452) baseStart_1240452 baseEnd_1240452 := by
    simpa [prefixWord, tailWord_1240452, baseEnd_1240452] using wordTrace_append hprefix tailTrace_1240452
  have hstable : (prefixWord ++ tailWord_1240452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240452).length < 2 ^ (prefixWord ++ tailWord_1240452).sum := by decide
  have hdescent : baseEnd_1240452 < baseStart_1240452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240455 : List Nat := [1, 1, 4, 2, 2, 2, 1, 10]
def baseStart_1240455 : Nat := 118140960795 + 1240455 * 2 ^ 59
def prefixEnd_1240455 : Nat := 4983230072969 + 3 ^ 40 * 1240455 * 2
def baseEnd_1240455 : Nat := 23590727602705535103991

theorem tailTrace_1240455 : CollatzResearch.WordTrace tailWord_1240455 prefixEnd_1240455 23590727602705535103991 := by
  unfold tailWord_1240455
  simp only [CollatzResearch.WordTrace]
  refine ⟨45243110721050862692642819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30162073814033908461761879 45243110721050862692642819)
  ·
    refine ⟨67864666081576294038964229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45243110721050862692642819 67864666081576294038964229)
    ·
      refine ⟨12724624890295555132305793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67864666081576294038964229 12724624890295555132305793)
      ·
        refine ⟨9543468667721666349229345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12724624890295555132305793 9543468667721666349229345)
        ·
          refine ⟨7157601500791249761922009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9543468667721666349229345 7157601500791249761922009)
          ·
            refine ⟨5368201125593437321441507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7157601500791249761922009 5368201125593437321441507)
            ·
              refine ⟨8052301688390155982162261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368201125593437321441507 8052301688390155982162261)
              ·
                refine ⟨23590727602705535103991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8052301688390155982162261 23590727602705535103991)
                ·
                  rfl

theorem cell23_1240455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 10].length) (baseStart_1240455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240455 prefixEnd_1240455 := by exact prefixLift 1240455
  have htrace : WordTrace (prefixWord ++ tailWord_1240455) baseStart_1240455 baseEnd_1240455 := by
    simpa [prefixWord, tailWord_1240455, baseEnd_1240455] using wordTrace_append hprefix tailTrace_1240455
  have hstable : (prefixWord ++ tailWord_1240455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240455).length < 2 ^ (prefixWord ++ tailWord_1240455).sum := by decide
  have hdescent : baseEnd_1240455 < baseStart_1240455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240466 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1240466 : Nat := 118140960795 + 1240466 * 2 ^ 59
def prefixEnd_1240466 : Nat := 4983230072969 + 3 ^ 40 * 1240466 * 2
def baseEnd_1240466 : Nat := 636955293560248904770207

theorem tailTrace_1240466 : CollatzResearch.WordTrace tailWord_1240466 prefixEnd_1240466 636955293560248904770207 := by
  unfold tailWord_1240466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11310877981002752892823313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30162341282674007714195501 11310877981002752892823313)
  ·
    refine ⟨8483158485752064669617485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11310877981002752892823313 8483158485752064669617485)
    ·
      refine ⟨3181184432157024251106557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8483158485752064669617485 3181184432157024251106557)
      ·
        refine ⟨1192944162058884094164959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3181184432157024251106557 1192944162058884094164959)
        ·
          refine ⟨1789416243088326141247439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192944162058884094164959 1789416243088326141247439)
          ·
            refine ⟨2684124364632489211871159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789416243088326141247439 2684124364632489211871159)
            ·
              refine ⟨4026186546948733817806739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684124364632489211871159 4026186546948733817806739)
              ·
                refine ⟨6039279820423100726710109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026186546948733817806739 6039279820423100726710109)
                ·
                  refine ⟨2264729932658662772516291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6039279820423100726710109 2264729932658662772516291)
                  ·
                    refine ⟨3397094898987994158774437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2264729932658662772516291 3397094898987994158774437)
                    ·
                      refine ⟨636955293560248904770207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3397094898987994158774437 636955293560248904770207)
                      ·
                        rfl

theorem cell23_1240466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1240466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240466 prefixEnd_1240466 := by exact prefixLift 1240466
  have htrace : WordTrace (prefixWord ++ tailWord_1240466) baseStart_1240466 baseEnd_1240466 := by
    simpa [prefixWord, tailWord_1240466, baseEnd_1240466] using wordTrace_append hprefix tailTrace_1240466
  have hstable : (prefixWord ++ tailWord_1240466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240466).length < 2 ^ (prefixWord ++ tailWord_1240466).sum := by decide
  have hdescent : baseEnd_1240466 < baseStart_1240466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240469 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_1240469 : Nat := 118140960795 + 1240469 * 2 ^ 59
def prefixEnd_1240469 : Nat := 4983230072969 + 3 ^ 40 * 1240469 * 2
def baseEnd_1240469 : Nat := 636956834002212393032693

theorem tailTrace_1240469 : CollatzResearch.WordTrace tailWord_1240469 prefixEnd_1240469 636956834002212393032693 := by
  unfold tailWord_1240469
  simp only [CollatzResearch.WordTrace]
  refine ⟨45243621343000143083652461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30162414228666762055768307 45243621343000143083652461)
  ·
    refine ⟨16966358003625053656369673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45243621343000143083652461 16966358003625053656369673)
    ·
      refine ⟨12724768502718790242277255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16966358003625053656369673 12724768502718790242277255)
      ·
        refine ⟨19087152754078185363415883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12724768502718790242277255 19087152754078185363415883)
        ·
          refine ⟨28630729131117278045123825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19087152754078185363415883 28630729131117278045123825)
          ·
            refine ⟨21473046848337958533842869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28630729131117278045123825 21473046848337958533842869)
            ·
              refine ⟨2013098142031683612547769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21473046848337958533842869 2013098142031683612547769)
              ·
                refine ⟨1509823606523762709410827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013098142031683612547769 1509823606523762709410827)
                ·
                  refine ⟨2264735409785644064116241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1509823606523762709410827 2264735409785644064116241)
                  ·
                    refine ⟨1698551557339233048087181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2264735409785644064116241 1698551557339233048087181)
                    ·
                      refine ⟨636956834002212393032693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698551557339233048087181 636956834002212393032693)
                      ·
                        rfl

theorem cell23_1240469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_1240469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240469 prefixEnd_1240469 := by exact prefixLift 1240469
  have htrace : WordTrace (prefixWord ++ tailWord_1240469) baseStart_1240469 baseEnd_1240469 := by
    simpa [prefixWord, tailWord_1240469, baseEnd_1240469] using wordTrace_append hprefix tailTrace_1240469
  have hstable : (prefixWord ++ tailWord_1240469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240469).length < 2 ^ (prefixWord ++ tailWord_1240469).sum := by decide
  have hdescent : baseEnd_1240469 < baseStart_1240469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240495 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_1240495 : Nat := 118140960795 + 1240495 * 2 ^ 59
def prefixEnd_1240495 : Nat := 4983230072969 + 3 ^ 40 * 1240495 * 2
def baseEnd_1240495 : Nat := 636970184499229291307573

theorem tailTrace_1240495 : CollatzResearch.WordTrace tailWord_1240495 prefixEnd_1240495 636970184499229291307573 := by
  unfold tailWord_1240495
  simp only [CollatzResearch.WordTrace]
  refine ⟨45244569640905949524098939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30163046427270633016065959 45244569640905949524098939)
  ·
    refine ⟨67866854461358924286148409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45244569640905949524098939 67866854461358924286148409)
    ·
      refine ⟨50900140846019193214611307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67866854461358924286148409 50900140846019193214611307)
      ·
        refine ⟨76350211269028789821916961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50900140846019193214611307 76350211269028789821916961)
        ·
          refine ⟨57262658451771592366437721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76350211269028789821916961 57262658451771592366437721)
          ·
            refine ⟨42946993838828694274828291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57262658451771592366437721 42946993838828694274828291)
            ·
              refine ⟨64420490758243041412242437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42946993838828694274828291 64420490758243041412242437)
              ·
                refine ⟨12078842017170570264795457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64420490758243041412242437 12078842017170570264795457)
                ·
                  refine ⟨9059131512877927698596593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12078842017170570264795457 9059131512877927698596593)
                  ·
                    refine ⟨6794348634658445773947445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9059131512877927698596593 6794348634658445773947445)
                    ·
                      refine ⟨636970184499229291307573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6794348634658445773947445 636970184499229291307573)
                      ·
                        rfl

theorem cell23_1240495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_1240495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240495 prefixEnd_1240495 := by exact prefixLift 1240495
  have htrace : WordTrace (prefixWord ++ tailWord_1240495) baseStart_1240495 baseEnd_1240495 := by
    simpa [prefixWord, tailWord_1240495, baseEnd_1240495] using wordTrace_append hprefix tailTrace_1240495
  have hstable : (prefixWord ++ tailWord_1240495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240495).length < 2 ^ (prefixWord ++ tailWord_1240495).sum := by decide
  have hdescent : baseEnd_1240495 < baseStart_1240495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240509 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_1240509 : Nat := 118140960795 + 1240509 * 2 ^ 59
def prefixEnd_1240509 : Nat := 4983230072969 + 3 ^ 40 * 1240509 * 2
def baseEnd_1240509 : Nat := 636977373228392236532509

theorem tailTrace_1240509 : CollatzResearch.WordTrace tailWord_1240509 prefixEnd_1240509 636977373228392236532509 := by
  unfold tailWord_1240509
  simp only [CollatzResearch.WordTrace]
  refine ⟨45245080262855229915108581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30163386841903486610072387 45245080262855229915108581)
  ·
    refine ⟨8483452549285355609082859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45245080262855229915108581 8483452549285355609082859)
    ·
      refine ⟨12725178823928033413624289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8483452549285355609082859 12725178823928033413624289)
      ·
        refine ⟨9543884117946025060218217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12725178823928033413624289 9543884117946025060218217)
        ·
          refine ⟨7157913088459518795163663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9543884117946025060218217 7157913088459518795163663)
          ·
            refine ⟨10736869632689278192745495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157913088459518795163663 10736869632689278192745495)
            ·
              refine ⟨16105304449033917289118243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10736869632689278192745495 16105304449033917289118243)
              ·
                refine ⟨24157956673550875933677365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16105304449033917289118243 24157956673550875933677365)
                ·
                  refine ⟨2264808438145394618782253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24157956673550875933677365 2264808438145394618782253)
                  ·
                    refine ⟨849303164304522982043345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2264808438145394618782253 849303164304522982043345)
                    ·
                      refine ⟨636977373228392236532509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849303164304522982043345 636977373228392236532509)
                      ·
                        rfl

theorem cell23_1240509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_1240509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240509 prefixEnd_1240509 := by exact prefixLift 1240509
  have htrace : WordTrace (prefixWord ++ tailWord_1240509) baseStart_1240509 baseEnd_1240509 := by
    simpa [prefixWord, tailWord_1240509, baseEnd_1240509] using wordTrace_append hprefix tailTrace_1240509
  have hstable : (prefixWord ++ tailWord_1240509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240509).length < 2 ^ (prefixWord ++ tailWord_1240509).sum := by decide
  have hdescent : baseEnd_1240509 < baseStart_1240509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240515 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 8]
def baseStart_1240515 : Nat := 118140960795 + 1240515 * 2 ^ 59
def prefixEnd_1240515 : Nat := 4983230072969 + 3 ^ 40 * 1240515 * 2
def baseEnd_1240515 : Nat := 212326818037439737685827

theorem tailTrace_1240515 : CollatzResearch.WordTrace tailWord_1240515 prefixEnd_1240515 212326818037439737685827 := by
  unfold tailWord_1240515
  simp only [CollatzResearch.WordTrace]
  refine ⟨45245299100833492939826999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30163532733888995293217999 45245299100833492939826999)
  ·
    refine ⟨67867948651250239409740499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45245299100833492939826999 67867948651250239409740499)
    ·
      refine ⟨101801922976875359114610749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67867948651250239409740499 101801922976875359114610749)
      ·
        refine ⟨38175721116328259667979031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101801922976875359114610749 38175721116328259667979031)
        ·
          refine ⟨57263581674492389501968547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38175721116328259667979031 57263581674492389501968547)
          ·
            refine ⟨85895372511738584252952821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57263581674492389501968547 85895372511738584252952821)
            ·
              refine ⟨8052691172975492273714327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85895372511738584252952821 8052691172975492273714327)
              ·
                refine ⟨12079036759463238410571491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052691172975492273714327 12079036759463238410571491)
                ·
                  refine ⟨18118555139194857615857237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079036759463238410571491 18118555139194857615857237)
                  ·
                    refine ⟨212326818037439737685827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18118555139194857615857237 212326818037439737685827)
                    ·
                      rfl

theorem cell23_1240515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_1240515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240515 prefixEnd_1240515 := by exact prefixLift 1240515
  have htrace : WordTrace (prefixWord ++ tailWord_1240515) baseStart_1240515 baseEnd_1240515 := by
    simpa [prefixWord, tailWord_1240515, baseEnd_1240515] using wordTrace_append hprefix tailTrace_1240515
  have hstable : (prefixWord ++ tailWord_1240515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240515).length < 2 ^ (prefixWord ++ tailWord_1240515).sum := by decide
  have hdescent : baseEnd_1240515 < baseStart_1240515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240516 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1240516 : Nat := 118140960795 + 1240516 * 2 ^ 59
def prefixEnd_1240516 : Nat := 4983230072969 + 3 ^ 40 * 1240516 * 2
def baseEnd_1240516 : Nat := 636980967592973709144977

theorem tailTrace_1240516 : CollatzResearch.WordTrace tailWord_1240516 prefixEnd_1240516 636980967592973709144977 := by
  unfold tailWord_1240516
  simp only [CollatzResearch.WordTrace]
  refine ⟨22622667786914935055306701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30163557049219913407075601 22622667786914935055306701)
  ·
    refine ⟨8483500420093100645740013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22622667786914935055306701 8483500420093100645740013)
    ·
      refine ⟨3181312657534912742152505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8483500420093100645740013 3181312657534912742152505)
      ·
        refine ⟨2385984493151184556614379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181312657534912742152505 2385984493151184556614379)
        ·
          refine ⟨3578976739726776834921569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385984493151184556614379 3578976739726776834921569)
          ·
            refine ⟨2684232554795082626191177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578976739726776834921569 2684232554795082626191177)
            ·
              refine ⟨2013174416096311969643383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684232554795082626191177 2013174416096311969643383)
              ·
                refine ⟨3019761624144467954465075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013174416096311969643383 3019761624144467954465075)
                ·
                  refine ⟨4529642436216701931697613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019761624144467954465075 4529642436216701931697613)
                  ·
                    refine ⟨1698615913581263224386605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4529642436216701931697613 1698615913581263224386605)
                    ·
                      refine ⟨636980967592973709144977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698615913581263224386605 636980967592973709144977)
                      ·
                        rfl

theorem cell23_1240516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1240516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240516 prefixEnd_1240516 := by exact prefixLift 1240516
  have htrace : WordTrace (prefixWord ++ tailWord_1240516) baseStart_1240516 baseEnd_1240516 := by
    simpa [prefixWord, tailWord_1240516, baseEnd_1240516] using wordTrace_append hprefix tailTrace_1240516
  have hstable : (prefixWord ++ tailWord_1240516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240516).length < 2 ^ (prefixWord ++ tailWord_1240516).sum := by decide
  have hdescent : baseEnd_1240516 < baseStart_1240516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 10, 2, 2]
def baseStart_1240539 : Nat := 118140960795 + 1240539 * 2 ^ 59
def prefixEnd_1240539 : Nat := 4983230072969 + 3 ^ 40 * 1240539 * 2
def baseEnd_1240539 : Nat := 636992777648027119157371

theorem tailTrace_1240539 : CollatzResearch.WordTrace tailWord_1240539 prefixEnd_1240539 636992777648027119157371 := by
  unfold tailWord_1240539
  simp only [CollatzResearch.WordTrace]
  refine ⟨45246174452746545038700671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30164116301831030025800447 45246174452746545038700671)
  ·
    refine ⟨67869261679119817558051007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45246174452746545038700671 67869261679119817558051007)
    ·
      refine ⟨101803892518679726337076511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67869261679119817558051007 101803892518679726337076511)
      ·
        refine ⟨152705838778019589505614767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101803892518679726337076511 152705838778019589505614767)
        ·
          refine ⟨229058758167029384258422151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152705838778019589505614767 229058758167029384258422151)
          ·
            refine ⟨343588137250544076387633227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229058758167029384258422151 343588137250544076387633227)
            ·
              refine ⟨515382205875816114581449841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343588137250544076387633227 515382205875816114581449841)
              ·
                refine ⟨386536654406862085936087381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515382205875816114581449841 386536654406862085936087381)
                ·
                  refine ⟨1132431604707603767390881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 386536654406862085936087381 1132431604707603767390881)
                  ·
                    refine ⟨849323703530702825543161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132431604707603767390881 849323703530702825543161)
                    ·
                      refine ⟨636992777648027119157371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849323703530702825543161 636992777648027119157371)
                      ·
                        rfl

theorem cell23_1240539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 2, 2].length) (baseStart_1240539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240539 prefixEnd_1240539 := by exact prefixLift 1240539
  have htrace : WordTrace (prefixWord ++ tailWord_1240539) baseStart_1240539 baseEnd_1240539 := by
    simpa [prefixWord, tailWord_1240539, baseEnd_1240539] using wordTrace_append hprefix tailTrace_1240539
  have hstable : (prefixWord ++ tailWord_1240539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240539).length < 2 ^ (prefixWord ++ tailWord_1240539).sum := by decide
  have hdescent : baseEnd_1240539 < baseStart_1240539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240552 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1240552 : Nat := 118140960795 + 1240552 * 2 ^ 59
def prefixEnd_1240552 : Nat := 4983230072969 + 3 ^ 40 * 1240552 * 2
def baseEnd_1240552 : Nat := 636999452896535568294811

theorem tailTrace_1240552 : CollatzResearch.WordTrace tailWord_1240552 prefixEnd_1240552 636999452896535568294811 := by
  unfold tailWord_1240552
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623324300849724129461955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30164432401132965505949273 22623324300849724129461955)
  ·
    refine ⟨33934986451274586194192933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22623324300849724129461955 33934986451274586194192933)
    ·
      refine ⟨6362809959613984911411175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33934986451274586194192933 6362809959613984911411175)
      ·
        refine ⟨9544214939420977367116763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6362809959613984911411175 9544214939420977367116763)
        ·
          refine ⟨14316322409131466050675145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9544214939420977367116763 14316322409131466050675145)
          ·
            refine ⟨10737241806848599538006359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14316322409131466050675145 10737241806848599538006359)
            ·
              refine ⟨16105862710272899307009539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10737241806848599538006359 16105862710272899307009539)
              ·
                refine ⟨24158794065409348960514309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16105862710272899307009539 24158794065409348960514309)
                ·
                  refine ⟨4529773887264252930096433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24158794065409348960514309 4529773887264252930096433)
                  ·
                    refine ⟨3397330415448189697572325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4529773887264252930096433 3397330415448189697572325)
                    ·
                      refine ⟨636999452896535568294811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3397330415448189697572325 636999452896535568294811)
                      ·
                        rfl

theorem cell23_1240552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1240552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240552 prefixEnd_1240552 := by exact prefixLift 1240552
  have htrace : WordTrace (prefixWord ++ tailWord_1240552) baseStart_1240552 baseEnd_1240552 := by
    simpa [prefixWord, tailWord_1240552, baseEnd_1240552] using wordTrace_append hprefix tailTrace_1240552
  have hstable : (prefixWord ++ tailWord_1240552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240552).length < 2 ^ (prefixWord ++ tailWord_1240552).sum := by decide
  have hdescent : baseEnd_1240552 < baseStart_1240552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240555 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_1240555 : Nat := 118140960795 + 1240555 * 2 ^ 59
def prefixEnd_1240555 : Nat := 4983230072969 + 3 ^ 40 * 1240555 * 2
def baseEnd_1240555 : Nat := 637000993338499056557297

theorem tailTrace_1240555 : CollatzResearch.WordTrace tailWord_1240555 prefixEnd_1240555 637000993338499056557297 := by
  unfold tailWord_1240555
  simp only [CollatzResearch.WordTrace]
  refine ⟨45246758020688579771283119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30164505347125719847522079 45246758020688579771283119)
  ·
    refine ⟨67870137031032869656924679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45246758020688579771283119 67870137031032869656924679)
    ·
      refine ⟨101805205546549304485387019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67870137031032869656924679 101805205546549304485387019)
      ·
        refine ⟨152707808319823956728080529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101805205546549304485387019 152707808319823956728080529)
        ·
          refine ⟨114530856239867967546060397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152707808319823956728080529 114530856239867967546060397)
          ·
            refine ⟨42949071089950487829772649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114530856239867967546060397 42949071089950487829772649)
            ·
              refine ⟨32211803317462865872329487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42949071089950487829772649 32211803317462865872329487)
              ·
                refine ⟨48317704976194298808494231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32211803317462865872329487 48317704976194298808494231)
                ·
                  refine ⟨72476557464291448212741347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48317704976194298808494231 72476557464291448212741347)
                  ·
                    refine ⟨108714836196437172319112021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72476557464291448212741347 108714836196437172319112021)
                    ·
                      refine ⟨637000993338499056557297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 108714836196437172319112021 637000993338499056557297)
                      ·
                        rfl

theorem cell23_1240555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_1240555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240555 prefixEnd_1240555 := by exact prefixLift 1240555
  have htrace : WordTrace (prefixWord ++ tailWord_1240555) baseStart_1240555 baseEnd_1240555 := by
    simpa [prefixWord, tailWord_1240555, baseEnd_1240555] using wordTrace_append hprefix tailTrace_1240555
  have hstable : (prefixWord ++ tailWord_1240555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240555).length < 2 ^ (prefixWord ++ tailWord_1240555).sum := by decide
  have hdescent : baseEnd_1240555 < baseStart_1240555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240556 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_1240556 : Nat := 118140960795 + 1240556 * 2 ^ 59
def prefixEnd_1240556 : Nat := 4983230072969 + 3 ^ 40 * 1240556 * 2
def baseEnd_1240556 : Nat := 637001506819153552644793

theorem tailTrace_1240556 : CollatzResearch.WordTrace tailWord_1240556 prefixEnd_1240556 637001506819153552644793 := by
  unfold tailWord_1240556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623397246842478471034761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30164529662456637961379681 22623397246842478471034761)
  ·
    refine ⟨16967547935131858853276071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22623397246842478471034761 16967547935131858853276071)
    ·
      refine ⟨25451321902697788279914107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16967547935131858853276071 25451321902697788279914107)
      ·
        refine ⟨38176982854046682419871161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25451321902697788279914107 38176982854046682419871161)
        ·
          refine ⟨28632737140535011814903371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38176982854046682419871161 28632737140535011814903371)
          ·
            refine ⟨42949105710802517722355057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28632737140535011814903371 42949105710802517722355057)
            ·
              refine ⟨32211829283101888291766293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42949105710802517722355057 32211829283101888291766293)
              ·
                refine ⟨1509929497645401013676545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32211829283101888291766293 1509929497645401013676545)
                ·
                  refine ⟨1132447123234050760257409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1509929497645401013676545 1132447123234050760257409)
                  ·
                    refine ⟨849335342425538070193057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132447123234050760257409 849335342425538070193057)
                    ·
                      refine ⟨637001506819153552644793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849335342425538070193057 637001506819153552644793)
                      ·
                        rfl

theorem cell23_1240556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_1240556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240556 prefixEnd_1240556 := by exact prefixLift 1240556
  have htrace : WordTrace (prefixWord ++ tailWord_1240556) baseStart_1240556 baseEnd_1240556 := by
    simpa [prefixWord, tailWord_1240556, baseEnd_1240556] using wordTrace_append hprefix tailTrace_1240556
  have hstable : (prefixWord ++ tailWord_1240556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240556).length < 2 ^ (prefixWord ++ tailWord_1240556).sum := by decide
  have hdescent : baseEnd_1240556 < baseStart_1240556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240602 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1240602 : Nat := 118140960795 + 1240602 * 2 ^ 59
def prefixEnd_1240602 : Nat := 4983230072969 + 3 ^ 40 * 1240602 * 2
def baseEnd_1240602 : Nat := 637025126929260372669581

theorem tailTrace_1240602 : CollatzResearch.WordTrace tailWord_1240602 prefixEnd_1240602 637025126929260372669581 := by
  unfold tailWord_1240602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312118062879576699561015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30165648167678871198829373 11312118062879576699561015)
  ·
    refine ⟨16968177094319365049341523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11312118062879576699561015 16968177094319365049341523)
    ·
      refine ⟨25452265641479047574012285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16968177094319365049341523 25452265641479047574012285)
      ·
        refine ⟨9544599615554642840254607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25452265641479047574012285 9544599615554642840254607)
        ·
          refine ⟨14316899423331964260381911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9544599615554642840254607 14316899423331964260381911)
          ·
            refine ⟨21475349134997946390572867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14316899423331964260381911 21475349134997946390572867)
            ·
              refine ⟨32213023702496919585859301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21475349134997946390572867 32213023702496919585859301)
              ·
                refine ⟨6039941944218172422348619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32213023702496919585859301 6039941944218172422348619)
                ·
                  refine ⟨9059912916327258633522929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039941944218172422348619 9059912916327258633522929)
                  ·
                    refine ⟨6794934687245443975142197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9059912916327258633522929 6794934687245443975142197)
                    ·
                      refine ⟨637025126929260372669581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6794934687245443975142197 637025126929260372669581)
                      ·
                        rfl

theorem cell23_1240602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1240602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240602 prefixEnd_1240602 := by exact prefixLift 1240602
  have htrace : WordTrace (prefixWord ++ tailWord_1240602) baseStart_1240602 baseEnd_1240602 := by
    simpa [prefixWord, tailWord_1240602, baseEnd_1240602] using wordTrace_append hprefix tailTrace_1240602
  have hstable : (prefixWord ++ tailWord_1240602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240602).length < 2 ^ (prefixWord ++ tailWord_1240602).sum := by decide
  have hdescent : baseEnd_1240602 < baseStart_1240602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240609 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1240609 : Nat := 118140960795 + 1240609 * 2 ^ 59
def prefixEnd_1240609 : Nat := 4983230072969 + 3 ^ 40 * 1240609 * 2
def baseEnd_1240609 : Nat := 212342907097947281760683

theorem tailTrace_1240609 : CollatzResearch.WordTrace tailWord_1240609 prefixEnd_1240609 212342907097947281760683 := by
  unfold tailWord_1240609
  simp only [CollatzResearch.WordTrace]
  refine ⟨45248727562492946993748881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30165818374995297995832587 45248727562492946993748881)
  ·
    refine ⟨33936545671869710245311661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45248727562492946993748881 33936545671869710245311661)
    ·
      refine ⟨12726204626951141341991873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33936545671869710245311661 12726204626951141341991873)
      ·
        refine ⟨9544653470213356006493905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12726204626951141341991873 9544653470213356006493905)
        ·
          refine ⟨7158490102660017004870429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9544653470213356006493905 7158490102660017004870429)
          ·
            refine ⟨2684433788497506376826411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7158490102660017004870429 2684433788497506376826411)
            ·
              refine ⟨4026650682746259565239617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684433788497506376826411 4026650682746259565239617)
              ·
                refine ⟨3019988012059694673929713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026650682746259565239617 3019988012059694673929713)
                ·
                  refine ⟨2264991009044771005447285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3019988012059694673929713 2264991009044771005447285)
                  ·
                    refine ⟨212342907097947281760683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2264991009044771005447285 212342907097947281760683)
                    ·
                      rfl

theorem cell23_1240609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1240609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240609 prefixEnd_1240609 := by exact prefixLift 1240609
  have htrace : WordTrace (prefixWord ++ tailWord_1240609) baseStart_1240609 baseEnd_1240609 := by
    simpa [prefixWord, tailWord_1240609, baseEnd_1240609] using wordTrace_append hprefix tailTrace_1240609
  have hstable : (prefixWord ++ tailWord_1240609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240609).length < 2 ^ (prefixWord ++ tailWord_1240609).sum := by decide
  have hdescent : baseEnd_1240609 < baseStart_1240609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240656 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 1, 4]
def baseStart_1240656 : Nat := 118140960795 + 1240656 * 2 ^ 59
def prefixEnd_1240656 : Nat := 4983230072969 + 3 ^ 40 * 1240656 * 2
def baseEnd_1240656 : Nat := 212350951628201053798111

theorem tailTrace_1240656 : CollatzResearch.WordTrace tailWord_1240656 prefixEnd_1240656 212350951628201053798111 := by
  unfold tailWord_1240656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22625220896661337010354911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30166961195548449347139881 22625220896661337010354911)
  ·
    refine ⟨33937831344992005515532367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22625220896661337010354911 33937831344992005515532367)
    ·
      refine ⟨50906747017488008273298551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33937831344992005515532367 50906747017488008273298551)
      ·
        refine ⟨76360120526232012409947827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50906747017488008273298551 76360120526232012409947827)
        ·
          refine ⟨114540180789348018614921741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76360120526232012409947827 114540180789348018614921741)
          ·
            refine ⟨42952567796005506980595653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114540180789348018614921741 42952567796005506980595653)
            ·
              refine ⟨8053606461751032558861685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42952567796005506980595653 8053606461751032558861685)
              ·
                refine ⟨755025605789159302393283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8053606461751032558861685 755025605789159302393283)
                ·
                  refine ⟨1132538408683738953589925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755025605789159302393283 1132538408683738953589925)
                  ·
                    refine ⟨212350951628201053798111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132538408683738953589925 212350951628201053798111)
                    ·
                      rfl

theorem cell23_1240656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 1, 4].length) (baseStart_1240656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240656 prefixEnd_1240656 := by exact prefixLift 1240656
  have htrace : WordTrace (prefixWord ++ tailWord_1240656) baseStart_1240656 baseEnd_1240656 := by
    simpa [prefixWord, tailWord_1240656, baseEnd_1240656] using wordTrace_append hprefix tailTrace_1240656
  have hstable : (prefixWord ++ tailWord_1240656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240656).length < 2 ^ (prefixWord ++ tailWord_1240656).sum := by decide
  have hdescent : baseEnd_1240656 < baseStart_1240656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240672 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1240672 : Nat := 118140960795 + 1240672 * 2 ^ 59
def prefixEnd_1240672 : Nat := 4983230072969 + 3 ^ 40 * 1240672 * 2
def baseEnd_1240672 : Nat := 637061070575075098794259

theorem tailTrace_1240672 : CollatzResearch.WordTrace tailWord_1240672 prefixEnd_1240672 637061070575075098794259 := by
  unfold tailWord_1240672
  simp only [CollatzResearch.WordTrace]
  refine ⟨22625512680632354376646135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30167350240843139168861513 22625512680632354376646135)
  ·
    refine ⟨33938269020948531564969203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22625512680632354376646135 33938269020948531564969203)
    ·
      refine ⟨50907403531422797347453805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33938269020948531564969203 50907403531422797347453805)
      ·
        refine ⟨19090276324283549005295177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50907403531422797347453805 19090276324283549005295177)
        ·
          refine ⟨14317707243212661753971383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19090276324283549005295177 14317707243212661753971383)
          ·
            refine ⟨21476560864818992630957075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14317707243212661753971383 21476560864818992630957075)
            ·
              refine ⟨32214841297228488946435613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21476560864818992630957075 32214841297228488946435613)
              ·
                refine ⟨12080565486460683354913355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32214841297228488946435613 12080565486460683354913355)
                ·
                  refine ⟨18120848229691025032370033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12080565486460683354913355 18120848229691025032370033)
                  ·
                    refine ⟨13590636172268268774277525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18120848229691025032370033 13590636172268268774277525)
                    ·
                      refine ⟨637061070575075098794259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13590636172268268774277525 637061070575075098794259)
                      ·
                        rfl

theorem cell23_1240672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1240672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240672 prefixEnd_1240672 := by exact prefixLift 1240672
  have htrace : WordTrace (prefixWord ++ tailWord_1240672) baseStart_1240672 baseEnd_1240672 := by
    simpa [prefixWord, tailWord_1240672, baseEnd_1240672] using wordTrace_append hprefix tailTrace_1240672
  have hstable : (prefixWord ++ tailWord_1240672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240672).length < 2 ^ (prefixWord ++ tailWord_1240672).sum := by decide
  have hdescent : baseEnd_1240672 < baseStart_1240672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240699 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 1, 5]
def baseStart_1240699 : Nat := 118140960795 + 1240699 * 2 ^ 59
def prefixEnd_1240699 : Nat := 4983230072969 + 3 ^ 40 * 1240699 * 2
def baseEnd_1240699 : Nat := 212358311517582164385545

theorem tailTrace_1240699 : CollatzResearch.WordTrace tailWord_1240699 prefixEnd_1240699 212358311517582164385545 := by
  unfold tailWord_1240699
  simp only [CollatzResearch.WordTrace]
  refine ⟨45252010132166892364525151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30168006754777928243016767 45252010132166892364525151)
  ·
    refine ⟨67878015198250338546787727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45252010132166892364525151 67878015198250338546787727)
    ·
      refine ⟨101817022797375507820181591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67878015198250338546787727 101817022797375507820181591)
      ·
        refine ⟨152725534196063261730272387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101817022797375507820181591 152725534196063261730272387)
        ·
          refine ⟨229088301294094892595408581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152725534196063261730272387 229088301294094892595408581)
          ·
            refine ⟨42954056492642792361639109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229088301294094892595408581 42954056492642792361639109)
            ·
              refine ⟨8053885592370523567807333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42954056492642792361639109 8053885592370523567807333)
              ·
                refine ⟨1510103548569473168963875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8053885592370523567807333 1510103548569473168963875)
                ·
                  refine ⟨2265155322854209753445813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510103548569473168963875 2265155322854209753445813)
                  ·
                    refine ⟨212358311517582164385545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2265155322854209753445813 212358311517582164385545)
                    ·
                      rfl

theorem cell23_1240699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 5].length) (baseStart_1240699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240699 prefixEnd_1240699 := by exact prefixLift 1240699
  have htrace : WordTrace (prefixWord ++ tailWord_1240699) baseStart_1240699 baseEnd_1240699 := by
    simpa [prefixWord, tailWord_1240699, baseEnd_1240699] using wordTrace_append hprefix tailTrace_1240699
  have hstable : (prefixWord ++ tailWord_1240699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240699).length < 2 ^ (prefixWord ++ tailWord_1240699).sum := by decide
  have hdescent : baseEnd_1240699 < baseStart_1240699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240713 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 1, 1, 3]
def baseStart_1240713 : Nat := 118140960795 + 1240713 * 2 ^ 59
def prefixEnd_1240713 : Nat := 4983230072969 + 3 ^ 40 * 1240713 * 2
def baseEnd_1240713 : Nat := 637082123281909438381571

theorem tailTrace_1240713 : CollatzResearch.WordTrace tailWord_1240713 prefixEnd_1240713 637082123281909438381571 := by
  unfold tailWord_1240713
  simp only [CollatzResearch.WordTrace]
  refine ⟨45252520754116172755534793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30168347169410781837023195 45252520754116172755534793)
  ·
    refine ⟨33939390565587129566651095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45252520754116172755534793 33939390565587129566651095)
    ·
      refine ⟨50909085848380694349976643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33939390565587129566651095 50909085848380694349976643)
      ·
        refine ⟨76363628772571041524964965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50909085848380694349976643 76363628772571041524964965)
        ·
          refine ⟨14318180394857070285930931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76363628772571041524964965 14318180394857070285930931)
          ·
            refine ⟨21477270592285605428896397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14318180394857070285930931 21477270592285605428896397)
            ·
              refine ⟨8053976472107102035836149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21477270592285605428896397 8053976472107102035836149)
              ·
                refine ⟨755060294260040815859639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8053976472107102035836149 755060294260040815859639)
                ·
                  refine ⟨1132590441390061223789459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755060294260040815859639 1132590441390061223789459)
                  ·
                    refine ⟨1698885662085091835684189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132590441390061223789459 1698885662085091835684189)
                    ·
                      refine ⟨637082123281909438381571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1698885662085091835684189 637082123281909438381571)
                      ·
                        rfl

theorem cell23_1240713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 1, 3].length) (baseStart_1240713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240713 prefixEnd_1240713 := by exact prefixLift 1240713
  have htrace : WordTrace (prefixWord ++ tailWord_1240713) baseStart_1240713 baseEnd_1240713 := by
    simpa [prefixWord, tailWord_1240713, baseEnd_1240713] using wordTrace_append hprefix tailTrace_1240713
  have hstable : (prefixWord ++ tailWord_1240713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240713).length < 2 ^ (prefixWord ++ tailWord_1240713).sum := by decide
  have hdescent : baseEnd_1240713 < baseStart_1240713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240739 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1240739 : Nat := 118140960795 + 1240739 * 2 ^ 59
def prefixEnd_1240739 : Nat := 4983230072969 + 3 ^ 40 * 1240739 * 2
def baseEnd_1240739 : Nat := 637095473778926336656451

theorem tailTrace_1240739 : CollatzResearch.WordTrace tailWord_1240739 prefixEnd_1240739 637095473778926336656451 := by
  unfold tailWord_1240739
  simp only [CollatzResearch.WordTrace]
  refine ⟨45253469052021979195981271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30168979368014652797320847 45253469052021979195981271)
  ·
    refine ⟨67880203578032968793971907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45253469052021979195981271 67880203578032968793971907)
    ·
      refine ⟨101820305367049453190957861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67880203578032968793971907 101820305367049453190957861)
      ·
        refine ⟨19091307256321772473304599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101820305367049453190957861 19091307256321772473304599)
        ·
          refine ⟨28636960884482658709956899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19091307256321772473304599 28636960884482658709956899)
          ·
            refine ⟨42955441326723988064935349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28636960884482658709956899 42955441326723988064935349)
            ·
              refine ⟨4027072624380373881087689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42955441326723988064935349 4027072624380373881087689)
              ·
                refine ⟨3020304468285280410815767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027072624380373881087689 3020304468285280410815767)
                ·
                  refine ⟨4530456702427920616223651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020304468285280410815767 4530456702427920616223651)
                  ·
                    refine ⟨6795685053641880924335477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4530456702427920616223651 6795685053641880924335477)
                    ·
                      refine ⟨637095473778926336656451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6795685053641880924335477 637095473778926336656451)
                      ·
                        rfl

theorem cell23_1240739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1240739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240739 prefixEnd_1240739 := by exact prefixLift 1240739
  have htrace : WordTrace (prefixWord ++ tailWord_1240739) baseStart_1240739 baseEnd_1240739 := by
    simpa [prefixWord, tailWord_1240739, baseEnd_1240739] using wordTrace_append hprefix tailTrace_1240739
  have hstable : (prefixWord ++ tailWord_1240739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240739).length < 2 ^ (prefixWord ++ tailWord_1240739).sum := by decide
  have hdescent : baseEnd_1240739 < baseStart_1240739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240750 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1240750 : Nat := 118140960795 + 1240750 * 2 ^ 59
def prefixEnd_1240750 : Nat := 4983230072969 + 3 ^ 40 * 1240750 * 2
def baseEnd_1240750 : Nat := 212367040688708597872967

theorem tailTrace_1240750 : CollatzResearch.WordTrace tailWord_1240750 prefixEnd_1240750 212367040688708597872967 := by
  unfold tailWord_1240750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656733781872766009328963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30169246836654752049754469 5656733781872766009328963)
  ·
    refine ⟨8485100672809149013993445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656733781872766009328963 8485100672809149013993445)
    ·
      refine ⟨1590956376151715440123771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8485100672809149013993445 1590956376151715440123771)
      ·
        refine ⟨2386434564227573160185657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590956376151715440123771 2386434564227573160185657)
        ·
          refine ⟨1789825923170679870139243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2386434564227573160185657 1789825923170679870139243)
          ·
            refine ⟨2684738884756019805208865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789825923170679870139243 2684738884756019805208865)
            ·
              refine ⟨2013554163567014853906649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684738884756019805208865 2013554163567014853906649)
              ·
                refine ⟨1510165622675261140429987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013554163567014853906649 1510165622675261140429987)
                ·
                  refine ⟨2265248434012891710644981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510165622675261140429987 2265248434012891710644981)
                  ·
                    refine ⟨212367040688708597872967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2265248434012891710644981 212367040688708597872967)
                    ·
                      rfl

theorem cell23_1240750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1240750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240750 prefixEnd_1240750 := by exact prefixLift 1240750
  have htrace : WordTrace (prefixWord ++ tailWord_1240750) baseStart_1240750 baseEnd_1240750 := by
    simpa [prefixWord, tailWord_1240750, baseEnd_1240750] using wordTrace_append hprefix tailTrace_1240750
  have hstable : (prefixWord ++ tailWord_1240750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240750).length < 2 ^ (prefixWord ++ tailWord_1240750).sum := by decide
  have hdescent : baseEnd_1240750 < baseStart_1240750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240759 : List Nat := [1, 1, 3, 1, 5, 2, 1, 9]
def baseStart_1240759 : Nat := 118140960795 + 1240759 * 2 ^ 59
def prefixEnd_1240759 : Nat := 4983230072969 + 3 ^ 40 * 1240759 * 2
def baseEnd_1240759 : Nat := 23596509014519120681717

theorem tailTrace_1240759 : CollatzResearch.WordTrace tailWord_1240759 prefixEnd_1240759 23596509014519120681717 := by
  unfold tailWord_1240759
  simp only [CollatzResearch.WordTrace]
  refine ⟨45254198511949522611709331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30169465674633015074472887 45254198511949522611709331)
  ·
    refine ⟨67881297767924283917563997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45254198511949522611709331 67881297767924283917563997)
    ·
      refine ⟨25455486662971606469086499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67881297767924283917563997 25455486662971606469086499)
      ·
        refine ⟨38183229994457409703629749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25455486662971606469086499 38183229994457409703629749)
        ·
          refine ⟨3579677811980382159715289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38183229994457409703629749 3579677811980382159715289)
          ·
            refine ⟨2684758358985286619786467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3579677811980382159715289 2684758358985286619786467)
            ·
              refine ⟨4027137538477929929679701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684758358985286619786467 4027137538477929929679701)
              ·
                refine ⟨23596509014519120681717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4027137538477929929679701 23596509014519120681717)
                ·
                  rfl

theorem cell23_1240759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 9].length) (baseStart_1240759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240759 prefixEnd_1240759 := by exact prefixLift 1240759
  have htrace : WordTrace (prefixWord ++ tailWord_1240759) baseStart_1240759 baseEnd_1240759 := by
    simpa [prefixWord, tailWord_1240759, baseEnd_1240759] using wordTrace_append hprefix tailTrace_1240759
  have hstable : (prefixWord ++ tailWord_1240759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240759).length < 2 ^ (prefixWord ++ tailWord_1240759).sum := by decide
  have hdescent : baseEnd_1240759 < baseStart_1240759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240807 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1240807 : Nat := 118140960795 + 1240807 * 2 ^ 59
def prefixEnd_1240807 : Nat := 4983230072969 + 3 ^ 40 * 1240807 * 2
def baseEnd_1240807 : Nat := 637130390463432070606139

theorem tailTrace_1240807 : CollatzResearch.WordTrace tailWord_1240807 prefixEnd_1240807 637130390463432070606139 := by
  unfold tailWord_1240807
  simp only [CollatzResearch.WordTrace]
  refine ⟨45255949215775626809456675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30170632810517084539637783 45255949215775626809456675)
  ·
    refine ⟨67883923823663440214185013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45255949215775626809456675 67883923823663440214185013)
    ·
      refine ⟨6364117858468447520079845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67883923823663440214185013 6364117858468447520079845)
      ·
        refine ⟨1193272098462833910014971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6364117858468447520079845 1193272098462833910014971)
        ·
          refine ⟨1789908147694250865022457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193272098462833910014971 1789908147694250865022457)
          ·
            refine ⟨1342431110770688148766843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789908147694250865022457 1342431110770688148766843)
            ·
              refine ⟨2013646666156032223150265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342431110770688148766843 2013646666156032223150265)
              ·
                refine ⟨1510234999617024167362699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013646666156032223150265 1510234999617024167362699)
                ·
                  refine ⟨2265352499425536251044049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510234999617024167362699 2265352499425536251044049)
                  ·
                    refine ⟨1699014374569152188283037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2265352499425536251044049 1699014374569152188283037)
                    ·
                      refine ⟨637130390463432070606139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699014374569152188283037 637130390463432070606139)
                      ·
                        rfl

theorem cell23_1240807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1240807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240807 prefixEnd_1240807 := by exact prefixLift 1240807
  have htrace : WordTrace (prefixWord ++ tailWord_1240807) baseStart_1240807 baseEnd_1240807 := by
    simpa [prefixWord, tailWord_1240807, baseEnd_1240807] using wordTrace_append hprefix tailTrace_1240807
  have hstable : (prefixWord ++ tailWord_1240807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240807).length < 2 ^ (prefixWord ++ tailWord_1240807).sum := by decide
  have hdescent : baseEnd_1240807 < baseStart_1240807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240820 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1240820 : Nat := 118140960795 + 1240820 * 2 ^ 59
def prefixEnd_1240820 : Nat := 4983230072969 + 3 ^ 40 * 1240820 * 2
def baseEnd_1240820 : Nat := 637137065711940519743579

theorem tailTrace_1240820 : CollatzResearch.WordTrace tailWord_1240820 prefixEnd_1240820 637137065711940519743579 := by
  unfold tailWord_1240820
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628211682364265014839957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30170948909819020019786609 22628211682364265014839957)
  ·
    refine ⟨1060697422610824922570623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22628211682364265014839957 1060697422610824922570623)
    ·
      refine ⟨1591046133916237383855935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060697422610824922570623 1591046133916237383855935)
      ·
        refine ⟨2386569200874356075783903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591046133916237383855935 2386569200874356075783903)
        ·
          refine ⟨3579853801311534113675855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386569200874356075783903 3579853801311534113675855)
          ·
            refine ⟨5369780701967301170513783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579853801311534113675855 5369780701967301170513783)
            ·
              refine ⟨8054671052950951755770675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369780701967301170513783 8054671052950951755770675)
              ·
                refine ⟨12082006579426427633656013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8054671052950951755770675 12082006579426427633656013)
                ·
                  refine ⟨4530752467284910362621005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12082006579426427633656013 4530752467284910362621005)
                  ·
                    refine ⟨1699032175231841385982877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4530752467284910362621005 1699032175231841385982877)
                    ·
                      refine ⟨637137065711940519743579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699032175231841385982877 637137065711940519743579)
                      ·
                        rfl

theorem cell23_1240820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1240820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240820 prefixEnd_1240820 := by exact prefixLift 1240820
  have htrace : WordTrace (prefixWord ++ tailWord_1240820) baseStart_1240820 baseEnd_1240820 := by
    simpa [prefixWord, tailWord_1240820, baseEnd_1240820] using wordTrace_append hprefix tailTrace_1240820
  have hstable : (prefixWord ++ tailWord_1240820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240820).length < 2 ^ (prefixWord ++ tailWord_1240820).sum := by decide
  have hdescent : baseEnd_1240820 < baseStart_1240820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240829 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1240829 : Nat := 118140960795 + 1240829 * 2 ^ 59
def prefixEnd_1240829 : Nat := 4983230072969 + 3 ^ 40 * 1240829 * 2
def baseEnd_1240829 : Nat := 637141687037830984531037

theorem tailTrace_1240829 : CollatzResearch.WordTrace tailWord_1240829 prefixEnd_1240829 637141687037830984531037 := by
  unfold tailWord_1240829
  simp only [CollatzResearch.WordTrace]
  refine ⟨45256751621695924566757541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30171167747797283044505027 45256751621695924566757541)
  ·
    refine ⟨8485640929067985856267039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45256751621695924566757541 8485640929067985856267039)
    ·
      refine ⟨12728461393601978784400559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8485640929067985856267039 12728461393601978784400559)
      ·
        refine ⟨19092692090402968176600839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12728461393601978784400559 19092692090402968176600839)
        ·
          refine ⟨28639038135604452264901259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19092692090402968176600839 28639038135604452264901259)
          ·
            refine ⟨42958557203406678397351889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28639038135604452264901259 42958557203406678397351889)
            ·
              refine ⟨32218917902555008798013917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42958557203406678397351889 32218917902555008798013917)
              ·
                refine ⟨12082094213458128299255219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32218917902555008798013917 12082094213458128299255219)
                ·
                  refine ⟨18123141320187192448882829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12082094213458128299255219 18123141320187192448882829)
                  ·
                    refine ⟨6796177995070197168331061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18123141320187192448882829 6796177995070197168331061)
                    ·
                      refine ⟨637141687037830984531037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6796177995070197168331061 637141687037830984531037)
                      ·
                        rfl

theorem cell23_1240829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1240829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240829 prefixEnd_1240829 := by exact prefixLift 1240829
  have htrace : WordTrace (prefixWord ++ tailWord_1240829) baseStart_1240829 baseEnd_1240829 := by
    simpa [prefixWord, tailWord_1240829, baseEnd_1240829] using wordTrace_append hprefix tailTrace_1240829
  have hstable : (prefixWord ++ tailWord_1240829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240829).length < 2 ^ (prefixWord ++ tailWord_1240829).sum := by decide
  have hdescent : baseEnd_1240829 < baseStart_1240829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240843 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 4, 2, 2]
def baseStart_1240843 : Nat := 118140960795 + 1240843 * 2 ^ 59
def prefixEnd_1240843 : Nat := 4983230072969 + 3 ^ 40 * 1240843 * 2
def baseEnd_1240843 : Nat := 637148875766993929755973

theorem tailTrace_1240843 : CollatzResearch.WordTrace tailWord_1240843 prefixEnd_1240843 637148875766993929755973 := by
  unfold tailWord_1240843
  simp only [CollatzResearch.WordTrace]
  refine ⟨45257262243645204957767183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30171508162430136638511455 45257262243645204957767183)
  ·
    refine ⟨67885893365467807436650775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45257262243645204957767183 67885893365467807436650775)
    ·
      refine ⟨101828840048201711154976163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67885893365467807436650775 101828840048201711154976163)
      ·
        refine ⟨152743260072302566732464245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101828840048201711154976163 152743260072302566732464245)
        ·
          refine ⟨14319680631778365631168523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152743260072302566732464245 14319680631778365631168523)
          ·
            refine ⟨21479520947667548446752785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14319680631778365631168523 21479520947667548446752785)
            ·
              refine ⟨16109640710750661335064589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21479520947667548446752785 16109640710750661335064589)
              ·
                refine ⟨6041115266531498000649221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16109640710750661335064589 6041115266531498000649221)
                ·
                  refine ⟨1132709112474655875121729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6041115266531498000649221 1132709112474655875121729)
                  ·
                    refine ⟨849531834355991906341297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132709112474655875121729 849531834355991906341297)
                    ·
                      refine ⟨637148875766993929755973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849531834355991906341297 637148875766993929755973)
                      ·
                        rfl

theorem cell23_1240843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 2, 2].length) (baseStart_1240843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240843 prefixEnd_1240843 := by exact prefixLift 1240843
  have htrace : WordTrace (prefixWord ++ tailWord_1240843) baseStart_1240843 baseEnd_1240843 := by
    simpa [prefixWord, tailWord_1240843, baseEnd_1240843] using wordTrace_append hprefix tailTrace_1240843
  have hstable : (prefixWord ++ tailWord_1240843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240843).length < 2 ^ (prefixWord ++ tailWord_1240843).sum := by decide
  have hdescent : baseEnd_1240843 < baseStart_1240843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240846 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1240846 : Nat := 118140960795 + 1240846 * 2 ^ 59
def prefixEnd_1240846 : Nat := 4983230072969 + 3 ^ 40 * 1240846 * 2
def baseEnd_1240846 : Nat := 637150416208957418018459

theorem tailTrace_1240846 : CollatzResearch.WordTrace tailWord_1240846 prefixEnd_1240846 637150416208957418018459 := by
  unfold tailWord_1240846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657171457829292058765799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30171581108422890980084261 5657171457829292058765799)
  ·
    refine ⟨8485757186743938088148699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657171457829292058765799 8485757186743938088148699)
    ·
      refine ⟨12728635780115907132223049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8485757186743938088148699 12728635780115907132223049)
      ·
        refine ⟨9546476835086930349167287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12728635780115907132223049 9546476835086930349167287)
        ·
          refine ⟨14319715252630395523750931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546476835086930349167287 14319715252630395523750931)
          ·
            refine ⟨21479572878945593285626397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14319715252630395523750931 21479572878945593285626397)
            ·
              refine ⟨8054839829604597482109899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21479572878945593285626397 8054839829604597482109899)
              ·
                refine ⟨12082259744406896223164849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8054839829604597482109899 12082259744406896223164849)
                ·
                  refine ⟨9061694808305172167373637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12082259744406896223164849 9061694808305172167373637)
                  ·
                    refine ⟨1699067776557219781382557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9061694808305172167373637 1699067776557219781382557)
                    ·
                      refine ⟨637150416208957418018459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699067776557219781382557 637150416208957418018459)
                      ·
                        rfl

theorem cell23_1240846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1240846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240846 prefixEnd_1240846 := by exact prefixLift 1240846
  have htrace : WordTrace (prefixWord ++ tailWord_1240846) baseStart_1240846 baseEnd_1240846 := by
    simpa [prefixWord, tailWord_1240846, baseEnd_1240846] using wordTrace_append hprefix tailTrace_1240846
  have hstable : (prefixWord ++ tailWord_1240846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240846).length < 2 ^ (prefixWord ++ tailWord_1240846).sum := by decide
  have hdescent : baseEnd_1240846 < baseStart_1240846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240849 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 7]
def baseStart_1240849 : Nat := 118140960795 + 1240849 * 2 ^ 59
def prefixEnd_1240849 : Nat := 4983230072969 + 3 ^ 40 * 1240849 * 2
def baseEnd_1240849 : Nat := 70794661850102322920105

theorem tailTrace_1240849 : CollatzResearch.WordTrace tailWord_1240849 prefixEnd_1240849 70794661850102322920105 := by
  unfold tailWord_1240849
  simp only [CollatzResearch.WordTrace]
  refine ⟨45257481081623467982485601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30171654054415645321657067 45257481081623467982485601)
  ·
    refine ⟨33943110811217600986864201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45257481081623467982485601 33943110811217600986864201)
    ·
      refine ⟨25457333108413200740148151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33943110811217600986864201 25457333108413200740148151)
      ·
        refine ⟨38185999662619801110222227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25457333108413200740148151 38185999662619801110222227)
        ·
          refine ⟨57278999493929701665333341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38185999662619801110222227 57278999493929701665333341)
          ·
            refine ⟨21479624810223638124500003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57278999493929701665333341 21479624810223638124500003)
            ·
              refine ⟨32219437215335457186750005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21479624810223638124500003 32219437215335457186750005)
              ·
                refine ⟨3020572238937699111257813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32219437215335457186750005 3020572238937699111257813)
                ·
                  refine ⟨70794661850102322920105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3020572238937699111257813 70794661850102322920105)
                  ·
                    rfl

theorem cell23_1240849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_1240849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240849 prefixEnd_1240849 := by exact prefixLift 1240849
  have htrace : WordTrace (prefixWord ++ tailWord_1240849) baseStart_1240849 baseEnd_1240849 := by
    simpa [prefixWord, tailWord_1240849, baseEnd_1240849] using wordTrace_append hprefix tailTrace_1240849
  have hstable : (prefixWord ++ tailWord_1240849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240849).length < 2 ^ (prefixWord ++ tailWord_1240849).sum := by decide
  have hdescent : baseEnd_1240849 < baseStart_1240849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240860 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1240860 : Nat := 118140960795 + 1240860 * 2 ^ 59
def prefixEnd_1240860 : Nat := 4983230072969 + 3 ^ 40 * 1240860 * 2
def baseEnd_1240860 : Nat := 637157604938120363243395

theorem tailTrace_1240860 : CollatzResearch.WordTrace tailWord_1240860 prefixEnd_1240860 637157604938120363243395 := by
  unfold tailWord_1240860
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628941142291808430568017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30171921523055744574090689 22628941142291808430568017)
  ·
    refine ⟨16971705856718856322926013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22628941142291808430568017 16971705856718856322926013)
    ·
      refine ⟨6364389696269571121097255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16971705856718856322926013 6364389696269571121097255)
      ·
        refine ⟨9546584544404356681645883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364389696269571121097255 9546584544404356681645883)
        ·
          refine ⟨14319876816606535022468825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546584544404356681645883 14319876816606535022468825)
          ·
            refine ⟨10739907612454901266851619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14319876816606535022468825 10739907612454901266851619)
            ·
              refine ⟨16109861418682351900277429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10739907612454901266851619 16109861418682351900277429)
              ·
                refine ⟨1510299508001470490651009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16109861418682351900277429 1510299508001470490651009)
                ·
                  refine ⟨1132724631001102867988257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510299508001470490651009 1132724631001102867988257)
                  ·
                    refine ⟨849543473250827150991193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132724631001102867988257 849543473250827150991193)
                    ·
                      refine ⟨637157604938120363243395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849543473250827150991193 637157604938120363243395)
                      ·
                        rfl

theorem cell23_1240860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1240860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240860 prefixEnd_1240860 := by exact prefixLift 1240860
  have htrace : WordTrace (prefixWord ++ tailWord_1240860) baseStart_1240860 baseEnd_1240860 := by
    simpa [prefixWord, tailWord_1240860, baseEnd_1240860] using wordTrace_append hprefix tailTrace_1240860
  have hstable : (prefixWord ++ tailWord_1240860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240860).length < 2 ^ (prefixWord ++ tailWord_1240860).sum := by decide
  have hdescent : baseEnd_1240860 < baseStart_1240860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240866 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1240866 : Nat := 118140960795 + 1240866 * 2 ^ 59
def prefixEnd_1240866 : Nat := 4983230072969 + 3 ^ 40 * 1240866 * 2
def baseEnd_1240866 : Nat := 70795631758005259974263

theorem tailTrace_1240866 : CollatzResearch.WordTrace tailWord_1240866 prefixEnd_1240866 70795631758005259974263 := by
  unfold tailWord_1240866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11314525280640469971463613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30172067415041253257236301 11314525280640469971463613)
  ·
    refine ⟨4242946980240176239298855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11314525280640469971463613 4242946980240176239298855)
    ·
      refine ⟨6364420470360264358948283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242946980240176239298855 6364420470360264358948283)
      ·
        refine ⟨9546630705540396538422425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6364420470360264358948283 9546630705540396538422425)
        ·
          refine ⟨7159973029155297403816819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9546630705540396538422425 7159973029155297403816819)
          ·
            refine ⟨10739959543732946105725229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7159973029155297403816819 10739959543732946105725229)
            ·
              refine ⟨4027484828899854789646961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10739959543732946105725229 4027484828899854789646961)
              ·
                refine ⟨3020613621674891092235221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027484828899854789646961 3020613621674891092235221)
                ·
                  refine ⟨70795631758005259974263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3020613621674891092235221 70795631758005259974263)
                  ·
                    rfl

theorem cell23_1240866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1240866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240866 prefixEnd_1240866 := by exact prefixLift 1240866
  have htrace : WordTrace (prefixWord ++ tailWord_1240866) baseStart_1240866 baseEnd_1240866 := by
    simpa [prefixWord, tailWord_1240866, baseEnd_1240866] using wordTrace_append hprefix tailTrace_1240866
  have hstable : (prefixWord ++ tailWord_1240866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240866).length < 2 ^ (prefixWord ++ tailWord_1240866).sum := by decide
  have hdescent : baseEnd_1240866 < baseStart_1240866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240879 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 7]
def baseStart_1240879 : Nat := 118140960795 + 1240879 * 2 ^ 59
def prefixEnd_1240879 : Nat := 4983230072969 + 3 ^ 40 * 1240879 * 2
def baseEnd_1240879 : Nat := 212389120356851929635269

theorem tailTrace_1240879 : CollatzResearch.WordTrace tailWord_1240879 prefixEnd_1240879 212389120356851929635269 := by
  unfold tailWord_1240879
  simp only [CollatzResearch.WordTrace]
  refine ⟨45258575271514783106077691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30172383514343188737385127 45258575271514783106077691)
  ·
    refine ⟨67887862907272174659116537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45258575271514783106077691 67887862907272174659116537)
    ·
      refine ⟨50915897180454130994337403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67887862907272174659116537 50915897180454130994337403)
      ·
        refine ⟨76373845770681196491506105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50915897180454130994337403 76373845770681196491506105)
        ·
          refine ⟨57280384328010897368629579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76373845770681196491506105 57280384328010897368629579)
          ·
            refine ⟨85920576492016346052944369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57280384328010897368629579 85920576492016346052944369)
            ·
              refine ⟨64440432369012259539708277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85920576492016346052944369 64440432369012259539708277)
              ·
                refine ⟨6041290534594899331847651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64440432369012259539708277 6041290534594899331847651)
                ·
                  refine ⟨9061935801892348997771477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6041290534594899331847651 9061935801892348997771477)
                  ·
                    refine ⟨212389120356851929635269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9061935801892348997771477 212389120356851929635269)
                    ·
                      rfl

theorem cell23_1240879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_1240879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240879 prefixEnd_1240879 := by exact prefixLift 1240879
  have htrace : WordTrace (prefixWord ++ tailWord_1240879) baseStart_1240879 baseEnd_1240879 := by
    simpa [prefixWord, tailWord_1240879, baseEnd_1240879] using wordTrace_append hprefix tailTrace_1240879
  have hstable : (prefixWord ++ tailWord_1240879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240879).length < 2 ^ (prefixWord ++ tailWord_1240879).sum := by decide
  have hdescent : baseEnd_1240879 < baseStart_1240879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240893 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1240893 : Nat := 118140960795 + 1240893 * 2 ^ 59
def prefixEnd_1240893 : Nat := 4983230072969 + 3 ^ 40 * 1240893 * 2
def baseEnd_1240893 : Nat := 637174549799718734130743

theorem tailTrace_1240893 : CollatzResearch.WordTrace tailWord_1240893 prefixEnd_1240893 637174549799718734130743 := by
  unfold tailWord_1240893
  simp only [CollatzResearch.WordTrace]
  refine ⟨45259085893464063497087333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30172723928976042331391555 45259085893464063497087333)
  ·
    refine ⟨8486078605024511905703875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45259085893464063497087333 8486078605024511905703875)
    ·
      refine ⟨12729117907536767858555813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8486078605024511905703875 12729117907536767858555813)
      ·
        refine ⟨2386709607663143973479215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12729117907536767858555813 2386709607663143973479215)
        ·
          refine ⟨3580064411494715960218823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386709607663143973479215 3580064411494715960218823)
          ·
            refine ⟨5370096617242073940328235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580064411494715960218823 5370096617242073940328235)
            ·
              refine ⟨8055144925863110910492353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370096617242073940328235 8055144925863110910492353)
              ·
                refine ⟨6041358694397333182869265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8055144925863110910492353 6041358694397333182869265)
                ·
                  refine ⟨4531019020797999887151949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041358694397333182869265 4531019020797999887151949)
                  ·
                    refine ⟨1699132132799249957681981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4531019020797999887151949 1699132132799249957681981)
                    ·
                      refine ⟨637174549799718734130743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699132132799249957681981 637174549799718734130743)
                      ·
                        rfl

theorem cell23_1240893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1240893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240893 prefixEnd_1240893 := by exact prefixLift 1240893
  have htrace : WordTrace (prefixWord ++ tailWord_1240893) baseStart_1240893 baseEnd_1240893 := by
    simpa [prefixWord, tailWord_1240893, baseEnd_1240893] using wordTrace_append hprefix tailTrace_1240893
  have hstable : (prefixWord ++ tailWord_1240893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240893).length < 2 ^ (prefixWord ++ tailWord_1240893).sum := by decide
  have hdescent : baseEnd_1240893 < baseStart_1240893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240894 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_1240894 : Nat := 118140960795 + 1240894 * 2 ^ 59
def prefixEnd_1240894 : Nat := 4983230072969 + 3 ^ 40 * 1240894 * 2
def baseEnd_1240894 : Nat := 637175063280373230218239

theorem tailTrace_1240894 : CollatzResearch.WordTrace tailWord_1240894 prefixEnd_1240894 637175063280373230218239 := by
  unfold tailWord_1240894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657390295807555083484217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30172748244306960445249157 5657390295807555083484217)
  ·
    refine ⟨4243042721855666312613163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5657390295807555083484217 4243042721855666312613163)
    ·
      refine ⟨6364564082783499468919745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4243042721855666312613163 6364564082783499468919745)
      ·
        refine ⟨4773423062087624601689809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6364564082783499468919745 4773423062087624601689809)
        ·
          refine ⟨3580067296565718451267357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4773423062087624601689809 3580067296565718451267357)
          ·
            refine ⟨1342525236212144419225259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3580067296565718451267357 1342525236212144419225259)
            ·
              refine ⟨2013787854318216628837889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342525236212144419225259 2013787854318216628837889)
              ·
                refine ⟨1510340890738662471628417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013787854318216628837889 1510340890738662471628417)
                ·
                  refine ⟨1132755668053996853721313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510340890738662471628417 1132755668053996853721313)
                  ·
                    refine ⟨849566751040497640290985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132755668053996853721313 849566751040497640290985)
                    ·
                      refine ⟨637175063280373230218239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849566751040497640290985 637175063280373230218239)
                      ·
                        rfl

theorem cell23_1240894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_1240894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240894 prefixEnd_1240894 := by exact prefixLift 1240894
  have htrace : WordTrace (prefixWord ++ tailWord_1240894) baseStart_1240894 baseEnd_1240894 := by
    simpa [prefixWord, tailWord_1240894, baseEnd_1240894] using wordTrace_append hprefix tailTrace_1240894
  have hstable : (prefixWord ++ tailWord_1240894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240894).length < 2 ^ (prefixWord ++ tailWord_1240894).sum := by decide
  have hdescent : baseEnd_1240894 < baseStart_1240894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240953 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1240953 : Nat := 118140960795 + 1240953 * 2 ^ 59
def prefixEnd_1240953 : Nat := 4983230072969 + 3 ^ 40 * 1240953 * 2
def baseEnd_1240953 : Nat := 637205358638988499380467

theorem tailTrace_1240953 : CollatzResearch.WordTrace tailWord_1240953 prefixEnd_1240953 637205358638988499380467 := by
  unfold tailWord_1240953
  simp only [CollatzResearch.WordTrace]
  refine ⟨45261274273246693744271513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30174182848831129162847675 45261274273246693744271513)
  ·
    refine ⟨33945955704935020308203635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45261274273246693744271513 33945955704935020308203635)
    ·
      refine ⟨50918933557402530462305453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33945955704935020308203635 50918933557402530462305453)
      ·
        refine ⟨19094600084025948923364545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50918933557402530462305453 19094600084025948923364545)
        ·
          refine ⟨14320950063019461692523409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19094600084025948923364545 14320950063019461692523409)
          ·
            refine ⟨10740712547264596269392557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14320950063019461692523409 10740712547264596269392557)
            ·
              refine ⟨4027767205224223601022209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10740712547264596269392557 4027767205224223601022209)
              ·
                refine ⟨3020825403918167700766657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4027767205224223601022209 3020825403918167700766657)
                ·
                  refine ⟨2265619052938625775574993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020825403918167700766657 2265619052938625775574993)
                  ·
                    refine ⟨1699214289703969331681245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2265619052938625775574993 1699214289703969331681245)
                    ·
                      refine ⟨637205358638988499380467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699214289703969331681245 637205358638988499380467)
                      ·
                        rfl

theorem cell23_1240953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1240953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1240953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1240953 prefixEnd_1240953 := by exact prefixLift 1240953
  have htrace : WordTrace (prefixWord ++ tailWord_1240953) baseStart_1240953 baseEnd_1240953 := by
    simpa [prefixWord, tailWord_1240953, baseEnd_1240953] using wordTrace_append hprefix tailTrace_1240953
  have hstable : (prefixWord ++ tailWord_1240953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240953).length < 2 ^ (prefixWord ++ tailWord_1240953).sum := by decide
  have hdescent : baseEnd_1240953 < baseStart_1240953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241016 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1241016 : Nat := 118140960795 + 1241016 * 2 ^ 59
def prefixEnd_1241016 : Nat := 4983230072969 + 3 ^ 40 * 1241016 * 2
def baseEnd_1241016 : Nat := 212412569306740584297559

theorem tailTrace_1241016 : CollatzResearch.WordTrace tailWord_1241016 prefixEnd_1241016 212412569306740584297559 := by
  unfold tailWord_1241016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22631786036009227751907451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30175714714678970335876601 22631786036009227751907451)
  ·
    refine ⟨33947679054013841627861177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22631786036009227751907451 33947679054013841627861177)
    ·
      refine ⟨25460759290510381220895883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33947679054013841627861177 25460759290510381220895883)
      ·
        refine ⟨38191138935765571831343825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25460759290510381220895883 38191138935765571831343825)
        ·
          refine ⟨28643354201824178873507869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38191138935765571831343825 28643354201824178873507869)
          ·
            refine ⟨10741257825684067077565451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28643354201824178873507869 10741257825684067077565451)
            ·
              refine ⟨16111886738526100616348177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10741257825684067077565451 16111886738526100616348177)
              ·
                refine ⟨12083915053894575462261133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16111886738526100616348177 12083915053894575462261133)
                ·
                  refine ⟨4531468145210465798347925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12083915053894575462261133 4531468145210465798347925)
                  ·
                    refine ⟨212412569306740584297559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4531468145210465798347925 212412569306740584297559)
                    ·
                      rfl

theorem cell23_1241016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1241016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241016 prefixEnd_1241016 := by exact prefixLift 1241016
  have htrace : WordTrace (prefixWord ++ tailWord_1241016) baseStart_1241016 baseEnd_1241016 := by
    simpa [prefixWord, tailWord_1241016, baseEnd_1241016] using wordTrace_append hprefix tailTrace_1241016
  have hstable : (prefixWord ++ tailWord_1241016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241016).length < 2 ^ (prefixWord ++ tailWord_1241016).sum := by decide
  have hdescent : baseEnd_1241016 < baseStart_1241016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241017 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1241017 : Nat := 118140960795 + 1241017 * 2 ^ 59
def prefixEnd_1241017 : Nat := 4983230072969 + 3 ^ 40 * 1241017 * 2
def baseEnd_1241017 : Nat := 637238221400876248980173

theorem tailTrace_1241017 : CollatzResearch.WordTrace tailWord_1241017 prefixEnd_1241017 637238221400876248980173 := by
  unfold tailWord_1241017
  simp only [CollatzResearch.WordTrace]
  refine ⟨45263608545014832674601305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30175739030009888449734203 45263608545014832674601305)
  ·
    refine ⟨33947706408761124505950979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45263608545014832674601305 33947706408761124505950979)
    ·
      refine ⟨50921559613141686758926469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33947706408761124505950979 50921559613141686758926469)
      ·
        refine ⟨9547792427464066267298713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50921559613141686758926469 9547792427464066267298713)
        ·
          refine ⟨7160844320598049700474035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9547792427464066267298713 7160844320598049700474035)
          ·
            refine ⟨10741266480897074550711053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160844320598049700474035 10741266480897074550711053)
            ·
              refine ⟨4027974930336402956516645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10741266480897074550711053 4027974930336402956516645)
              ·
                refine ⟨755245299438075554346871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4027974930336402956516645 755245299438075554346871)
                ·
                  refine ⟨1132867949157113331520307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755245299438075554346871 1132867949157113331520307)
                  ·
                    refine ⟨1699301923735669997280461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132867949157113331520307 1699301923735669997280461)
                    ·
                      refine ⟨637238221400876248980173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699301923735669997280461 637238221400876248980173)
                      ·
                        rfl

theorem cell23_1241017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1241017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241017 prefixEnd_1241017 := by exact prefixLift 1241017
  have htrace : WordTrace (prefixWord ++ tailWord_1241017) baseStart_1241017 baseEnd_1241017 := by
    simpa [prefixWord, tailWord_1241017, baseEnd_1241017] using wordTrace_append hprefix tailTrace_1241017
  have hstable : (prefixWord ++ tailWord_1241017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241017).length < 2 ^ (prefixWord ++ tailWord_1241017).sum := by decide
  have hdescent : baseEnd_1241017 < baseStart_1241017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241040 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2]
def baseStart_1241040 : Nat := 118140960795 + 1241040 * 2 ^ 59
def prefixEnd_1241040 : Nat := 4983230072969 + 3 ^ 40 * 1241040 * 2
def baseEnd_1241040 : Nat := 637250031455929658992567

theorem tailTrace_1241040 : CollatzResearch.WordTrace tailWord_1241040 prefixEnd_1241040 637250031455929658992567 := by
  unfold tailWord_1241040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22632223711965753801344287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30176298282621005068459049 22632223711965753801344287)
  ·
    refine ⟨33948335567948630702016431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22632223711965753801344287 33948335567948630702016431)
    ·
      refine ⟨50922503351922946053024647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33948335567948630702016431 50922503351922946053024647)
      ·
        refine ⟨76383755027884419079536971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50922503351922946053024647 76383755027884419079536971)
        ·
          refine ⟨114575632541826628619305457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76383755027884419079536971 114575632541826628619305457)
          ·
            refine ⟨85931724406369971464479093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114575632541826628619305457 85931724406369971464479093)
            ·
              refine ⟨8056099163097184824794915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85931724406369971464479093 8056099163097184824794915)
              ·
                refine ⟨12084148744645777237192373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056099163097184824794915 12084148744645777237192373)
                ·
                  refine ⟨1132888944810541615986785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12084148744645777237192373 1132888944810541615986785)
                  ·
                    refine ⟨849666708607906211990089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132888944810541615986785 849666708607906211990089)
                    ·
                      refine ⟨637250031455929658992567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849666708607906211990089 637250031455929658992567)
                      ·
                        rfl

theorem cell23_1241040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 2, 2].length) (baseStart_1241040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241040 prefixEnd_1241040 := by exact prefixLift 1241040
  have htrace : WordTrace (prefixWord ++ tailWord_1241040) baseStart_1241040 baseEnd_1241040 := by
    simpa [prefixWord, tailWord_1241040, baseEnd_1241040] using wordTrace_append hprefix tailTrace_1241040
  have hstable : (prefixWord ++ tailWord_1241040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241040).length < 2 ^ (prefixWord ++ tailWord_1241040).sum := by decide
  have hdescent : baseEnd_1241040 < baseStart_1241040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241060 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_1241060 : Nat := 118140960795 + 1241060 * 2 ^ 59
def prefixEnd_1241060 : Nat := 4983230072969 + 3 ^ 40 * 1241060 * 2
def baseEnd_1241060 : Nat := 637260301069019580742475

theorem tailTrace_1241060 : CollatzResearch.WordTrace tailWord_1241060 prefixEnd_1241060 637260301069019580742475 := by
  unfold tailWord_1241060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22632588441929525509208317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30176784589239367345611089 22632588441929525509208317)
  ·
    refine ⟨8487220665723572065953119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22632588441929525509208317 8487220665723572065953119)
    ·
      refine ⟨12730830998585358098929679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8487220665723572065953119 12730830998585358098929679)
      ·
        refine ⟨19096246497878037148394519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12730830998585358098929679 19096246497878037148394519)
        ·
          refine ⟨28644369746817055722591779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19096246497878037148394519 28644369746817055722591779)
          ·
            refine ⟨42966554620225583583887669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28644369746817055722591779 42966554620225583583887669)
            ·
              refine ⟨4028114495646148460989469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42966554620225583583887669 4028114495646148460989469)
              ·
                refine ⟨1510542935867305672871051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4028114495646148460989469 1510542935867305672871051)
                ·
                  refine ⟨2265814403800958509306577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510542935867305672871051 2265814403800958509306577)
                  ·
                    refine ⟨1699360802850718881979933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2265814403800958509306577 1699360802850718881979933)
                    ·
                      refine ⟨637260301069019580742475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699360802850718881979933 637260301069019580742475)
                      ·
                        rfl

theorem cell23_1241060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_1241060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241060 prefixEnd_1241060 := by exact prefixLift 1241060
  have htrace : WordTrace (prefixWord ++ tailWord_1241060) baseStart_1241060 baseEnd_1241060 := by
    simpa [prefixWord, tailWord_1241060, baseEnd_1241060] using wordTrace_append hprefix tailTrace_1241060
  have hstable : (prefixWord ++ tailWord_1241060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241060).length < 2 ^ (prefixWord ++ tailWord_1241060).sum := by decide
  have hdescent : baseEnd_1241060 < baseStart_1241060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241063 : List Nat := [1, 1, 5, 2, 3, 1, 10]
def baseStart_1241063 : Nat := 118140960795 + 1241063 * 2 ^ 59
def prefixEnd_1241063 : Nat := 4983230072969 + 3 ^ 40 * 1241063 * 2
def baseEnd_1241063 : Nat := 7867430142110902086481

theorem tailTrace_1241063 : CollatzResearch.WordTrace tailWord_1241063 prefixEnd_1241063 7867430142110902086481 := by
  unfold tailWord_1241063
  simp only [CollatzResearch.WordTrace]
  refine ⟨45265286302848182530775843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30176857535232121687183895 45265286302848182530775843)
  ·
    refine ⟨67897929454272273796163765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45265286302848182530775843 67897929454272273796163765)
    ·
      refine ⟨6365430886338025668390353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67897929454272273796163765 6365430886338025668390353)
      ·
        refine ⟨4774073164753519251292765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6365430886338025668390353 4774073164753519251292765)
        ·
          refine ⟨1790277436782569719234787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4774073164753519251292765 1790277436782569719234787)
          ·
            refine ⟨2685416155173854578852181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790277436782569719234787 2685416155173854578852181)
            ·
              refine ⟨7867430142110902086481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2685416155173854578852181 7867430142110902086481)
              ·
                rfl

theorem cell23_1241063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 10].length) (baseStart_1241063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241063 prefixEnd_1241063 := by exact prefixLift 1241063
  have htrace : WordTrace (prefixWord ++ tailWord_1241063) baseStart_1241063 baseEnd_1241063 := by
    simpa [prefixWord, tailWord_1241063, baseEnd_1241063] using wordTrace_append hprefix tailTrace_1241063
  have hstable : (prefixWord ++ tailWord_1241063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241063).length < 2 ^ (prefixWord ++ tailWord_1241063).sum := by decide
  have hdescent : baseEnd_1241063 < baseStart_1241063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241143 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1241143 : Nat := 118140960795 + 1241143 * 2 ^ 59
def prefixEnd_1241143 : Nat := 4983230072969 + 3 ^ 40 * 1241143 * 2
def baseEnd_1241143 : Nat := 637302919963342756004593

theorem tailTrace_1241143 : CollatzResearch.WordTrace tailWord_1241143 prefixEnd_1241143 637302919963342756004593 := by
  unfold tailWord_1241143
  simp only [CollatzResearch.WordTrace]
  refine ⟨45268204142558356193688083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30178802761705570795792055 45268204142558356193688083)
  ·
    refine ⟨67902306213837534290532125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45268204142558356193688083 67902306213837534290532125)
    ·
      refine ⟨25463364830189075358949547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67902306213837534290532125 25463364830189075358949547)
      ·
        refine ⟨38195047245283613038424321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25463364830189075358949547 38195047245283613038424321)
        ·
          refine ⟨28646285433962709778818241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38195047245283613038424321 28646285433962709778818241)
          ·
            refine ⟨21484714075472032334113681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28646285433962709778818241 21484714075472032334113681)
            ·
              refine ⟨16113535556604024250585261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21484714075472032334113681 16113535556604024250585261)
              ·
                refine ⟨6042575833726509093969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16113535556604024250585261 6042575833726509093969473)
                ·
                  refine ⟨4531931875294881820477105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042575833726509093969473 4531931875294881820477105)
                  ·
                    refine ⟨3398948906471161365357829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531931875294881820477105 3398948906471161365357829)
                    ·
                      refine ⟨637302919963342756004593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3398948906471161365357829 637302919963342756004593)
                      ·
                        rfl

theorem cell23_1241143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1241143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241143 prefixEnd_1241143 := by exact prefixLift 1241143
  have htrace : WordTrace (prefixWord ++ tailWord_1241143) baseStart_1241143 baseEnd_1241143 := by
    simpa [prefixWord, tailWord_1241143, baseEnd_1241143] using wordTrace_append hprefix tailTrace_1241143
  have hstable : (prefixWord ++ tailWord_1241143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241143).length < 2 ^ (prefixWord ++ tailWord_1241143).sum := by decide
  have hdescent : baseEnd_1241143 < baseStart_1241143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241147 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 2, 2, 2]
def baseStart_1241147 : Nat := 118140960795 + 1241147 * 2 ^ 59
def prefixEnd_1241147 : Nat := 4983230072969 + 3 ^ 40 * 1241147 * 2
def baseEnd_1241147 : Nat := 637304973885960740354575

theorem tailTrace_1241147 : CollatzResearch.WordTrace tailWord_1241147 prefixEnd_1241147 637304973885960740354575 := by
  unfold tailWord_1241147
  simp only [CollatzResearch.WordTrace]
  refine ⟨45268350034543864876833695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30178900023029243251222463 45268350034543864876833695)
  ·
    refine ⟨67902525051815797315250543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45268350034543864876833695 67902525051815797315250543)
    ·
      refine ⟨101853787577723695972875815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67902525051815797315250543 101853787577723695972875815)
      ·
        refine ⟨152780681366585543959313723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101853787577723695972875815 152780681366585543959313723)
        ·
          refine ⟨229171022049878315938970585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152780681366585543959313723 229171022049878315938970585)
          ·
            refine ⟨171878266537408736954227939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229171022049878315938970585 171878266537408736954227939)
            ·
              refine ⟨257817399806113105431341909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171878266537408736954227939 257817399806113105431341909)
              ·
                refine ⟨1510648826988943977136769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 257817399806113105431341909 1510648826988943977136769)
                ·
                  refine ⟨1132986620241707982852577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510648826988943977136769 1132986620241707982852577)
                  ·
                    refine ⟨849739965181280987139433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1132986620241707982852577 849739965181280987139433)
                    ·
                      refine ⟨637304973885960740354575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849739965181280987139433 637304973885960740354575)
                      ·
                        rfl

theorem cell23_1241147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 2, 2].length) (baseStart_1241147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241147 prefixEnd_1241147 := by exact prefixLift 1241147
  have htrace : WordTrace (prefixWord ++ tailWord_1241147) baseStart_1241147 baseEnd_1241147 := by
    simpa [prefixWord, tailWord_1241147, baseEnd_1241147] using wordTrace_append hprefix tailTrace_1241147
  have hstable : (prefixWord ++ tailWord_1241147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241147).length < 2 ^ (prefixWord ++ tailWord_1241147).sum := by decide
  have hdescent : baseEnd_1241147 < baseStart_1241147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241163 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3]
def baseStart_1241163 : Nat := 118140960795 + 1241163 * 2 ^ 59
def prefixEnd_1241163 : Nat := 4983230072969 + 3 ^ 40 * 1241163 * 2
def baseEnd_1241163 : Nat := 637313189576432677754501

theorem tailTrace_1241163 : CollatzResearch.WordTrace tailWord_1241163 prefixEnd_1241163 637313189576432677754501 := by
  unfold tailWord_1241163
  simp only [CollatzResearch.WordTrace]
  refine ⟨45268933602485899609416143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30179289068323933072944095 45268933602485899609416143)
  ·
    refine ⟨67903400403728849414124215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45268933602485899609416143 67903400403728849414124215)
    ·
      refine ⟨101855100605593274121186323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67903400403728849414124215 101855100605593274121186323)
      ·
        refine ⟨152782650908389911181779485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101855100605593274121186323 152782650908389911181779485)
        ·
          refine ⟨57293494090646216693167307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152782650908389911181779485 57293494090646216693167307)
          ·
            refine ⟨85940241135969325039750961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57293494090646216693167307 85940241135969325039750961)
            ·
              refine ⟨64455180851976993779813221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85940241135969325039750961 64455180851976993779813221)
              ·
                refine ⟨12085346409745686333714979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64455180851976993779813221 12085346409745686333714979)
                ·
                  refine ⟨18128019614618529500572469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12085346409745686333714979 18128019614618529500572469)
                  ·
                    refine ⟨1699501838870487140678669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18128019614618529500572469 1699501838870487140678669)
                    ·
                      refine ⟨637313189576432677754501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699501838870487140678669 637313189576432677754501)
                      ·
                        rfl

theorem cell23_1241163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3].length) (baseStart_1241163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241163 prefixEnd_1241163 := by exact prefixLift 1241163
  have htrace : WordTrace (prefixWord ++ tailWord_1241163) baseStart_1241163 baseEnd_1241163 := by
    simpa [prefixWord, tailWord_1241163, baseEnd_1241163] using wordTrace_append hprefix tailTrace_1241163
  have hstable : (prefixWord ++ tailWord_1241163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241163).length < 2 ^ (prefixWord ++ tailWord_1241163).sum := by decide
  have hdescent : baseEnd_1241163 < baseStart_1241163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241181 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1241181 : Nat := 118140960795 + 1241181 * 2 ^ 59
def prefixEnd_1241181 : Nat := 4983230072969 + 3 ^ 40 * 1241181 * 2
def baseEnd_1241181 : Nat := 637322432228213607329419

theorem tailTrace_1241181 : CollatzResearch.WordTrace tailWord_1241181 prefixEnd_1241181 637322432228213607329419 := by
  unfold tailWord_1241181
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269590116420688683571397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30179726744280459122380931 45269590116420688683571397)
  ·
    refine ⟨8488048146828879128169637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45269590116420688683571397 8488048146828879128169637)
    ·
      refine ⟨1591509027530414836531807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8488048146828879128169637 1591509027530414836531807)
      ·
        refine ⟨2387263541295622254797711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591509027530414836531807 2387263541295622254797711)
        ·
          refine ⟨3580895311943433382196567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2387263541295622254797711 3580895311943433382196567)
          ·
            refine ⟨5371342967915150073294851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580895311943433382196567 5371342967915150073294851)
            ·
              refine ⟨8057014451872725109942277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371342967915150073294851 8057014451872725109942277)
              ·
                refine ⟨1510690209726135958114177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8057014451872725109942277 1510690209726135958114177)
                ·
                  refine ⟨1133017657294601968585633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510690209726135958114177 1133017657294601968585633)
                  ·
                    refine ⟨849763242970951476439225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1133017657294601968585633 849763242970951476439225)
                    ·
                      refine ⟨637322432228213607329419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849763242970951476439225 637322432228213607329419)
                      ·
                        rfl

theorem cell23_1241181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1241181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241181 prefixEnd_1241181 := by exact prefixLift 1241181
  have htrace : WordTrace (prefixWord ++ tailWord_1241181) baseStart_1241181 baseEnd_1241181 := by
    simpa [prefixWord, tailWord_1241181, baseEnd_1241181] using wordTrace_append hprefix tailTrace_1241181
  have hstable : (prefixWord ++ tailWord_1241181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241181).length < 2 ^ (prefixWord ++ tailWord_1241181).sum := by decide
  have hdescent : baseEnd_1241181 < baseStart_1241181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241183 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 4, 5]
def baseStart_1241183 : Nat := 118140960795 + 1241183 * 2 ^ 59
def prefixEnd_1241183 : Nat := 4983230072969 + 3 ^ 40 * 1241183 * 2
def baseEnd_1241183 : Nat := 212441153063174199834803

theorem tailTrace_1241183 : CollatzResearch.WordTrace tailWord_1241183 prefixEnd_1241183 212441153063174199834803 := by
  unfold tailWord_1241183
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269663062413443025144203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30179775374942295350096135 45269663062413443025144203)
  ·
    refine ⟨67904494593620164537716305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45269663062413443025144203 67904494593620164537716305)
    ·
      refine ⟨50928370945215123403287229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67904494593620164537716305 50928370945215123403287229)
      ·
        refine ⟨19098139104455671276232711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50928370945215123403287229 19098139104455671276232711)
        ·
          refine ⟨28647208656683506914349067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19098139104455671276232711 28647208656683506914349067)
          ·
            refine ⟨42970812985025260371523601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28647208656683506914349067 42970812985025260371523601)
            ·
              refine ⟨32228109738768945278642701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42970812985025260371523601 32228109738768945278642701)
              ·
                refine ⟨12085541152038354479491013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32228109738768945278642701 12085541152038354479491013)
                ·
                  refine ⟨2266038966007191464904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12085541152038354479491013 2266038966007191464904565)
                  ·
                    refine ⟨212441153063174199834803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2266038966007191464904565 212441153063174199834803)
                    ·
                      rfl

theorem cell23_1241183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_1241183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241183 prefixEnd_1241183 := by exact prefixLift 1241183
  have htrace : WordTrace (prefixWord ++ tailWord_1241183) baseStart_1241183 baseEnd_1241183 := by
    simpa [prefixWord, tailWord_1241183, baseEnd_1241183] using wordTrace_append hprefix tailTrace_1241183
  have hstable : (prefixWord ++ tailWord_1241183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241183).length < 2 ^ (prefixWord ++ tailWord_1241183).sum := by decide
  have hdescent : baseEnd_1241183 < baseStart_1241183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241187 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 5]
def baseStart_1241187 : Nat := 118140960795 + 1241187 * 2 ^ 59
def prefixEnd_1241187 : Nat := 4983230072969 + 3 ^ 40 * 1241187 * 2
def baseEnd_1241187 : Nat := 70813945901348953761599

theorem tailTrace_1241187 : CollatzResearch.WordTrace tailWord_1241187 prefixEnd_1241187 70813945901348953761599 := by
  unfold tailWord_1241187
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269808954398951708289815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30179872636265967805526543 45269808954398951708289815)
  ·
    refine ⟨67904713431598427562434723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45269808954398951708289815 67904713431598427562434723)
    ·
      refine ⟨101857070147397641343652085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67904713431598427562434723 101857070147397641343652085)
      ·
        refine ⟨9549100326318528875967383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101857070147397641343652085 9549100326318528875967383)
        ·
          refine ⟨14323650489477793313951075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549100326318528875967383 14323650489477793313951075)
          ·
            refine ⟨21485475734216689970926613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14323650489477793313951075 21485475734216689970926613)
            ·
              refine ⟨1007131675041407342387185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21485475734216689970926613 1007131675041407342387185)
              ·
                refine ⟨755348756281055506790389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007131675041407342387185 755348756281055506790389)
                ·
                  refine ⟨70813945901348953761599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 755348756281055506790389 70813945901348953761599)
                  ·
                    rfl

theorem cell23_1241187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 5].length) (baseStart_1241187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241187 prefixEnd_1241187 := by exact prefixLift 1241187
  have htrace : WordTrace (prefixWord ++ tailWord_1241187) baseStart_1241187 baseEnd_1241187 := by
    simpa [prefixWord, tailWord_1241187, baseEnd_1241187] using wordTrace_append hprefix tailTrace_1241187
  have hstable : (prefixWord ++ tailWord_1241187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241187).length < 2 ^ (prefixWord ++ tailWord_1241187).sum := by decide
  have hdescent : baseEnd_1241187 < baseStart_1241187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241193 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_1241193 : Nat := 118140960795 + 1241193 * 2 ^ 59
def prefixEnd_1241193 : Nat := 4983230072969 + 3 ^ 40 * 1241193 * 2
def baseEnd_1241193 : Nat := 637328593996067560379363

theorem tailTrace_1241193 : CollatzResearch.WordTrace tailWord_1241193 prefixEnd_1241193 637328593996067560379363 := by
  unfold tailWord_1241193
  simp only [CollatzResearch.WordTrace]
  refine ⟨45270027792377214733008233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30180018528251476488672155 45270027792377214733008233)
  ·
    refine ⟨33952520844282911049756175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45270027792377214733008233 33952520844282911049756175)
    ·
      refine ⟨50928781266424366574634263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33952520844282911049756175 50928781266424366574634263)
      ·
        refine ⟨76393171899636549861951395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50928781266424366574634263 76393171899636549861951395)
        ·
          refine ⟨114589757849454824792927093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76393171899636549861951395 114589757849454824792927093)
          ·
            refine ⟨10742789798386389824336915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114589757849454824792927093 10742789798386389824336915)
            ·
              refine ⟨16114184697579584736505373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10742789798386389824336915 16114184697579584736505373)
              ·
                refine ⟨6042819261592344276189515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16114184697579584736505373 6042819261592344276189515)
                ·
                  refine ⟨9064228892388516414284273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042819261592344276189515 9064228892388516414284273)
                  ·
                    refine ⟨6798171669291387310713205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9064228892388516414284273 6798171669291387310713205)
                    ·
                      refine ⟨637328593996067560379363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6798171669291387310713205 637328593996067560379363)
                      ·
                        rfl

theorem cell23_1241193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_1241193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241193 prefixEnd_1241193 := by exact prefixLift 1241193
  have htrace : WordTrace (prefixWord ++ tailWord_1241193) baseStart_1241193 baseEnd_1241193 := by
    simpa [prefixWord, tailWord_1241193, baseEnd_1241193] using wordTrace_append hprefix tailTrace_1241193
  have hstable : (prefixWord ++ tailWord_1241193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241193).length < 2 ^ (prefixWord ++ tailWord_1241193).sum := by decide
  have hdescent : baseEnd_1241193 < baseStart_1241193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241220 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1241220 : Nat := 118140960795 + 1241220 * 2 ^ 59
def prefixEnd_1241220 : Nat := 4983230072969 + 3 ^ 40 * 1241220 * 2
def baseEnd_1241220 : Nat := 637342457973738954741739

theorem tailTrace_1241220 : CollatzResearch.WordTrace tailWord_1241220 prefixEnd_1241220 637342457973738954741739 := by
  unfold tailWord_1241220
  simp only [CollatzResearch.WordTrace]
  refine ⟨22635506281639699172120557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30180675042186265562827409 22635506281639699172120557)
  ·
    refine ⟨8488314855614887189545209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22635506281639699172120557 8488314855614887189545209)
    ·
      refine ⟨6366236141711165392158907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8488314855614887189545209 6366236141711165392158907)
      ·
        refine ⟨9549354212566748088238361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366236141711165392158907 9549354212566748088238361)
        ·
          refine ⟨7162015659425061066178771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9549354212566748088238361 7162015659425061066178771)
          ·
            refine ⟨10743023489137591599268157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162015659425061066178771 10743023489137591599268157)
            ·
              refine ⟨4028633808426596849725559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10743023489137591599268157 4028633808426596849725559)
              ·
                refine ⟨6042950712639895274588339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028633808426596849725559 6042950712639895274588339)
                ·
                  refine ⟨9064426068959842911882509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042950712639895274588339 9064426068959842911882509)
                  ·
                    refine ⟨3399159775859941091955941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9064426068959842911882509 3399159775859941091955941)
                    ·
                      refine ⟨637342457973738954741739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3399159775859941091955941 637342457973738954741739)
                      ·
                        rfl

theorem cell23_1241220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1241220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241220 prefixEnd_1241220 := by exact prefixLift 1241220
  have htrace : WordTrace (prefixWord ++ tailWord_1241220) baseStart_1241220 baseEnd_1241220 := by
    simpa [prefixWord, tailWord_1241220, baseEnd_1241220] using wordTrace_append hprefix tailTrace_1241220
  have hstable : (prefixWord ++ tailWord_1241220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241220).length < 2 ^ (prefixWord ++ tailWord_1241220).sum := by decide
  have hdescent : baseEnd_1241220 < baseStart_1241220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241233 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_1241233 : Nat := 118140960795 + 1241233 * 2 ^ 59
def prefixEnd_1241233 : Nat := 4983230072969 + 3 ^ 40 * 1241233 * 2
def baseEnd_1241233 : Nat := 637349133222247403879179

theorem tailTrace_1241233 : CollatzResearch.WordTrace tailWord_1241233 prefixEnd_1241233 637349133222247403879179 := by
  unfold tailWord_1241233
  simp only [CollatzResearch.WordTrace]
  refine ⟨45271486712232301564464353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30180991141488201042976235 45271486712232301564464353)
  ·
    refine ⟨33953615034174226173348265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45271486712232301564464353 33953615034174226173348265)
    ·
      refine ⟨25465211275630669630011199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33953615034174226173348265 25465211275630669630011199)
      ·
        refine ⟨38197816913446004445016799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25465211275630669630011199 38197816913446004445016799)
        ·
          refine ⟨57296725370169006667525199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38197816913446004445016799 57296725370169006667525199)
          ·
            refine ⟨85945088055253510001287799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57296725370169006667525199 85945088055253510001287799)
            ·
              refine ⟨128917632082880265001931699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85945088055253510001287799 128917632082880265001931699)
              ·
                refine ⟨193376448124320397502897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128917632082880265001931699 193376448124320397502897549)
                ·
                  refine ⟨72516168046620149063586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193376448124320397502897549 72516168046620149063586581)
                  ·
                    refine ⟨3399195377185319487355621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72516168046620149063586581 3399195377185319487355621)
                    ·
                      refine ⟨637349133222247403879179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3399195377185319487355621 637349133222247403879179)
                      ·
                        rfl

theorem cell23_1241233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_1241233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241233 prefixEnd_1241233 := by exact prefixLift 1241233
  have htrace : WordTrace (prefixWord ++ tailWord_1241233) baseStart_1241233 baseEnd_1241233 := by
    simpa [prefixWord, tailWord_1241233, baseEnd_1241233] using wordTrace_append hprefix tailTrace_1241233
  have hstable : (prefixWord ++ tailWord_1241233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241233).length < 2 ^ (prefixWord ++ tailWord_1241233).sum := by decide
  have hdescent : baseEnd_1241233 < baseStart_1241233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241238 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1241238 : Nat := 118140960795 + 1241238 * 2 ^ 59
def prefixEnd_1241238 : Nat := 4983230072969 + 3 ^ 40 * 1241238 * 2
def baseEnd_1241238 : Nat := 70816855625057764924073

theorem tailTrace_1241238 : CollatzResearch.WordTrace tailWord_1241238 prefixEnd_1241238 70816855625057764924073 := by
  unfold tailWord_1241238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829479317325886713649773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30181112718142791612264245 2829479317325886713649773)
  ·
    refine ⟨1061054743997207517618665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2829479317325886713649773 1061054743997207517618665)
    ·
      refine ⟨795791057997905638213999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1061054743997207517618665 795791057997905638213999)
      ·
        refine ⟨1193686586996858457320999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795791057997905638213999 1193686586996858457320999)
        ·
          refine ⟨1790529880495287685981499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193686586996858457320999 1790529880495287685981499)
          ·
            refine ⟨2685794820742931528972249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790529880495287685981499 2685794820742931528972249)
            ·
              refine ⟨2014346115557198646729187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2685794820742931528972249 2014346115557198646729187)
              ·
                refine ⟨3021519173335797970093781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014346115557198646729187 3021519173335797970093781)
                ·
                  refine ⟨70816855625057764924073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3021519173335797970093781 70816855625057764924073)
                  ·
                    rfl

theorem cell23_1241238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1241238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241238 prefixEnd_1241238 := by exact prefixLift 1241238
  have htrace : WordTrace (prefixWord ++ tailWord_1241238) baseStart_1241238 baseEnd_1241238 := by
    simpa [prefixWord, tailWord_1241238, baseEnd_1241238] using wordTrace_append hprefix tailTrace_1241238
  have hstable : (prefixWord ++ tailWord_1241238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241238).length < 2 ^ (prefixWord ++ tailWord_1241238).sum := by decide
  have hdescent : baseEnd_1241238 < baseStart_1241238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241247 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 3, 4]
def baseStart_1241247 : Nat := 118140960795 + 1241247 * 2 ^ 59
def prefixEnd_1241247 : Nat := 4983230072969 + 3 ^ 40 * 1241247 * 2
def baseEnd_1241247 : Nat := 212452107317136783034705

theorem tailTrace_1241247 : CollatzResearch.WordTrace tailWord_1241247 prefixEnd_1241247 212452107317136783034705 := by
  unfold tailWord_1241247
  simp only [CollatzResearch.WordTrace]
  refine ⟨45271997334181581955473995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30181331556121054636982663 45271997334181581955473995)
  ·
    refine ⟨67907996001272372933210993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45271997334181581955473995 67907996001272372933210993)
    ·
      refine ⟨50930997000954279699908245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67907996001272372933210993 50930997000954279699908245)
      ·
        refine ⟨2387390484419731860933199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50930997000954279699908245 2387390484419731860933199)
        ·
          refine ⟨3581085726629597791399799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2387390484419731860933199 3581085726629597791399799)
          ·
            refine ⟨5371628589944396687099699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581085726629597791399799 5371628589944396687099699)
            ·
              refine ⟨8057442884916595030649549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371628589944396687099699 8057442884916595030649549)
              ·
                refine ⟨3021541081843723136493581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8057442884916595030649549 3021541081843723136493581)
                ·
                  refine ⟨1133077905691396176185093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3021541081843723136493581 1133077905691396176185093)
                  ·
                    refine ⟨212452107317136783034705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133077905691396176185093 212452107317136783034705)
                    ·
                      rfl

theorem cell23_1241247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_1241247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241247 prefixEnd_1241247 := by exact prefixLift 1241247
  have htrace : WordTrace (prefixWord ++ tailWord_1241247) baseStart_1241247 baseEnd_1241247 := by
    simpa [prefixWord, tailWord_1241247, baseEnd_1241247] using wordTrace_append hprefix tailTrace_1241247
  have hstable : (prefixWord ++ tailWord_1241247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241247).length < 2 ^ (prefixWord ++ tailWord_1241247).sum := by decide
  have hdescent : baseEnd_1241247 < baseStart_1241247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241263 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_1241263 : Nat := 118140960795 + 1241263 * 2 ^ 59
def prefixEnd_1241263 : Nat := 4983230072969 + 3 ^ 40 * 1241263 * 2
def baseEnd_1241263 : Nat := 637364537641882286504041

theorem tailTrace_1241263 : CollatzResearch.WordTrace tailWord_1241263 prefixEnd_1241263 637364537641882286504041 := by
  unfold tailWord_1241263
  simp only [CollatzResearch.WordTrace]
  refine ⟨45272580902123616688056443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30181720601415744458704295 45272580902123616688056443)
  ·
    refine ⟨67908871353185425032084665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45272580902123616688056443 67908871353185425032084665)
    ·
      refine ⟨50931653514889068774063499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67908871353185425032084665 50931653514889068774063499)
      ·
        refine ⟨76397480272333603161095249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50931653514889068774063499 76397480272333603161095249)
        ·
          refine ⟨57298110204250202370821437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76397480272333603161095249 57298110204250202370821437)
          ·
            refine ⟨21486791326593825889058039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57298110204250202370821437 21486791326593825889058039)
            ·
              refine ⟨32230186989890738833587059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21486791326593825889058039 32230186989890738833587059)
              ·
                refine ⟨48345280484836108250380589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32230186989890738833587059 48345280484836108250380589)
                ·
                  refine ⟨18129480181813540593892721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48345280484836108250380589 18129480181813540593892721)
                  ·
                    refine ⟨13597110136360155445419541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18129480181813540593892721 13597110136360155445419541)
                    ·
                      refine ⟨637364537641882286504041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13597110136360155445419541 637364537641882286504041)
                      ·
                        rfl

theorem cell23_1241263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_1241263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241263 prefixEnd_1241263 := by exact prefixLift 1241263
  have htrace : WordTrace (prefixWord ++ tailWord_1241263) baseStart_1241263 baseEnd_1241263 := by
    simpa [prefixWord, tailWord_1241263, baseEnd_1241263] using wordTrace_append hprefix tailTrace_1241263
  have hstable : (prefixWord ++ tailWord_1241263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241263).length < 2 ^ (prefixWord ++ tailWord_1241263).sum := by decide
  have hdescent : baseEnd_1241263 < baseStart_1241263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241283 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1241283 : Nat := 118140960795 + 1241283 * 2 ^ 59
def prefixEnd_1241283 : Nat := 4983230072969 + 3 ^ 40 * 1241283 * 2
def baseEnd_1241283 : Nat := 637374807254972208253949

theorem tailTrace_1241283 : CollatzResearch.WordTrace tailWord_1241283 prefixEnd_1241283 637374807254972208253949 := by
  unfold tailWord_1241283
  simp only [CollatzResearch.WordTrace]
  refine ⟨45273310362051160103784503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30182206908034106735856335 45273310362051160103784503)
  ·
    refine ⟨67909965543076740155676755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45273310362051160103784503 67909965543076740155676755)
    ·
      refine ⟨101864948314615110233515133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67909965543076740155676755 101864948314615110233515133)
      ·
        refine ⟨38199355617980666337568175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101864948314615110233515133 38199355617980666337568175)
        ·
          refine ⟨57299033426970999506352263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38199355617980666337568175 57299033426970999506352263)
          ·
            refine ⟨85948550140456499259528395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57299033426970999506352263 85948550140456499259528395)
            ·
              refine ⟨128922825210684748889292593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85948550140456499259528395 128922825210684748889292593)
              ·
                refine ⟨96692118908013561666969445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128922825210684748889292593 96692118908013561666969445)
                ·
                  refine ⟨18129772295252542812556771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96692118908013561666969445 18129772295252542812556771)
                  ·
                    refine ⟨27194658442878814218835157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18129772295252542812556771 27194658442878814218835157)
                    ·
                      refine ⟨637374807254972208253949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27194658442878814218835157 637374807254972208253949)
                      ·
                        rfl

theorem cell23_1241283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1241283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241283 prefixEnd_1241283 := by exact prefixLift 1241283
  have htrace : WordTrace (prefixWord ++ tailWord_1241283) baseStart_1241283 baseEnd_1241283 := by
    simpa [prefixWord, tailWord_1241283, baseEnd_1241283] using wordTrace_append hprefix tailTrace_1241283
  have hstable : (prefixWord ++ tailWord_1241283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241283).length < 2 ^ (prefixWord ++ tailWord_1241283).sum := by decide
  have hdescent : baseEnd_1241283 < baseStart_1241283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241297 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_1241297 : Nat := 118140960795 + 1241297 * 2 ^ 59
def prefixEnd_1241297 : Nat := 4983230072969 + 3 ^ 40 * 1241297 * 2
def baseEnd_1241297 : Nat := 637381995984135153478885

theorem tailTrace_1241297 : CollatzResearch.WordTrace tailWord_1241297 prefixEnd_1241297 637381995984135153478885 := by
  unfold tailWord_1241297
  simp only [CollatzResearch.WordTrace]
  refine ⟨45273820984000440494794145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30182547322666960329862763 45273820984000440494794145)
  ·
    refine ⟨33955365738000330371095609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45273820984000440494794145 33955365738000330371095609)
    ·
      refine ⟨25466524303500247778321707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33955365738000330371095609 25466524303500247778321707)
      ·
        refine ⟨38199786455250371667482561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25466524303500247778321707 38199786455250371667482561)
        ·
          refine ⟨28649839841437778750611921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38199786455250371667482561 28649839841437778750611921)
          ·
            refine ⟨21487379881078334062958941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28649839841437778750611921 21487379881078334062958941)
            ·
              refine ⟨8057767455404375273609603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21487379881078334062958941 8057767455404375273609603)
              ·
                refine ⟨12086651183106562910414405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057767455404375273609603 12086651183106562910414405)
                ·
                  refine ⟨2266247096832480545702701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12086651183106562910414405 2266247096832480545702701)
                  ·
                    refine ⟨849842661312180204638513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2266247096832480545702701 849842661312180204638513)
                    ·
                      refine ⟨637381995984135153478885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 849842661312180204638513 637381995984135153478885)
                      ·
                        rfl

theorem cell23_1241297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_1241297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241297 prefixEnd_1241297 := by exact prefixLift 1241297
  have htrace : WordTrace (prefixWord ++ tailWord_1241297) baseStart_1241297 baseEnd_1241297 := by
    simpa [prefixWord, tailWord_1241297, baseEnd_1241297] using wordTrace_append hprefix tailTrace_1241297
  have hstable : (prefixWord ++ tailWord_1241297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241297).length < 2 ^ (prefixWord ++ tailWord_1241297).sum := by decide
  have hdescent : baseEnd_1241297 < baseStart_1241297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241304 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1241304 : Nat := 118140960795 + 1241304 * 2 ^ 59
def prefixEnd_1241304 : Nat := 4983230072969 + 3 ^ 40 * 1241304 * 2
def baseEnd_1241304 : Nat := 637385590348716626091353

theorem tailTrace_1241304 : CollatzResearch.WordTrace tailWord_1241304 prefixEnd_1241304 637385590348716626091353 := by
  unfold tailWord_1241304
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637038147487540345149483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30182717529983387126865977 22637038147487540345149483)
  ·
    refine ⟨33955557221231310517724225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22637038147487540345149483 33955557221231310517724225)
    ·
      refine ⟨25466667915923482888293169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33955557221231310517724225 25466667915923482888293169)
      ·
        refine ⟨19100000936942612166219877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25466667915923482888293169 19100000936942612166219877)
        ·
          refine ⟨3581250175676739781166227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19100000936942612166219877 3581250175676739781166227)
          ·
            refine ⟨5371875263515109671749341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581250175676739781166227 5371875263515109671749341)
            ·
              refine ⟨2014453223818166126906003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5371875263515109671749341 2014453223818166126906003)
              ·
                refine ⟨3021679835727249190359005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014453223818166126906003 3021679835727249190359005)
                ·
                  refine ⟨1133129938397718446384627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3021679835727249190359005 1133129938397718446384627)
                  ·
                    refine ⟨1699694907596577669576941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133129938397718446384627 1699694907596577669576941)
                    ·
                      refine ⟨637385590348716626091353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699694907596577669576941 637385590348716626091353)
                      ·
                        rfl

theorem cell23_1241304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1241304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241304 prefixEnd_1241304 := by exact prefixLift 1241304
  have htrace : WordTrace (prefixWord ++ tailWord_1241304) baseStart_1241304 baseEnd_1241304 := by
    simpa [prefixWord, tailWord_1241304, baseEnd_1241304] using wordTrace_append hprefix tailTrace_1241304
  have hstable : (prefixWord ++ tailWord_1241304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241304).length < 2 ^ (prefixWord ++ tailWord_1241304).sum := by decide
  have hdescent : baseEnd_1241304 < baseStart_1241304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241327 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_1241327 : Nat := 118140960795 + 1241327 * 2 ^ 59
def prefixEnd_1241327 : Nat := 4983230072969 + 3 ^ 40 * 1241327 * 2
def baseEnd_1241327 : Nat := 637397400403770036103747

theorem tailTrace_1241327 : CollatzResearch.WordTrace tailWord_1241327 prefixEnd_1241327 637397400403770036103747 := by
  unfold tailWord_1241327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45274915173891755618386235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30183276782594503745590823 45274915173891755618386235)
  ·
    refine ⟨67912372760837633427579353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45274915173891755618386235 67912372760837633427579353)
    ·
      refine ⟨50934279570628225070684515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67912372760837633427579353 50934279570628225070684515)
      ·
        refine ⟨76401419355942337606026773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50934279570628225070684515 76401419355942337606026773)
        ·
          refine ⟨3581316532309797075282505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76401419355942337606026773 3581316532309797075282505)
          ·
            refine ⟨2685987399232347806461879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3581316532309797075282505 2685987399232347806461879)
            ·
              refine ⟨4028981098848521709692819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2685987399232347806461879 4028981098848521709692819)
              ·
                refine ⟨6043471648272782564539229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028981098848521709692819 6043471648272782564539229)
                ·
                  refine ⟨2266301868102293461702211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6043471648272782564539229 2266301868102293461702211)
                  ·
                    refine ⟨3399452802153440192553317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266301868102293461702211 3399452802153440192553317)
                    ·
                      refine ⟨637397400403770036103747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3399452802153440192553317 637397400403770036103747)
                      ·
                        rfl

theorem cell23_1241327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_1241327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241327 prefixEnd_1241327 := by exact prefixLift 1241327
  have htrace : WordTrace (prefixWord ++ tailWord_1241327) baseStart_1241327 baseEnd_1241327 := by
    simpa [prefixWord, tailWord_1241327, baseEnd_1241327] using wordTrace_append hprefix tailTrace_1241327
  have hstable : (prefixWord ++ tailWord_1241327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241327).length < 2 ^ (prefixWord ++ tailWord_1241327).sum := by decide
  have hdescent : baseEnd_1241327 < baseStart_1241327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241367 : List Nat := [1, 1, 3, 4, 1, 4, 1, 8]
def baseStart_1241367 : Nat := 118140960795 + 1241367 * 2 ^ 59
def prefixEnd_1241367 : Nat := 4983230072969 + 3 ^ 40 * 1241367 * 2
def baseEnd_1241367 : Nat := 23608071838146291837169

theorem tailTrace_1241367 : CollatzResearch.WordTrace tailWord_1241367 prefixEnd_1241367 23608071838146291837169 := by
  unfold tailWord_1241367
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276374093746842449842355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30184249395831228299894903 45276374093746842449842355)
  ·
    refine ⟨67914561140620263674763533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45276374093746842449842355 67914561140620263674763533)
    ·
      refine ⟨25467960427732598878036325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67914561140620263674763533 25467960427732598878036325)
      ·
        refine ⟨4775242580199862289631811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25467960427732598878036325 4775242580199862289631811)
        ·
          refine ⟨7162863870299793434447717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775242580199862289631811 7162863870299793434447717)
          ·
            refine ⟨1343036975681211268958947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7162863870299793434447717 1343036975681211268958947)
            ·
              refine ⟨2014555463521816903438421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343036975681211268958947 2014555463521816903438421)
              ·
                refine ⟨23608071838146291837169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2014555463521816903438421 23608071838146291837169)
                ·
                  rfl

theorem cell23_1241367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 8].length) (baseStart_1241367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241367 prefixEnd_1241367 := by exact prefixLift 1241367
  have htrace : WordTrace (prefixWord ++ tailWord_1241367) baseStart_1241367 baseEnd_1241367 := by
    simpa [prefixWord, tailWord_1241367, baseEnd_1241367] using wordTrace_append hprefix tailTrace_1241367
  have hstable : (prefixWord ++ tailWord_1241367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241367).length < 2 ^ (prefixWord ++ tailWord_1241367).sum := by decide
  have hdescent : baseEnd_1241367 < baseStart_1241367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241377 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1241377 : Nat := 118140960795 + 1241377 * 2 ^ 59
def prefixEnd_1241377 : Nat := 4983230072969 + 3 ^ 40 * 1241377 * 2
def baseEnd_1241377 : Nat := 637423074436494840478517

theorem tailTrace_1241377 : CollatzResearch.WordTrace tailWord_1241377 prefixEnd_1241377 637423074436494840478517 := by
  unfold tailWord_1241377
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276738823710614157706385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30184492549140409438470923 45276738823710614157706385)
  ·
    refine ⟨33957554117782960618279789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45276738823710614157706385 33957554117782960618279789)
    ·
      refine ⟨12734082794168610231854921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33957554117782960618279789 12734082794168610231854921)
      ·
        refine ⟨9550562095626457673891191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12734082794168610231854921 9550562095626457673891191)
        ·
          refine ⟨14325843143439686510836787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9550562095626457673891191 14325843143439686510836787)
          ·
            refine ⟨21488764715159529766255181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14325843143439686510836787 21488764715159529766255181)
            ·
              refine ⟨8058286768184823662345693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21488764715159529766255181 8058286768184823662345693)
              ·
                refine ⟨3021857538069308873379635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8058286768184823662345693 3021857538069308873379635)
                ·
                  refine ⟨4532786307103963310069453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021857538069308873379635 4532786307103963310069453)
                  ·
                    refine ⟨1699794865163986241276045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4532786307103963310069453 1699794865163986241276045)
                    ·
                      refine ⟨637423074436494840478517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699794865163986241276045 637423074436494840478517)
                      ·
                        rfl

theorem cell23_1241377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1241377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241377 prefixEnd_1241377 := by exact prefixLift 1241377
  have htrace : WordTrace (prefixWord ++ tailWord_1241377) baseStart_1241377 baseEnd_1241377 := by
    simpa [prefixWord, tailWord_1241377, baseEnd_1241377] using wordTrace_append hprefix tailTrace_1241377
  have hstable : (prefixWord ++ tailWord_1241377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241377).length < 2 ^ (prefixWord ++ tailWord_1241377).sum := by decide
  have hdescent : baseEnd_1241377 < baseStart_1241377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241384 : List Nat := [2, 1, 5, 1, 3, 1, 3, 7]
def baseStart_1241384 : Nat := 118140960795 + 1241384 * 2 ^ 59
def prefixEnd_1241384 : Nat := 4983230072969 + 3 ^ 40 * 1241384 * 2
def baseEnd_1241384 : Nat := 23608395140780604188555

theorem tailTrace_1241384 : CollatzResearch.WordTrace tailWord_1241384 prefixEnd_1241384 23608395140780604188555 := by
  unfold tailWord_1241384
  simp only [CollatzResearch.WordTrace]
  refine ⟨22638497067342627176605603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30184662756456836235474137 22638497067342627176605603)
  ·
    refine ⟨33957745601013940764908405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22638497067342627176605603 33957745601013940764908405)
    ·
      refine ⟨3183538650095056946710163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33957745601013940764908405 3183538650095056946710163)
      ·
        refine ⟨4775307975142585420065245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183538650095056946710163 4775307975142585420065245)
        ·
          refine ⟨1790740490678469532524467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4775307975142585420065245 1790740490678469532524467)
          ·
            refine ⟨2686110736017704298786701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790740490678469532524467 2686110736017704298786701)
            ·
              refine ⟨1007291526006639112045013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686110736017704298786701 1007291526006639112045013)
              ·
                refine ⟨23608395140780604188555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1007291526006639112045013 23608395140780604188555)
                ·
                  rfl

theorem cell23_1241384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 7].length) (baseStart_1241384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241384 prefixEnd_1241384 := by exact prefixLift 1241384
  have htrace : WordTrace (prefixWord ++ tailWord_1241384) baseStart_1241384 baseEnd_1241384 := by
    simpa [prefixWord, tailWord_1241384, baseEnd_1241384] using wordTrace_append hprefix tailTrace_1241384
  have hstable : (prefixWord ++ tailWord_1241384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241384).length < 2 ^ (prefixWord ++ tailWord_1241384).sum := by decide
  have hdescent : baseEnd_1241384 < baseStart_1241384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241428 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_1241428 : Nat := 118140960795 + 1241428 * 2 ^ 59
def prefixEnd_1241428 : Nat := 4983230072969 + 3 ^ 40 * 1241428 * 2
def baseEnd_1241428 : Nat := 637449261949874140940783

theorem tailTrace_1241428 : CollatzResearch.WordTrace tailWord_1241428 prefixEnd_1241428 637449261949874140940783 := by
  unfold tailWord_1241428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22639299473262924933906469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30185732631017233245208625 22639299473262924933906469)
  ·
    refine ⟨4244868651236798425107463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22639299473262924933906469 4244868651236798425107463)
    ·
      refine ⟨6367302976855197637661195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244868651236798425107463 6367302976855197637661195)
      ·
        refine ⟨9550954465282796456491793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6367302976855197637661195 9550954465282796456491793)
        ·
          refine ⟨7163215848962097342368845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9550954465282796456491793 7163215848962097342368845)
          ·
            refine ⟨2686205943360786503388317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7163215848962097342368845 2686205943360786503388317)
            ·
              refine ⟨1007327228760294938770619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686205943360786503388317 1007327228760294938770619)
              ·
                refine ⟨1510990843140442408155929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007327228760294938770619 1510990843140442408155929)
                ·
                  refine ⟨1133243132355331806116947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510990843140442408155929 1133243132355331806116947)
                  ·
                    refine ⟨1699864698532997709175421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133243132355331806116947 1699864698532997709175421)
                    ·
                      refine ⟨637449261949874140940783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1699864698532997709175421 637449261949874140940783)
                      ·
                        rfl

theorem cell23_1241428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_1241428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1241428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1241428 prefixEnd_1241428 := by exact prefixLift 1241428
  have htrace : WordTrace (prefixWord ++ tailWord_1241428) baseStart_1241428 baseEnd_1241428 := by
    simpa [prefixWord, tailWord_1241428, baseEnd_1241428] using wordTrace_append hprefix tailTrace_1241428
  have hstable : (prefixWord ++ tailWord_1241428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241428).length < 2 ^ (prefixWord ++ tailWord_1241428).sum := by decide
  have hdescent : baseEnd_1241428 < baseStart_1241428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
