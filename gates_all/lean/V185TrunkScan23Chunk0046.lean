import V185TrunkScan23Chunk0045

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_272901 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_272901 : Nat := 118140960795 + 272901 * 2 ^ 59
def prefixEnd_272901 : Nat := 4983230072969 + 3 ^ 40 * 272901 * 2
def baseEnd_272901 : Nat := 140129384092742007282457

theorem tailTrace_272901 : CollatzResearch.WordTrace tailWord_272901 prefixEnd_272901 140129384092742007282457 := by
  unfold tailWord_272901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953517184333759625274557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6635678122889173083516371 9953517184333759625274557)
  ·
    refine ⟨3732568944125159859477959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9953517184333759625274557 3732568944125159859477959)
    ·
      refine ⟨5598853416187739789216939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732568944125159859477959 5598853416187739789216939)
      ·
        refine ⟨8398280124281609683825409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598853416187739789216939 8398280124281609683825409)
        ·
          refine ⟨6298710093211207262869057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8398280124281609683825409 6298710093211207262869057)
          ·
            refine ⟨4724032569908405447151793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6298710093211207262869057 4724032569908405447151793)
            ·
              refine ⟨3543024427431304085363845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4724032569908405447151793 3543024427431304085363845)
              ·
                refine ⟨664317080143369516005721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3543024427431304085363845 664317080143369516005721)
                ·
                  refine ⟨498237810107527137004291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664317080143369516005721 498237810107527137004291)
                  ·
                    refine ⟨747356715161290705506437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 498237810107527137004291 747356715161290705506437)
                    ·
                      refine ⟨140129384092742007282457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 747356715161290705506437 140129384092742007282457)
                      ·
                        rfl

theorem cell23_272901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_272901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272901 prefixEnd_272901 := by exact prefixLift 272901
  have htrace : WordTrace (prefixWord ++ tailWord_272901) baseStart_272901 baseEnd_272901 := by
    simpa [prefixWord, tailWord_272901, baseEnd_272901] using wordTrace_append hprefix tailTrace_272901
  have hstable : (prefixWord ++ tailWord_272901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272901).length < 2 ^ (prefixWord ++ tailWord_272901).sum := by decide
  have hdescent : baseEnd_272901 < baseStart_272901 := by decide
  rcases family_descends (prefixWord ++ tailWord_272901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272902 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_272902 : Nat := 118140960795 + 272902 * 2 ^ 59
def prefixEnd_272902 : Nat := 4983230072969 + 3 ^ 40 * 272902 * 2
def baseEnd_272902 : Nat := 15569988619266278152217

theorem tailTrace_272902 : CollatzResearch.WordTrace tailWord_272902 prefixEnd_272902 15569988619266278152217 := by
  unfold tailWord_272902
  simp only [CollatzResearch.WordTrace]
  refine ⟨311048551791566774876905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6635702438220091197373973 311048551791566774876905)
  ·
    refine ⟨233286413843675081157679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311048551791566774876905 233286413843675081157679)
    ·
      refine ⟨349929620765512621736519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233286413843675081157679 349929620765512621736519)
      ·
        refine ⟨524894431148268932604779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349929620765512621736519 524894431148268932604779)
        ·
          refine ⟨787341646722403398907169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524894431148268932604779 787341646722403398907169)
          ·
            refine ⟨590506235041802549180377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787341646722403398907169 590506235041802549180377)
            ·
              refine ⟨442879676281351911885283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590506235041802549180377 442879676281351911885283)
              ·
                refine ⟨664319514422027867827925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442879676281351911885283 664319514422027867827925)
                ·
                  refine ⟨15569988619266278152217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 664319514422027867827925 15569988619266278152217)
                  ·
                    rfl

theorem cell23_272902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_272902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272902 prefixEnd_272902 := by exact prefixLift 272902
  have htrace : WordTrace (prefixWord ++ tailWord_272902) baseStart_272902 baseEnd_272902 := by
    simpa [prefixWord, tailWord_272902, baseEnd_272902] using wordTrace_append hprefix tailTrace_272902
  have hstable : (prefixWord ++ tailWord_272902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272902).length < 2 ^ (prefixWord ++ tailWord_272902).sum := by decide
  have hdescent : baseEnd_272902 < baseStart_272902 := by decide
  rcases family_descends (prefixWord ++ tailWord_272902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272911 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 3, 4]
def baseStart_272911 : Nat := 118140960795 + 272911 * 2 ^ 59
def prefixEnd_272911 : Nat := 4983230072969 + 3 ^ 40 * 272911 * 2
def baseEnd_272911 : Nat := 46711506299762322719137

theorem tailTrace_272911 : CollatzResearch.WordTrace tailWord_272911 prefixEnd_272911 46711506299762322719137 := by
  unfold tailWord_272911
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953881914297531333138587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6635921276198354222092391 9953881914297531333138587)
  ·
    refine ⟨14930822871446296999707881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9953881914297531333138587 14930822871446296999707881)
    ·
      refine ⟨11198117153584722749780911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14930822871446296999707881 11198117153584722749780911)
      ·
        refine ⟨16797175730377084124671367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11198117153584722749780911 16797175730377084124671367)
        ·
          refine ⟨25195763595565626187007051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16797175730377084124671367 25195763595565626187007051)
          ·
            refine ⟨37793645393348439280510577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25195763595565626187007051 37793645393348439280510577)
            ·
              refine ⟨28345234045011329460382933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37793645393348439280510577 28345234045011329460382933)
              ·
                refine ⟨664341422929953034227725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28345234045011329460382933 664341422929953034227725)
                ·
                  refine ⟨249128033598732387835397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 664341422929953034227725 249128033598732387835397)
                  ·
                    refine ⟨46711506299762322719137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249128033598732387835397 46711506299762322719137)
                    ·
                      rfl

theorem cell23_272911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_272911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272911 prefixEnd_272911 := by exact prefixLift 272911
  have htrace : WordTrace (prefixWord ++ tailWord_272911) baseStart_272911 baseEnd_272911 := by
    simpa [prefixWord, tailWord_272911, baseEnd_272911] using wordTrace_append hprefix tailTrace_272911
  have hstable : (prefixWord ++ tailWord_272911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272911).length < 2 ^ (prefixWord ++ tailWord_272911).sum := by decide
  have hdescent : baseEnd_272911 < baseStart_272911 := by decide
  rcases family_descends (prefixWord ++ tailWord_272911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272921 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_272921 : Nat := 118140960795 + 272921 * 2 ^ 59
def prefixEnd_272921 : Nat := 4983230072969 + 3 ^ 40 * 272921 * 2
def baseEnd_272921 : Nat := 140139653705831929032365

theorem tailTrace_272921 : CollatzResearch.WordTrace tailWord_272921 prefixEnd_272921 140139653705831929032365 := by
  unfold tailWord_272921
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954246644261303041002617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6636164429507535360668411 9954246644261303041002617)
  ·
    refine ⟨7465684983195977280751963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9954246644261303041002617 7465684983195977280751963)
    ·
      refine ⟨11198527474793965921127945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465684983195977280751963 11198527474793965921127945)
      ·
        refine ⟨8398895606095474440845959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11198527474793965921127945 8398895606095474440845959)
        ·
          refine ⟨12598343409143211661268939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398895606095474440845959 12598343409143211661268939)
          ·
            refine ⟨18897515113714817491903409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598343409143211661268939 18897515113714817491903409)
            ·
              refine ⟨14173136335286113118927557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18897515113714817491903409 14173136335286113118927557)
              ·
                refine ⟨2657463062866146209798917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14173136335286113118927557 2657463062866146209798917)
                ·
                  refine ⟨498274324287402414337297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2657463062866146209798917 498274324287402414337297)
                  ·
                    refine ⟨373705743215551810752973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 498274324287402414337297 373705743215551810752973)
                    ·
                      refine ⟨140139653705831929032365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 373705743215551810752973 140139653705831929032365)
                      ·
                        rfl

theorem cell23_272921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_272921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272921 prefixEnd_272921 := by exact prefixLift 272921
  have htrace : WordTrace (prefixWord ++ tailWord_272921) baseStart_272921 baseEnd_272921 := by
    simpa [prefixWord, tailWord_272921, baseEnd_272921] using wordTrace_append hprefix tailTrace_272921
  have hstable : (prefixWord ++ tailWord_272921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272921).length < 2 ^ (prefixWord ++ tailWord_272921).sum := by decide
  have hdescent : baseEnd_272921 < baseStart_272921 := by decide
  rcases family_descends (prefixWord ++ tailWord_272921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272938 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_272938 : Nat := 118140960795 + 272938 * 2 ^ 59
def prefixEnd_272938 : Nat := 4983230072969 + 3 ^ 40 * 272938 * 2
def baseEnd_272938 : Nat := 140148382876958362519787

theorem tailTrace_272938 : CollatzResearch.WordTrace tailWord_272938 prefixEnd_272938 140148382876958362519787 := by
  unfold tailWord_272938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488716671299928736092867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6636577790133143296247645 2488716671299928736092867)
  ·
    refine ⟨3733075006949893104139301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2488716671299928736092867 3733075006949893104139301)
    ·
      refine ⟨699951563803104957026119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3733075006949893104139301 699951563803104957026119)
      ·
        refine ⟨1049927345704657435539179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699951563803104957026119 1049927345704657435539179)
        ·
          refine ⟨1574891018556986153308769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049927345704657435539179 1574891018556986153308769)
          ·
            refine ⟨1181168263917739614981577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574891018556986153308769 1181168263917739614981577)
            ·
              refine ⟨885876197938304711236183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181168263917739614981577 885876197938304711236183)
              ·
                refine ⟨1328814296907457066854275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885876197938304711236183 1328814296907457066854275)
                ·
                  refine ⟨1993221445361185600281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328814296907457066854275 1993221445361185600281413)
                  ·
                    refine ⟨373729021005222300052765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993221445361185600281413 373729021005222300052765)
                    ·
                      refine ⟨140148382876958362519787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 373729021005222300052765 140148382876958362519787)
                      ·
                        rfl

theorem cell23_272938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_272938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272938 prefixEnd_272938 := by exact prefixLift 272938
  have htrace : WordTrace (prefixWord ++ tailWord_272938) baseStart_272938 baseEnd_272938 := by
    simpa [prefixWord, tailWord_272938, baseEnd_272938] using wordTrace_append hprefix tailTrace_272938
  have hstable : (prefixWord ++ tailWord_272938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272938).length < 2 ^ (prefixWord ++ tailWord_272938).sum := by decide
  have hdescent : baseEnd_272938 < baseStart_272938 := by decide
  rcases family_descends (prefixWord ++ tailWord_272938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272945 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 1, 4]
def baseStart_272945 : Nat := 118140960795 + 272945 * 2 ^ 59
def prefixEnd_272945 : Nat := 4983230072969 + 3 ^ 40 * 272945 * 2
def baseEnd_272945 : Nat := 46717325747179945044085

theorem tailTrace_272945 : CollatzResearch.WordTrace tailWord_272945 prefixEnd_272945 46717325747179945044085 := by
  unfold tailWord_272945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955121996174355139876289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6636747997449570093250859 9955121996174355139876289)
  ·
    refine ⟨7466341497130766354907217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9955121996174355139876289 7466341497130766354907217)
    ·
      refine ⟨5599756122848074766180413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7466341497130766354907217 5599756122848074766180413)
      ·
        refine ⟨2099908546068028037317655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5599756122848074766180413 2099908546068028037317655)
        ·
          refine ⟨3149862819102042055976483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099908546068028037317655 3149862819102042055976483)
          ·
            refine ⟨4724794228653063083964725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149862819102042055976483 4724794228653063083964725)
            ·
              refine ⟨442949458936224664121693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4724794228653063083964725 442949458936224664121693)
              ·
                refine ⟨166106047101084249045635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442949458936224664121693 166106047101084249045635)
                ·
                  refine ⟨249159070651626373568453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166106047101084249045635 249159070651626373568453)
                  ·
                    refine ⟨46717325747179945044085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249159070651626373568453 46717325747179945044085)
                    ·
                      rfl

theorem cell23_272945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_272945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272945 prefixEnd_272945 := by exact prefixLift 272945
  have htrace : WordTrace (prefixWord ++ tailWord_272945) baseStart_272945 baseEnd_272945 := by
    simpa [prefixWord, tailWord_272945, baseEnd_272945] using wordTrace_append hprefix tailTrace_272945
  have hstable : (prefixWord ++ tailWord_272945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272945).length < 2 ^ (prefixWord ++ tailWord_272945).sum := by decide
  have hdescent : baseEnd_272945 < baseStart_272945 := by decide
  rcases family_descends (prefixWord ++ tailWord_272945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272995 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 2, 3, 2]
def baseStart_272995 : Nat := 118140960795 + 272995 * 2 ^ 59
def prefixEnd_272995 : Nat := 4983230072969 + 3 ^ 40 * 272995 * 2
def baseEnd_272995 : Nat := 140177651274264639507025

theorem tailTrace_272995 : CollatzResearch.WordTrace tailWord_272995 prefixEnd_272995 140177651274264639507025 := by
  unfold tailWord_272995
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956945645993213679196439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637963763995475786130959 9956945645993213679196439)
  ·
    refine ⟨14935418468989820518794659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9956945645993213679196439 14935418468989820518794659)
    ·
      refine ⟨22403127703484730778191989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14935418468989820518794659 22403127703484730778191989)
      ·
        refine ⟨2100293222201693510455499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22403127703484730778191989 2100293222201693510455499)
        ·
          refine ⟨3150439833302540265683249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100293222201693510455499 3150439833302540265683249)
          ·
            refine ⟨2362829874976905199262437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3150439833302540265683249 2362829874976905199262437)
            ·
              refine ⟨443030601558169724861707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2362829874976905199262437 443030601558169724861707)
              ·
                refine ⟨664545902337254587292561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443030601558169724861707 664545902337254587292561)
                ·
                  refine ⟨498409426752940940469421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664545902337254587292561 498409426752940940469421)
                  ·
                    refine ⟨186903535032352852676033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498409426752940940469421 186903535032352852676033)
                    ·
                      refine ⟨140177651274264639507025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186903535032352852676033 140177651274264639507025)
                      ·
                        rfl

theorem cell23_272995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_272995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272995 prefixEnd_272995 := by exact prefixLift 272995
  have htrace : WordTrace (prefixWord ++ tailWord_272995) baseStart_272995 baseEnd_272995 := by
    simpa [prefixWord, tailWord_272995, baseEnd_272995] using wordTrace_append hprefix tailTrace_272995
  have hstable : (prefixWord ++ tailWord_272995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272995).length < 2 ^ (prefixWord ++ tailWord_272995).sum := by decide
  have hdescent : baseEnd_272995 < baseStart_272995 := by decide
  rcases family_descends (prefixWord ++ tailWord_272995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273002 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_273002 : Nat := 118140960795 + 273002 * 2 ^ 59
def prefixEnd_273002 : Nat := 4983230072969 + 3 ^ 40 * 273002 * 2
def baseEnd_273002 : Nat := 140181245638846112119493

theorem tailTrace_273002 : CollatzResearch.WordTrace tailWord_273002 prefixEnd_273002 140181245638846112119493 := by
  unfold tailWord_273002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489300239241963468675315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6638133971311902583134173 2489300239241963468675315)
  ·
    refine ⟨3733950358862945203012973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2489300239241963468675315 3733950358862945203012973)
    ·
      refine ⟨1400231384573604451129865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3733950358862945203012973 1400231384573604451129865)
      ·
        refine ⟨1050173538430203338347399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1400231384573604451129865 1050173538430203338347399)
        ·
          refine ⟨1575260307645305007521099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050173538430203338347399 1575260307645305007521099)
          ·
            refine ⟨2362890461467957511281649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575260307645305007521099 2362890461467957511281649)
            ·
              refine ⟨1772167846100968133461237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362890461467957511281649 1772167846100968133461237)
              ·
                refine ⟨166140735571965762511991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1772167846100968133461237 166140735571965762511991)
                ·
                  refine ⟨249211103357948643767987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166140735571965762511991 249211103357948643767987)
                  ·
                    refine ⟨373816655036922965651981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249211103357948643767987 373816655036922965651981)
                    ·
                      refine ⟨140181245638846112119493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 373816655036922965651981 140181245638846112119493)
                      ·
                        rfl

theorem cell23_273002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_273002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273002 prefixEnd_273002 := by exact prefixLift 273002
  have htrace : WordTrace (prefixWord ++ tailWord_273002) baseStart_273002 baseEnd_273002 := by
    simpa [prefixWord, tailWord_273002, baseEnd_273002] using wordTrace_append hprefix tailTrace_273002
  have hstable : (prefixWord ++ tailWord_273002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273002).length < 2 ^ (prefixWord ++ tailWord_273002).sum := by decide
  have hdescent : baseEnd_273002 < baseStart_273002 := by decide
  rcases family_descends (prefixWord ++ tailWord_273002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273011 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5]
def baseStart_273011 : Nat := 118140960795 + 273011 * 2 ^ 59
def prefixEnd_273011 : Nat := 4983230072969 + 3 ^ 40 * 273011 * 2
def baseEnd_273011 : Nat := 140185866964736576906951

theorem tailTrace_273011 : CollatzResearch.WordTrace tailWord_273011 prefixEnd_273011 140185866964736576906951 := by
  unfold tailWord_273011
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957529213935248411778887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6638352809290165607852591 9957529213935248411778887)
  ·
    refine ⟨14936293820902872617668331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9957529213935248411778887 14936293820902872617668331)
    ·
      refine ⟨22404440731354308926502497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14936293820902872617668331 22404440731354308926502497)
      ·
        refine ⟨16803330548515731694876873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22404440731354308926502497 16803330548515731694876873)
        ·
          refine ⟨12602497911386798771157655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16803330548515731694876873 12602497911386798771157655)
          ·
            refine ⟨18903746867080198156736483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602497911386798771157655 18903746867080198156736483)
            ·
              refine ⟨28355620300620297235104725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18903746867080198156736483 28355620300620297235104725)
              ·
                refine ⟨664584850795788216447767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28355620300620297235104725 664584850795788216447767)
                ·
                  refine ⟨996877276193682324671651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664584850795788216447767 996877276193682324671651)
                  ·
                    refine ⟨1495315914290523487007477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996877276193682324671651 1495315914290523487007477)
                    ·
                      refine ⟨140185866964736576906951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1495315914290523487007477 140185866964736576906951)
                      ·
                        rfl

theorem cell23_273011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_273011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273011 prefixEnd_273011 := by exact prefixLift 273011
  have htrace : WordTrace (prefixWord ++ tailWord_273011) baseStart_273011 baseEnd_273011 := by
    simpa [prefixWord, tailWord_273011, baseEnd_273011] using wordTrace_append hprefix tailTrace_273011
  have hstable : (prefixWord ++ tailWord_273011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273011).length < 2 ^ (prefixWord ++ tailWord_273011).sum := by decide
  have hdescent : baseEnd_273011 < baseStart_273011 := by decide
  rcases family_descends (prefixWord ++ tailWord_273011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273042 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_273042 : Nat := 118140960795 + 273042 * 2 ^ 59
def prefixEnd_273042 : Nat := 4983230072969 + 3 ^ 40 * 273042 * 2
def baseEnd_273042 : Nat := 140201784865025955619309

theorem tailTrace_273042 : CollatzResearch.WordTrace tailWord_273042 prefixEnd_273042 140201784865025955619309 := by
  unfold tailWord_273042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489664969205735176539345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6639106584548627137438253 2489664969205735176539345)
  ·
    refine ⟨1867248726904301382404509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2489664969205735176539345 1867248726904301382404509)
    ·
      refine ⟨700218272589113018401691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1867248726904301382404509 700218272589113018401691)
      ·
        refine ⟨1050327408883669527602537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700218272589113018401691 1050327408883669527602537)
        ·
          refine ⟨787745556662752145701903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1050327408883669527602537 787745556662752145701903)
          ·
            refine ⟨1181618334994128218552855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787745556662752145701903 1181618334994128218552855)
            ·
              refine ⟨1772427502491192327829283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181618334994128218552855 1772427502491192327829283)
              ·
                refine ⟨2658641253736788491743925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772427502491192327829283 2658641253736788491743925)
                ·
                  refine ⟨249247617537823921100993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2658641253736788491743925 249247617537823921100993)
                  ·
                    refine ⟨186935713153367940825745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 249247617537823921100993 186935713153367940825745)
                    ·
                      refine ⟨140201784865025955619309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186935713153367940825745 140201784865025955619309)
                      ·
                        rfl

theorem cell23_273042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_273042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273042 prefixEnd_273042 := by exact prefixLift 273042
  have htrace : WordTrace (prefixWord ++ tailWord_273042) baseStart_273042 baseEnd_273042 := by
    simpa [prefixWord, tailWord_273042, baseEnd_273042] using wordTrace_append hprefix tailTrace_273042
  have hstable : (prefixWord ++ tailWord_273042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273042).length < 2 ^ (prefixWord ++ tailWord_273042).sum := by decide
  have hdescent : baseEnd_273042 < baseStart_273042 := by decide
  rcases family_descends (prefixWord ++ tailWord_273042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273048 : List Nat := [2, 1, 2, 4, 1, 1, 5, 7]
def baseStart_273048 : Nat := 118140960795 + 273048 * 2 ^ 59
def prefixEnd_273048 : Nat := 4983230072969 + 3 ^ 40 * 273048 * 2
def baseEnd_273048 : Nat := 5192772805516775264603

theorem tailTrace_273048 : CollatzResearch.WordTrace tailWord_273048 prefixEnd_273048 5192772805516775264603 := by
  unfold tailWord_273048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979439357400601865437899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6639252476534135820583865 4979439357400601865437899)
  ·
    refine ⟨7469159036100902798156849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4979439357400601865437899 7469159036100902798156849)
    ·
      refine ⟨5601869277075677098617637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7469159036100902798156849 5601869277075677098617637)
      ·
        refine ⟨1050350489451689455990807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5601869277075677098617637 1050350489451689455990807)
        ·
          refine ⟨1575525734177534183986211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050350489451689455990807 1575525734177534183986211)
          ·
            refine ⟨2363288601266301275979317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575525734177534183986211 2363288601266301275979317)
            ·
              refine ⟨221558306368715744623061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2363288601266301275979317 221558306368715744623061)
              ·
                refine ⟨5192772805516775264603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 221558306368715744623061 5192772805516775264603)
                ·
                  rfl

theorem cell23_273048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 7].length) (baseStart_273048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273048 prefixEnd_273048 := by exact prefixLift 273048
  have htrace : WordTrace (prefixWord ++ tailWord_273048) baseStart_273048 baseEnd_273048 := by
    simpa [prefixWord, tailWord_273048, baseEnd_273048] using wordTrace_append hprefix tailTrace_273048
  have hstable : (prefixWord ++ tailWord_273048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273048).length < 2 ^ (prefixWord ++ tailWord_273048).sum := by decide
  have hdescent : baseEnd_273048 < baseStart_273048 := by decide
  rcases family_descends (prefixWord ++ tailWord_273048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273075 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 3]
def baseStart_273075 : Nat := 118140960795 + 273075 * 2 ^ 59
def prefixEnd_273075 : Nat := 4983230072969 + 3 ^ 40 * 273075 * 2
def baseEnd_273075 : Nat := 140218729726624326506657

theorem tailTrace_273075 : CollatzResearch.WordTrace tailWord_273075 prefixEnd_273075 140218729726624326506657 := by
  unfold tailWord_273075
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959863485703387342108679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6639908990468924894739119 9959863485703387342108679)
  ·
    refine ⟨14939795228555081013163019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959863485703387342108679 14939795228555081013163019)
    ·
      refine ⟨22409692842832621519744529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14939795228555081013163019 22409692842832621519744529)
      ·
        refine ⟨16807269632124466139808397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22409692842832621519744529 16807269632124466139808397)
        ·
          refine ⟨6302726112046674802428149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16807269632124466139808397 6302726112046674802428149)
          ·
            refine ⟨590880573004375762727639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6302726112046674802428149 590880573004375762727639)
            ·
              refine ⟨886320859506563644091459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590880573004375762727639 886320859506563644091459)
              ·
                refine ⟨1329481289259845466137189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886320859506563644091459 1329481289259845466137189)
                ·
                  refine ⟨249277741736221024900723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329481289259845466137189 249277741736221024900723)
                  ·
                    refine ⟨373916612604331537351085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249277741736221024900723 373916612604331537351085)
                    ·
                      refine ⟨140218729726624326506657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 373916612604331537351085 140218729726624326506657)
                      ·
                        rfl

theorem cell23_273075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_273075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273075 prefixEnd_273075 := by exact prefixLift 273075
  have htrace : WordTrace (prefixWord ++ tailWord_273075) baseStart_273075 baseEnd_273075 := by
    simpa [prefixWord, tailWord_273075, baseEnd_273075] using wordTrace_append hprefix tailTrace_273075
  have hstable : (prefixWord ++ tailWord_273075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273075).length < 2 ^ (prefixWord ++ tailWord_273075).sum := by decide
  have hdescent : baseEnd_273075 < baseStart_273075 := by decide
  rcases family_descends (prefixWord ++ tailWord_273075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273089 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_273089 : Nat := 118140960795 + 273089 * 2 ^ 59
def prefixEnd_273089 : Nat := 4983230072969 + 3 ^ 40 * 273089 * 2
def baseEnd_273089 : Nat := 140225918455787271731593

theorem tailTrace_273089 : CollatzResearch.WordTrace tailWord_273089 prefixEnd_273089 140225918455787271731593 := by
  unfold tailWord_273089
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960374107652667733118321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6640249405101778488745547 9960374107652667733118321)
  ·
    refine ⟨7470280580739500799838741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9960374107652667733118321 7470280580739500799838741)
    ·
      refine ⟨350169402222164099992441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7470280580739500799838741 350169402222164099992441)
      ·
        refine ⟨262627051666623074994331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350169402222164099992441 262627051666623074994331)
        ·
          refine ⟨393940577499934612491497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262627051666623074994331 393940577499934612491497)
          ·
            refine ⟨295455433124950959368623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393940577499934612491497 295455433124950959368623)
            ·
              refine ⟨443183149687426439052935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295455433124950959368623 443183149687426439052935)
              ·
                refine ⟨664774724531139658579403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443183149687426439052935 664774724531139658579403)
                ·
                  refine ⟨997162086796709487869105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664774724531139658579403 997162086796709487869105)
                  ·
                    refine ⟨747871565097532115901829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 997162086796709487869105 747871565097532115901829)
                    ·
                      refine ⟨140225918455787271731593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 747871565097532115901829 140225918455787271731593)
                      ·
                        rfl

theorem cell23_273089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_273089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273089 prefixEnd_273089 := by exact prefixLift 273089
  have htrace : WordTrace (prefixWord ++ tailWord_273089) baseStart_273089 baseEnd_273089 := by
    simpa [prefixWord, tailWord_273089, baseEnd_273089] using wordTrace_append hprefix tailTrace_273089
  have hstable : (prefixWord ++ tailWord_273089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273089).length < 2 ^ (prefixWord ++ tailWord_273089).sum := by decide
  have hdescent : baseEnd_273089 < baseStart_273089 := by decide
  rcases family_descends (prefixWord ++ tailWord_273089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273092 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_273092 : Nat := 118140960795 + 273092 * 2 ^ 59
def prefixEnd_273092 : Nat := 4983230072969 + 3 ^ 40 * 273092 * 2
def baseEnd_273092 : Nat := 140227458897750759994079

theorem tailTrace_273092 : CollatzResearch.WordTrace tailWord_273092 prefixEnd_273092 140227458897750759994079 := by
  unfold tailWord_273092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4980241763320899622738765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6640322351094532830318353 4980241763320899622738765)
  ·
    refine ⟨1867590661245337358527037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4980241763320899622738765 1867590661245337358527037)
    ·
      refine ⟨700346497967001509447639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1867590661245337358527037 700346497967001509447639)
      ·
        refine ⟨1050519746950502264171459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700346497967001509447639 1050519746950502264171459)
        ·
          refine ⟨1575779620425753396257189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050519746950502264171459 1575779620425753396257189)
          ·
            refine ⟨295458678829828761798223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1575779620425753396257189 295458678829828761798223)
            ·
              refine ⟨443188018244743142697335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295458678829828761798223 443188018244743142697335)
              ·
                refine ⟨664782027367114714046003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443188018244743142697335 664782027367114714046003)
                ·
                  refine ⟨997173041050672071069005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664782027367114714046003 997173041050672071069005)
                  ·
                    refine ⟨373939890394002026650877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 997173041050672071069005 373939890394002026650877)
                    ·
                      refine ⟨140227458897750759994079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 373939890394002026650877 140227458897750759994079)
                      ·
                        rfl

theorem cell23_273092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_273092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273092 prefixEnd_273092 := by exact prefixLift 273092
  have htrace : WordTrace (prefixWord ++ tailWord_273092) baseStart_273092 baseEnd_273092 := by
    simpa [prefixWord, tailWord_273092, baseEnd_273092] using wordTrace_append hprefix tailTrace_273092
  have hstable : (prefixWord ++ tailWord_273092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273092).length < 2 ^ (prefixWord ++ tailWord_273092).sum := by decide
  have hdescent : baseEnd_273092 < baseStart_273092 := by decide
  rcases family_descends (prefixWord ++ tailWord_273092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273102 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_273102 : Nat := 118140960795 + 273102 * 2 ^ 59
def prefixEnd_273102 : Nat := 4983230072969 + 3 ^ 40 * 273102 * 2
def baseEnd_273102 : Nat := 140232593704295720869033

theorem tailTrace_273102 : CollatzResearch.WordTrace tailWord_273102 prefixEnd_273102 140232593704295720869033 := by
  unfold tailWord_273102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245106032075696369167695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6640565504403713968894373 1245106032075696369167695)
  ·
    refine ⟨1867659048113544553751543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245106032075696369167695 1867659048113544553751543)
    ·
      refine ⟨2801488572170316830627315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1867659048113544553751543 2801488572170316830627315)
      ·
        refine ⟨4202232858255475245940973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801488572170316830627315 4202232858255475245940973)
        ·
          refine ⟨1575837321845803217227865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4202232858255475245940973 1575837321845803217227865)
          ·
            refine ⟨1181877991384352412920899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575837321845803217227865 1181877991384352412920899)
            ·
              refine ⟨1772816987076528619381349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181877991384352412920899 1772816987076528619381349)
              ·
                refine ⟨332403185076849116134003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1772816987076528619381349 332403185076849116134003)
                ·
                  refine ⟨498604777615273674201005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332403185076849116134003 498604777615273674201005)
                  ·
                    refine ⟨186976791605727627825377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498604777615273674201005 186976791605727627825377)
                    ·
                      refine ⟨140232593704295720869033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186976791605727627825377 140232593704295720869033)
                      ·
                        rfl

theorem cell23_273102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_273102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273102 prefixEnd_273102 := by exact prefixLift 273102
  have htrace : WordTrace (prefixWord ++ tailWord_273102) baseStart_273102 baseEnd_273102 := by
    simpa [prefixWord, tailWord_273102, baseEnd_273102] using wordTrace_append hprefix tailTrace_273102
  have hstable : (prefixWord ++ tailWord_273102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273102).length < 2 ^ (prefixWord ++ tailWord_273102).sum := by decide
  have hdescent : baseEnd_273102 < baseStart_273102 := by decide
  rcases family_descends (prefixWord ++ tailWord_273102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273131 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_273131 : Nat := 118140960795 + 273131 * 2 ^ 59
def prefixEnd_273131 : Nat := 4983230072969 + 3 ^ 40 * 273131 * 2
def baseEnd_273131 : Nat := 140247484643276107406399

theorem tailTrace_273131 : CollatzResearch.WordTrace tailWord_273131 prefixEnd_273131 140247484643276107406399 := by
  unfold tailWord_273131
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961905973500508906147247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6641270649000339270764831 9961905973500508906147247)
  ·
    refine ⟨14942858960250763359220871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9961905973500508906147247 14942858960250763359220871)
    ·
      refine ⟨22414288440376145038831307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14942858960250763359220871 22414288440376145038831307)
      ·
        refine ⟨33621432660564217558246961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22414288440376145038831307 33621432660564217558246961)
        ·
          refine ⟨25216074495423163168685221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33621432660564217558246961 25216074495423163168685221)
          ·
            refine ⟨4728013967891843094128479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25216074495423163168685221 4728013967891843094128479)
            ·
              refine ⟨7092020951837764641192719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728013967891843094128479 7092020951837764641192719)
              ·
                refine ⟨10638031427756646961789079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7092020951837764641192719 10638031427756646961789079)
                ·
                  refine ⟨15957047141634970442683619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10638031427756646961789079 15957047141634970442683619)
                  ·
                    refine ⟨23935570712452455664025429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15957047141634970442683619 23935570712452455664025429)
                    ·
                      refine ⟨140247484643276107406399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 23935570712452455664025429 140247484643276107406399)
                      ·
                        rfl

theorem cell23_273131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_273131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273131 prefixEnd_273131 := by exact prefixLift 273131
  have htrace : WordTrace (prefixWord ++ tailWord_273131) baseStart_273131 baseEnd_273131 := by
    simpa [prefixWord, tailWord_273131, baseEnd_273131] using wordTrace_append hprefix tailTrace_273131
  have hstable : (prefixWord ++ tailWord_273131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273131).length < 2 ^ (prefixWord ++ tailWord_273131).sum := by decide
  have hdescent : baseEnd_273131 < baseStart_273131 := by decide
  rcases family_descends (prefixWord ++ tailWord_273131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273132 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_273132 : Nat := 118140960795 + 273132 * 2 ^ 59
def prefixEnd_273132 : Nat := 4983230072969 + 3 ^ 40 * 273132 * 2
def baseEnd_273132 : Nat := 140247998123930603493895

theorem tailTrace_273132 : CollatzResearch.WordTrace tailWord_273132 prefixEnd_273132 140247998123930603493895 := by
  unfold tailWord_273132
  simp only [CollatzResearch.WordTrace]
  refine ⟨4980971223248443038466825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6641294964331257384622433 4980971223248443038466825)
  ·
    refine ⟨3735728417436332278850119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4980971223248443038466825 3735728417436332278850119)
    ·
      refine ⟨5603592626154498418275179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735728417436332278850119 5603592626154498418275179)
      ·
        refine ⟨8405388939231747627412769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5603592626154498418275179 8405388939231747627412769)
        ·
          refine ⟨6304041704423810720559577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8405388939231747627412769 6304041704423810720559577)
          ·
            refine ⟨4728031278317858040419683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6304041704423810720559577 4728031278317858040419683)
            ·
              refine ⟨7092046917476787060629525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728031278317858040419683 7092046917476787060629525)
              ·
                refine ⟨332439699256724393467009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7092046917476787060629525 332439699256724393467009)
                ·
                  refine ⟨249329774442543295100257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332439699256724393467009 249329774442543295100257)
                  ·
                    refine ⟨186997330831907471325193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 249329774442543295100257 186997330831907471325193)
                    ·
                      refine ⟨140247998123930603493895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186997330831907471325193 140247998123930603493895)
                      ·
                        rfl

theorem cell23_273132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_273132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273132 prefixEnd_273132 := by exact prefixLift 273132
  have htrace : WordTrace (prefixWord ++ tailWord_273132) baseStart_273132 baseEnd_273132 := by
    simpa [prefixWord, tailWord_273132, baseEnd_273132] using wordTrace_append hprefix tailTrace_273132
  have hstable : (prefixWord ++ tailWord_273132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273132).length < 2 ^ (prefixWord ++ tailWord_273132).sum := by decide
  have hdescent : baseEnd_273132 < baseStart_273132 := by decide
  rcases family_descends (prefixWord ++ tailWord_273132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273178 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_273178 : Nat := 118140960795 + 273178 * 2 ^ 59
def prefixEnd_273178 : Nat := 4983230072969 + 3 ^ 40 * 273178 * 2
def baseEnd_273178 : Nat := 140271618234037423518683

theorem tailTrace_273178 : CollatzResearch.WordTrace tailWord_273178 prefixEnd_273178 140271618234037423518683 := by
  unfold tailWord_273178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490905051082558983277047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6642413469553490622072125 2490905051082558983277047)
  ·
    refine ⟨3736357576623838474915571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490905051082558983277047 3736357576623838474915571)
    ·
      refine ⟨5604536364935757712373357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736357576623838474915571 5604536364935757712373357)
      ·
        refine ⟨2101701136850909142140009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5604536364935757712373357 2101701136850909142140009)
        ·
          refine ⟨1576275852638181856605007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101701136850909142140009 1576275852638181856605007)
          ·
            refine ⟨2364413778957272784907511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576275852638181856605007 2364413778957272784907511)
            ·
              refine ⟨3546620668435909177361267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364413778957272784907511 3546620668435909177361267)
              ·
                refine ⟨5319931002653863766041901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546620668435909177361267 5319931002653863766041901)
                ·
                  refine ⟨1994974125995198912265713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5319931002653863766041901 1994974125995198912265713)
                  ·
                    refine ⟨1496230594496399184199285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994974125995198912265713 1496230594496399184199285)
                    ·
                      refine ⟨140271618234037423518683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1496230594496399184199285 140271618234037423518683)
                      ·
                        rfl

theorem cell23_273178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_273178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273178 prefixEnd_273178 := by exact prefixLift 273178
  have htrace : WordTrace (prefixWord ++ tailWord_273178) baseStart_273178 baseEnd_273178 := by
    simpa [prefixWord, tailWord_273178, baseEnd_273178] using wordTrace_append hprefix tailTrace_273178
  have hstable : (prefixWord ++ tailWord_273178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273178).length < 2 ^ (prefixWord ++ tailWord_273178).sum := by decide
  have hdescent : baseEnd_273178 < baseStart_273178 := by decide
  rcases family_descends (prefixWord ++ tailWord_273178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273215 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 5, 4]
def baseStart_273215 : Nat := 118140960795 + 273215 * 2 ^ 59
def prefixEnd_273215 : Nat := 4983230072969 + 3 ^ 40 * 273215 * 2
def baseEnd_273215 : Nat := 46763539006084592918671

theorem tailTrace_273215 : CollatzResearch.WordTrace tailWord_273215 prefixEnd_273215 46763539006084592918671 := by
  unfold tailWord_273215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9964969705196191252205099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6643313136797460834803399 9964969705196191252205099)
  ·
    refine ⟨14947454557794286878307649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9964969705196191252205099 14947454557794286878307649)
    ·
      refine ⟨11210590918345715158730737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14947454557794286878307649 11210590918345715158730737)
      ·
        refine ⟨8407943188759286369048053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11210590918345715158730737 8407943188759286369048053)
        ·
          refine ⟨788244673946183097098255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8407943188759286369048053 788244673946183097098255)
          ·
            refine ⟨1182367010919274645647383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788244673946183097098255 1182367010919274645647383)
            ·
              refine ⟨1773550516378911968471075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182367010919274645647383 1773550516378911968471075)
              ·
                refine ⟨2660325774568367952706613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773550516378911968471075 2660325774568367952706613)
                ·
                  refine ⟨249405541365784495566245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2660325774568367952706613 249405541365784495566245)
                  ·
                    refine ⟨46763539006084592918671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249405541365784495566245 46763539006084592918671)
                    ·
                      rfl

theorem cell23_273215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_273215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273215 prefixEnd_273215 := by exact prefixLift 273215
  have htrace : WordTrace (prefixWord ++ tailWord_273215) baseStart_273215 baseEnd_273215 := by
    simpa [prefixWord, tailWord_273215, baseEnd_273215] using wordTrace_append hprefix tailTrace_273215
  have hstable : (prefixWord ++ tailWord_273215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273215).length < 2 ^ (prefixWord ++ tailWord_273215).sum := by decide
  have hdescent : baseEnd_273215 < baseStart_273215 := by decide
  rcases family_descends (prefixWord ++ tailWord_273215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273225 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_273225 : Nat := 118140960795 + 273225 * 2 ^ 59
def prefixEnd_273225 : Nat := 4983230072969 + 3 ^ 40 * 273225 * 2
def baseEnd_273225 : Nat := 140295751824798739630967

theorem tailTrace_273225 : CollatzResearch.WordTrace tailWord_273225 prefixEnd_273225 140295751824798739630967 := by
  unfold tailWord_273225
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965334435159962960069129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6643556290106641973379419 9965334435159962960069129)
  ·
    refine ⟨7474000826369972220051847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9965334435159962960069129 7474000826369972220051847)
    ·
      refine ⟨11211001239554958330077771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474000826369972220051847 11211001239554958330077771)
      ·
        refine ⟨16816501859332437495116657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11211001239554958330077771 16816501859332437495116657)
        ·
          refine ⟨12612376394499328121337493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16816501859332437495116657 12612376394499328121337493)
          ·
            refine ⟨591205143492156005687695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12612376394499328121337493 591205143492156005687695)
            ·
              refine ⟨886807715238234008531543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591205143492156005687695 886807715238234008531543)
              ·
                refine ⟨1330211572857351012797315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886807715238234008531543 1330211572857351012797315)
                ·
                  refine ⟨1995317359286026519195973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330211572857351012797315 1995317359286026519195973)
                  ·
                    refine ⟨374122004866129972349245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1995317359286026519195973 374122004866129972349245)
                    ·
                      refine ⟨140295751824798739630967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374122004866129972349245 140295751824798739630967)
                      ·
                        rfl

theorem cell23_273225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_273225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273225 prefixEnd_273225 := by exact prefixLift 273225
  have htrace : WordTrace (prefixWord ++ tailWord_273225) baseStart_273225 baseEnd_273225 := by
    simpa [prefixWord, tailWord_273225, baseEnd_273225] using wordTrace_append hprefix tailTrace_273225
  have hstable : (prefixWord ++ tailWord_273225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273225).length < 2 ^ (prefixWord ++ tailWord_273225).sum := by decide
  have hdescent : baseEnd_273225 < baseStart_273225 := by decide
  rcases family_descends (prefixWord ++ tailWord_273225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273232 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 1, 4]
def baseStart_273232 : Nat := 118140960795 + 273232 * 2 ^ 59
def prefixEnd_273232 : Nat := 4983230072969 + 3 ^ 40 * 273232 * 2
def baseEnd_273232 : Nat := 46766448729793404081145

theorem tailTrace_273232 : CollatzResearch.WordTrace tailWord_273232 prefixEnd_273232 46766448729793404081145 := by
  unfold tailWord_273232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982794873067301577786975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6643726497423068770382633 4982794873067301577786975)
  ·
    refine ⟨7474192309600952366680463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4982794873067301577786975 7474192309600952366680463)
    ·
      refine ⟨11211288464401428550020695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474192309600952366680463 11211288464401428550020695)
      ·
        refine ⟨16816932696602142825031043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11211288464401428550020695 16816932696602142825031043)
        ·
          refine ⟨25225399044903214237546565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16816932696602142825031043 25225399044903214237546565)
          ·
            refine ⟨4729762320919352669539981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25225399044903214237546565 4729762320919352669539981)
            ·
              refine ⟨1773660870344757251077493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4729762320919352669539981 1773660870344757251077493)
              ·
                refine ⟨166280706594820992288515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1773660870344757251077493 166280706594820992288515)
                ·
                  refine ⟨249421059892231488432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166280706594820992288515 249421059892231488432773)
                  ·
                    refine ⟨46766448729793404081145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249421059892231488432773 46766448729793404081145)
                    ·
                      rfl

theorem cell23_273232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 4].length) (baseStart_273232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273232 prefixEnd_273232 := by exact prefixLift 273232
  have htrace : WordTrace (prefixWord ++ tailWord_273232) baseStart_273232 baseEnd_273232 := by
    simpa [prefixWord, tailWord_273232, baseEnd_273232] using wordTrace_append hprefix tailTrace_273232
  have hstable : (prefixWord ++ tailWord_273232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273232).length < 2 ^ (prefixWord ++ tailWord_273232).sum := by decide
  have hdescent : baseEnd_273232 < baseStart_273232 := by decide
  rcases family_descends (prefixWord ++ tailWord_273232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273248 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_273248 : Nat := 118140960795 + 273248 * 2 ^ 59
def prefixEnd_273248 : Nat := 4983230072969 + 3 ^ 40 * 273248 * 2
def baseEnd_273248 : Nat := 140307561879852149643361

theorem tailTrace_273248 : CollatzResearch.WordTrace tailWord_273248 prefixEnd_273248 140307561879852149643361 := by
  unfold tailWord_273248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983086657038318944078199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6644115542717758592104265 4983086657038318944078199)
  ·
    refine ⟨7474629985557478416117299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4983086657038318944078199 7474629985557478416117299)
    ·
      refine ⟨11211944978336217624175949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474629985557478416117299 11211944978336217624175949)
      ·
        refine ⟨4204479366876081609065981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11211944978336217624175949 4204479366876081609065981)
        ·
          refine ⟨1576679762578530603399743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4204479366876081609065981 1576679762578530603399743)
          ·
            refine ⟨2365019643867795905099615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576679762578530603399743 2365019643867795905099615)
            ·
              refine ⟨3547529465801693857649423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365019643867795905099615 3547529465801693857649423)
              ·
                refine ⟨5321294198702540786474135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547529465801693857649423 5321294198702540786474135)
                ·
                  refine ⟨7981941298053811179711203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321294198702540786474135 7981941298053811179711203)
                  ·
                    refine ⟨11972911947080716769566805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7981941298053811179711203 11972911947080716769566805)
                    ·
                      refine ⟨140307561879852149643361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 11972911947080716769566805 140307561879852149643361)
                      ·
                        rfl

theorem cell23_273248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_273248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273248 prefixEnd_273248 := by exact prefixLift 273248
  have htrace : WordTrace (prefixWord ++ tailWord_273248) baseStart_273248 baseEnd_273248 := by
    simpa [prefixWord, tailWord_273248, baseEnd_273248] using wordTrace_append hprefix tailTrace_273248
  have hstable : (prefixWord ++ tailWord_273248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273248).length < 2 ^ (prefixWord ++ tailWord_273248).sum := by decide
  have hdescent : baseEnd_273248 < baseStart_273248 := by decide
  rcases family_descends (prefixWord ++ tailWord_273248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273275 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 1, 5]
def baseStart_273275 : Nat := 118140960795 + 273275 * 2 ^ 59
def prefixEnd_273275 : Nat := 4983230072969 + 3 ^ 40 * 273275 * 2
def baseEnd_273275 : Nat := 46773808619174514668579

theorem tailTrace_273275 : CollatzResearch.WordTrace tailWord_273275 prefixEnd_273275 46773808619174514668579 := by
  unfold tailWord_273275
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967158084978821499389279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6644772056652547666259519 9967158084978821499389279)
  ·
    refine ⟨14950737127468232249083919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9967158084978821499389279 14950737127468232249083919)
    ·
      refine ⟨22426105691202348373625879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14950737127468232249083919 22426105691202348373625879)
      ·
        refine ⟨33639158536803522560438819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22426105691202348373625879 33639158536803522560438819)
        ·
          refine ⟨50458737805205283840658229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33639158536803522560438819 50458737805205283840658229)
          ·
            refine ⟨4730506669237995360061709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50458737805205283840658229 4730506669237995360061709)
            ·
              refine ⟨1773940000964248260023141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4730506669237995360061709 1773940000964248260023141)
              ·
                refine ⟨332613750180796548754339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1773940000964248260023141 332613750180796548754339)
                ·
                  refine ⟨498920625271194823131509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332613750180796548754339 498920625271194823131509)
                  ·
                    refine ⟨46773808619174514668579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 498920625271194823131509 46773808619174514668579)
                    ·
                      rfl

theorem cell23_273275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 5].length) (baseStart_273275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273275 prefixEnd_273275 := by exact prefixLift 273275
  have htrace : WordTrace (prefixWord ++ tailWord_273275) baseStart_273275 baseEnd_273275 := by
    simpa [prefixWord, tailWord_273275, baseEnd_273275] using wordTrace_append hprefix tailTrace_273275
  have hstable : (prefixWord ++ tailWord_273275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273275).length < 2 ^ (prefixWord ++ tailWord_273275).sum := by decide
  have hdescent : baseEnd_273275 < baseStart_273275 := by decide
  rcases family_descends (prefixWord ++ tailWord_273275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273306 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_273306 : Nat := 118140960795 + 273306 * 2 ^ 59
def prefixEnd_273306 : Nat := 4983230072969 + 3 ^ 40 * 273306 * 2
def baseEnd_273306 : Nat := 140337343757812922718095

theorem tailTrace_273306 : CollatzResearch.WordTrace tailWord_273306 prefixEnd_273306 140337343757812922718095 := by
  unfold tailWord_273306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492072186966628448441943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6645525831911009195845181 2492072186966628448441943)
  ·
    refine ⟨3738108280449942672662915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2492072186966628448441943 3738108280449942672662915)
    ·
      refine ⟨5607162420674914008994373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3738108280449942672662915 5607162420674914008994373)
      ·
        refine ⟨1051342953876546376686445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5607162420674914008994373 1051342953876546376686445)
        ·
          refine ⟨394253607703704891257417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1051342953876546376686445 394253607703704891257417)
          ·
            refine ⟨295690205777778668443063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394253607703704891257417 295690205777778668443063)
            ·
              refine ⟨443535308666668002664595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295690205777778668443063 443535308666668002664595)
              ·
                refine ⟨665302963000002003996893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443535308666668002664595 665302963000002003996893)
                ·
                  refine ⟨249488611125000751498835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 665302963000002003996893 249488611125000751498835)
                  ·
                    refine ⟨374232916687501127248253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249488611125000751498835 374232916687501127248253)
                    ·
                      refine ⟨140337343757812922718095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374232916687501127248253 140337343757812922718095)
                      ·
                        rfl

theorem cell23_273306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_273306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273306 prefixEnd_273306 := by exact prefixLift 273306
  have htrace : WordTrace (prefixWord ++ tailWord_273306) baseStart_273306 baseEnd_273306 := by
    simpa [prefixWord, tailWord_273306, baseEnd_273306] using wordTrace_append hprefix tailTrace_273306
  have hstable : (prefixWord ++ tailWord_273306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273306).length < 2 ^ (prefixWord ++ tailWord_273306).sum := by decide
  have hdescent : baseEnd_273306 < baseStart_273306 := by decide
  rcases family_descends (prefixWord ++ tailWord_273306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273315 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5]
def baseStart_273315 : Nat := 118140960795 + 273315 * 2 ^ 59
def prefixEnd_273315 : Nat := 4983230072969 + 3 ^ 40 * 273315 * 2
def baseEnd_273315 : Nat := 140341965083703387505553

theorem tailTrace_273315 : CollatzResearch.WordTrace tailWord_273315 prefixEnd_273315 140341965083703387505553 := by
  unfold tailWord_273315
  simp only [CollatzResearch.WordTrace]
  refine ⟨9968617004833908330845399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6645744669889272220563599 9968617004833908330845399)
  ·
    refine ⟨14952925507250862496268099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9968617004833908330845399 14952925507250862496268099)
    ·
      refine ⟨22429388260876293744402149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14952925507250862496268099 22429388260876293744402149)
      ·
        refine ⟨4205510298914305077075403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22429388260876293744402149 4205510298914305077075403)
        ·
          refine ⟨6308265448371457615613105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205510298914305077075403 6308265448371457615613105)
          ·
            refine ⟨4731199086278593211709829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6308265448371457615613105 4731199086278593211709829)
            ·
              refine ⟨887099828677236227195593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4731199086278593211709829 887099828677236227195593)
              ·
                refine ⟨665324871507927170396695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887099828677236227195593 665324871507927170396695)
                ·
                  refine ⟨997987307261890755595043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665324871507927170396695 997987307261890755595043)
                  ·
                    refine ⟨1496980960892836133392565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 997987307261890755595043 1496980960892836133392565)
                    ·
                      refine ⟨140341965083703387505553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1496980960892836133392565 140341965083703387505553)
                      ·
                        rfl

theorem cell23_273315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_273315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273315 prefixEnd_273315 := by exact prefixLift 273315
  have htrace : WordTrace (prefixWord ++ tailWord_273315) baseStart_273315 baseEnd_273315 := by
    simpa [prefixWord, tailWord_273315, baseEnd_273315] using wordTrace_append hprefix tailTrace_273315
  have hstable : (prefixWord ++ tailWord_273315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273315).length < 2 ^ (prefixWord ++ tailWord_273315).sum := by decide
  have hdescent : baseEnd_273315 < baseStart_273315 := by decide
  rcases family_descends (prefixWord ++ tailWord_273315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273342 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_273342 : Nat := 118140960795 + 273342 * 2 ^ 59
def prefixEnd_273342 : Nat := 4983230072969 + 3 ^ 40 * 273342 * 2
def baseEnd_273342 : Nat := 140355829061374781867929

theorem tailTrace_273342 : CollatzResearch.WordTrace tailWord_273342 prefixEnd_273342 140355829061374781867929 := by
  unfold tailWord_273342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246200221967011492759785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6646401183824061294718853 1246200221967011492759785)
  ·
    refine ⟨934650166475258619569839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1246200221967011492759785 934650166475258619569839)
    ·
      refine ⟨1401975249712887929354759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934650166475258619569839 1401975249712887929354759)
      ·
        refine ⟨2102962874569331894032139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401975249712887929354759 2102962874569331894032139)
        ·
          refine ⟨3154444311853997841048209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102962874569331894032139 3154444311853997841048209)
          ·
            refine ⟨2365833233890498380786157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3154444311853997841048209 2365833233890498380786157)
            ·
              refine ⟨887187462708936892794809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2365833233890498380786157 887187462708936892794809)
              ·
                refine ⟨665390597031702669596107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887187462708936892794809 665390597031702669596107)
                ·
                  refine ⟨998085895547554004394161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 665390597031702669596107 998085895547554004394161)
                  ·
                    refine ⟨748564421660665503295621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998085895547554004394161 748564421660665503295621)
                    ·
                      refine ⟨140355829061374781867929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 748564421660665503295621 140355829061374781867929)
                      ·
                        rfl

theorem cell23_273342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_273342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273342 prefixEnd_273342 := by exact prefixLift 273342
  have htrace : WordTrace (prefixWord ++ tailWord_273342) baseStart_273342 baseEnd_273342 := by
    simpa [prefixWord, tailWord_273342, baseEnd_273342] using wordTrace_append hprefix tailTrace_273342
  have hstable : (prefixWord ++ tailWord_273342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273342).length < 2 ^ (prefixWord ++ tailWord_273342).sum := by decide
  have hdescent : baseEnd_273342 < baseStart_273342 := by decide
  rcases family_descends (prefixWord ++ tailWord_273342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273357 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_273357 : Nat := 118140960795 + 273357 * 2 ^ 59
def prefixEnd_273357 : Nat := 4983230072969 + 3 ^ 40 * 273357 * 2
def baseEnd_273357 : Nat := 140363531271192223180361

theorem tailTrace_273357 : CollatzResearch.WordTrace tailWord_273357 prefixEnd_273357 140363531271192223180361 := by
  unfold tailWord_273357
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970148870681749503874325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6646765913787833002582883 9970148870681749503874325)
  ·
    refine ⟨467350728313207007994109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9970148870681749503874325 467350728313207007994109)
    ·
      refine ⟨175256523117452627997791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 467350728313207007994109 175256523117452627997791)
      ·
        refine ⟨262884784676178941996687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175256523117452627997791 262884784676178941996687)
        ·
          refine ⟨394327177014268412995031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262884784676178941996687 394327177014268412995031)
          ·
            refine ⟨591490765521402619492547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394327177014268412995031 591490765521402619492547)
            ·
              refine ⟨887236148282103929238821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591490765521402619492547 887236148282103929238821)
              ·
                refine ⟨166356777802894486732279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 887236148282103929238821 166356777802894486732279)
                ·
                  refine ⟨249535166704341730098419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166356777802894486732279 249535166704341730098419)
                  ·
                    refine ⟨374302750056512595147629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249535166704341730098419 374302750056512595147629)
                    ·
                      refine ⟨140363531271192223180361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374302750056512595147629 140363531271192223180361)
                      ·
                        rfl

theorem cell23_273357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_273357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273357 prefixEnd_273357 := by exact prefixLift 273357
  have htrace : WordTrace (prefixWord ++ tailWord_273357) baseStart_273357 baseEnd_273357 := by
    simpa [prefixWord, tailWord_273357, baseEnd_273357] using wordTrace_append hprefix tailTrace_273357
  have hstable : (prefixWord ++ tailWord_273357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273357).length < 2 ^ (prefixWord ++ tailWord_273357).sum := by decide
  have hdescent : baseEnd_273357 < baseStart_273357 := by decide
  rcases family_descends (prefixWord ++ tailWord_273357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273379 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 3]
def baseStart_273379 : Nat := 118140960795 + 273379 * 2 ^ 59
def prefixEnd_273379 : Nat := 4983230072969 + 3 ^ 40 * 273379 * 2
def baseEnd_273379 : Nat := 140374827845591137105259

theorem tailTrace_273379 : CollatzResearch.WordTrace tailWord_273379 prefixEnd_273379 140374827845591137105259 := by
  unfold tailWord_273379
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970951276602047261175191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6647300851068031507450127 9970951276602047261175191)
  ·
    refine ⟨14956426914903070891762787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9970951276602047261175191 14956426914903070891762787)
    ·
      refine ⟨22434640372354606337644181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956426914903070891762787 22434640372354606337644181)
      ·
        refine ⟨1051623767454122172077071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22434640372354606337644181 1051623767454122172077071)
        ·
          refine ⟨1577435651181183258115607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051623767454122172077071 1577435651181183258115607)
          ·
            refine ⟨2366153476771774887173411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577435651181183258115607 2366153476771774887173411)
            ·
              refine ⟨3549230215157662330760117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366153476771774887173411 3549230215157662330760117)
              ·
                refine ⟨332740332671030843508761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3549230215157662330760117 332740332671030843508761)
                ·
                  refine ⟨249555249503273132631571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332740332671030843508761 249555249503273132631571)
                  ·
                    refine ⟨374332874254909698947357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249555249503273132631571 374332874254909698947357)
                    ·
                      refine ⟨140374827845591137105259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374332874254909698947357 140374827845591137105259)
                      ·
                        rfl

theorem cell23_273379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_273379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273379 prefixEnd_273379 := by exact prefixLift 273379
  have htrace : WordTrace (prefixWord ++ tailWord_273379) baseStart_273379 baseEnd_273379 := by
    simpa [prefixWord, tailWord_273379, baseEnd_273379] using wordTrace_append hprefix tailTrace_273379
  have hstable : (prefixWord ++ tailWord_273379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273379).length < 2 ^ (prefixWord ++ tailWord_273379).sum := by decide
  have hdescent : baseEnd_273379 < baseStart_273379 := by decide
  rcases family_descends (prefixWord ++ tailWord_273379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273397 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_273397 : Nat := 118140960795 + 273397 * 2 ^ 59
def prefixEnd_273397 : Nat := 4983230072969 + 3 ^ 40 * 273397 * 2
def baseEnd_273397 : Nat := 140384070497372066680177

theorem tailTrace_273397 : CollatzResearch.WordTrace tailWord_273397 prefixEnd_273397 140384070497372066680177 := by
  unfold tailWord_273397
  simp only [CollatzResearch.WordTrace]
  refine ⟨9971607790536836335330445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6647738527024557556886963 9971607790536836335330445)
  ·
    refine ⟨3739352921451313625748917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9971607790536836335330445 3739352921451313625748917)
    ·
      refine ⟨350564336386060652413961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3739352921451313625748917 350564336386060652413961)
      ·
        refine ⟨262923252289545489310471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350564336386060652413961 262923252289545489310471)
        ·
          refine ⟨394384878434318233965707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262923252289545489310471 394384878434318233965707)
          ·
            refine ⟨591577317651477350948561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394384878434318233965707 591577317651477350948561)
            ·
              refine ⟨443682988238608013211421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591577317651477350948561 443682988238608013211421)
              ·
                refine ⟨166381120589478004954283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 443682988238608013211421 166381120589478004954283)
                ·
                  refine ⟨249571680884217007431425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166381120589478004954283 249571680884217007431425)
                  ·
                    refine ⟨187178760663162755573569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 249571680884217007431425 187178760663162755573569)
                    ·
                      refine ⟨140384070497372066680177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187178760663162755573569 140384070497372066680177)
                      ·
                        rfl

theorem cell23_273397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_273397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273397 prefixEnd_273397 := by exact prefixLift 273397
  have htrace : WordTrace (prefixWord ++ tailWord_273397) baseStart_273397 baseEnd_273397 := by
    simpa [prefixWord, tailWord_273397, baseEnd_273397] using wordTrace_append hprefix tailTrace_273397
  have hstable : (prefixWord ++ tailWord_273397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273397).length < 2 ^ (prefixWord ++ tailWord_273397).sum := by decide
  have hdescent : baseEnd_273397 < baseStart_273397 := by decide
  rcases family_descends (prefixWord ++ tailWord_273397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273405 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_273405 : Nat := 118140960795 + 273405 * 2 ^ 59
def prefixEnd_273405 : Nat := 4983230072969 + 3 ^ 40 * 273405 * 2
def baseEnd_273405 : Nat := 140388178342608035380139

theorem tailTrace_273405 : CollatzResearch.WordTrace tailWord_273405 prefixEnd_273405 140388178342608035380139 := by
  unfold tailWord_273405
  simp only [CollatzResearch.WordTrace]
  refine ⟨9971899574507853701621669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6647933049671902467747779 9971899574507853701621669)
  ·
    refine ⟨1869731170220222569054063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9971899574507853701621669 1869731170220222569054063)
    ·
      refine ⟨2804596755330333853581095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869731170220222569054063 2804596755330333853581095)
      ·
        refine ⟨4206895132995500780371643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804596755330333853581095 4206895132995500780371643)
        ·
          refine ⟨6310342699493251170557465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206895132995500780371643 6310342699493251170557465)
          ·
            refine ⟨4732757024619938377918099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6310342699493251170557465 4732757024619938377918099)
            ·
              refine ⟨7099135536929907566877149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732757024619938377918099 7099135536929907566877149)
              ·
                refine ⟨2662175826348715337578931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7099135536929907566877149 2662175826348715337578931)
                ·
                  refine ⟨3993263739523073006368397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662175826348715337578931 3993263739523073006368397)
                  ·
                    refine ⟨1497473902321152377388149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3993263739523073006368397 1497473902321152377388149)
                    ·
                      refine ⟨140388178342608035380139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1497473902321152377388149 140388178342608035380139)
                      ·
                        rfl

theorem cell23_273405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_273405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273405 prefixEnd_273405 := by exact prefixLift 273405
  have htrace : WordTrace (prefixWord ++ tailWord_273405) baseStart_273405 baseEnd_273405 := by
    simpa [prefixWord, tailWord_273405, baseEnd_273405] using wordTrace_append hprefix tailTrace_273405
  have hstable : (prefixWord ++ tailWord_273405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273405).length < 2 ^ (prefixWord ++ tailWord_273405).sum := by decide
  have hdescent : baseEnd_273405 < baseStart_273405 := by decide
  rcases family_descends (prefixWord ++ tailWord_273405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273432 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_273432 : Nat := 118140960795 + 273432 * 2 ^ 59
def prefixEnd_273432 : Nat := 4983230072969 + 3 ^ 40 * 273432 * 2
def baseEnd_273432 : Nat := 140402042320279429742515

theorem tailTrace_273432 : CollatzResearch.WordTrace tailWord_273432 prefixEnd_273432 140402042320279429742515 := by
  unfold tailWord_273432
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986442172705018656427275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6648589563606691541903033 4986442172705018656427275)
  ·
    refine ⟨7479663259057527984640913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986442172705018656427275 7479663259057527984640913)
    ·
      refine ⟨5609747444293145988480685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7479663259057527984640913 5609747444293145988480685)
      ·
        refine ⟨2103655291609929745680257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5609747444293145988480685 2103655291609929745680257)
        ·
          refine ⟨1577741468707447309260193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103655291609929745680257 1577741468707447309260193)
          ·
            refine ⟨1183306101530585481945145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577741468707447309260193 1183306101530585481945145)
            ·
              refine ⟨887479576147939111458859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183306101530585481945145 887479576147939111458859)
              ·
                refine ⟨1331219364221908667188289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887479576147939111458859 1331219364221908667188289)
                ·
                  refine ⟨998414523166431500391217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1331219364221908667188289 998414523166431500391217)
                  ·
                    refine ⟨748810892374823625293413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998414523166431500391217 748810892374823625293413)
                    ·
                      refine ⟨140402042320279429742515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 748810892374823625293413 140402042320279429742515)
                      ·
                        rfl

theorem cell23_273432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_273432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273432 prefixEnd_273432 := by exact prefixLift 273432
  have htrace : WordTrace (prefixWord ++ tailWord_273432) baseStart_273432 baseEnd_273432 := by
    simpa [prefixWord, tailWord_273432, baseEnd_273432] using wordTrace_append hprefix tailTrace_273432
  have hstable : (prefixWord ++ tailWord_273432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273432).length < 2 ^ (prefixWord ++ tailWord_273432).sum := by decide
  have hdescent : baseEnd_273432 < baseStart_273432 := by decide
  rcases family_descends (prefixWord ++ tailWord_273432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273442 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_273442 : Nat := 118140960795 + 273442 * 2 ^ 59
def prefixEnd_273442 : Nat := 4983230072969 + 3 ^ 40 * 273442 * 2
def baseEnd_273442 : Nat := 15600797458536043401941

theorem tailTrace_273442 : CollatzResearch.WordTrace tailWord_273442 prefixEnd_273442 15600797458536043401941 := by
  unfold tailWord_273442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493312268843452255179645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6648832716915872680479053 2493312268843452255179645)
  ·
    refine ⟨934992100816294595692367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2493312268843452255179645 934992100816294595692367)
    ·
      refine ⟨1402488151224441893538551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934992100816294595692367 1402488151224441893538551)
      ·
        refine ⟨2103732226836662840307827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402488151224441893538551 2103732226836662840307827)
        ·
          refine ⟨3155598340254994260461741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103732226836662840307827 3155598340254994260461741)
          ·
            refine ⟨1183349377595622847673153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3155598340254994260461741 1183349377595622847673153)
            ·
              refine ⟨887512033196717135754865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183349377595622847673153 887512033196717135754865)
              ·
                refine ⟨665634024897537851816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887512033196717135754865 665634024897537851816149)
                ·
                  refine ⟨15600797458536043401941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 665634024897537851816149 15600797458536043401941)
                  ·
                    rfl

theorem cell23_273442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_273442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273442 prefixEnd_273442 := by exact prefixLift 273442
  have htrace : WordTrace (prefixWord ++ tailWord_273442) baseStart_273442 baseEnd_273442 := by
    simpa [prefixWord, tailWord_273442, baseEnd_273442] using wordTrace_append hprefix tailTrace_273442
  have hstable : (prefixWord ++ tailWord_273442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273442).length < 2 ^ (prefixWord ++ tailWord_273442).sum := by decide
  have hdescent : baseEnd_273442 < baseStart_273442 := by decide
  rcases family_descends (prefixWord ++ tailWord_273442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273472 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_273472 : Nat := 118140960795 + 273472 * 2 ^ 59
def prefixEnd_273472 : Nat := 4983230072969 + 3 ^ 40 * 273472 * 2
def baseEnd_273472 : Nat := 46807527182153091080777

theorem tailTrace_273472 : CollatzResearch.WordTrace tailWord_273472 prefixEnd_273472 46807527182153091080777 := by
  unfold tailWord_273472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987171632632562072155335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6649562176843416096207113 4987171632632562072155335)
  ·
    refine ⟨7480757448948843108233003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4987171632632562072155335 7480757448948843108233003)
    ·
      refine ⟨11221136173423264662349505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480757448948843108233003 11221136173423264662349505)
      ·
        refine ⟨8415852130067448496762129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11221136173423264662349505 8415852130067448496762129)
        ·
          refine ⟨6311889097550586372571597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8415852130067448496762129 6311889097550586372571597)
          ·
            refine ⟨2366958411581469889714349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6311889097550586372571597 2366958411581469889714349)
            ·
              refine ⟨887609404343051208642881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2366958411581469889714349 887609404343051208642881)
              ·
                refine ⟨665707053257288406482161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887609404343051208642881 665707053257288406482161)
                ·
                  refine ⟨499280289942966304861621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665707053257288406482161 499280289942966304861621)
                  ·
                    refine ⟨46807527182153091080777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 499280289942966304861621 46807527182153091080777)
                    ·
                      rfl

theorem cell23_273472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_273472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273472 prefixEnd_273472 := by exact prefixLift 273472
  have htrace : WordTrace (prefixWord ++ tailWord_273472) baseStart_273472 baseEnd_273472 := by
    simpa [prefixWord, tailWord_273472, baseEnd_273472] using wordTrace_append hprefix tailTrace_273472
  have hstable : (prefixWord ++ tailWord_273472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273472).length < 2 ^ (prefixWord ++ tailWord_273472).sum := by decide
  have hdescent : baseEnd_273472 < baseStart_273472 := by decide
  rcases family_descends (prefixWord ++ tailWord_273472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273492 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_273492 : Nat := 118140960795 + 273492 * 2 ^ 59
def prefixEnd_273492 : Nat := 4983230072969 + 3 ^ 40 * 273492 * 2
def baseEnd_273492 : Nat := 140432851159549194992239

theorem tailTrace_273492 : CollatzResearch.WordTrace tailWord_273492 prefixEnd_273492 140432851159549194992239 := by
  unfold tailWord_273492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987536362596333780019365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6650048483461778373359153 4987536362596333780019365)
  ·
    refine ⟨935163067986812583753631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4987536362596333780019365 935163067986812583753631)
    ·
      refine ⟨1402744601980218875630447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935163067986812583753631 1402744601980218875630447)
      ·
        refine ⟨2104116902970328313445671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402744601980218875630447 2104116902970328313445671)
        ·
          refine ⟨3156175354455492470168507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104116902970328313445671 3156175354455492470168507)
          ·
            refine ⟨4734263031683238705252761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156175354455492470168507 4734263031683238705252761)
            ·
              refine ⟨3550697273762429028939571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4734263031683238705252761 3550697273762429028939571)
              ·
                refine ⟨5326045910643643543409357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3550697273762429028939571 5326045910643643543409357)
                ·
                  refine ⟨1997267216491366328778509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5326045910643643543409357 1997267216491366328778509)
                  ·
                    refine ⟨748975206184262373291941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997267216491366328778509 748975206184262373291941)
                    ·
                      refine ⟨140432851159549194992239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 748975206184262373291941 140432851159549194992239)
                      ·
                        rfl

theorem cell23_273492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_273492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273492 prefixEnd_273492 := by exact prefixLift 273492
  have htrace : WordTrace (prefixWord ++ tailWord_273492) baseStart_273492 baseEnd_273492 := by
    simpa [prefixWord, tailWord_273492, baseEnd_273492] using wordTrace_append hprefix tailTrace_273492
  have hstable : (prefixWord ++ tailWord_273492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273492).length < 2 ^ (prefixWord ++ tailWord_273492).sum := by decide
  have hdescent : baseEnd_273492 < baseStart_273492 := by decide
  rcases family_descends (prefixWord ++ tailWord_273492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273506 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_273506 : Nat := 118140960795 + 273506 * 2 ^ 59
def prefixEnd_273506 : Nat := 4983230072969 + 3 ^ 40 * 273506 * 2
def baseEnd_273506 : Nat := 46813346629570713405725

theorem tailTrace_273506 : CollatzResearch.WordTrace tailWord_273506 prefixEnd_273506 46813346629570713405725 := by
  unfold tailWord_273506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493895836785486987762093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6650388898094631967365581 2493895836785486987762093)
  ·
    refine ⟨935210938794557620410785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2493895836785486987762093 935210938794557620410785)
    ·
      refine ⟨701408204095918215308089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 935210938794557620410785 701408204095918215308089)
      ·
        refine ⟨526056153071938661481067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701408204095918215308089 526056153071938661481067)
        ·
          refine ⟨789084229607907992221601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526056153071938661481067 789084229607907992221601)
          ·
            refine ⟨591813172205930994166201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789084229607907992221601 591813172205930994166201)
            ·
              refine ⟨443859879154448245624651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591813172205930994166201 443859879154448245624651)
              ·
                refine ⟨665789818731672368436977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443859879154448245624651 665789818731672368436977)
                ·
                  refine ⟨499342364048754276327733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665789818731672368436977 499342364048754276327733)
                  ·
                    refine ⟨46813346629570713405725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 499342364048754276327733 46813346629570713405725)
                    ·
                      rfl

theorem cell23_273506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_273506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273506 prefixEnd_273506 := by exact prefixLift 273506
  have htrace : WordTrace (prefixWord ++ tailWord_273506) baseStart_273506 baseEnd_273506 := by
    simpa [prefixWord, tailWord_273506, baseEnd_273506] using wordTrace_append hprefix tailTrace_273506
  have hstable : (prefixWord ++ tailWord_273506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273506).length < 2 ^ (prefixWord ++ tailWord_273506).sum := by decide
  have hdescent : baseEnd_273506 < baseStart_273506 := by decide
  rcases family_descends (prefixWord ++ tailWord_273506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273509 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_273509 : Nat := 118140960795 + 273509 * 2 ^ 59
def prefixEnd_273509 : Nat := 4983230072969 + 3 ^ 40 * 273509 * 2
def baseEnd_273509 : Nat := 140441580330675628479661

theorem tailTrace_273509 : CollatzResearch.WordTrace tailWord_273509 prefixEnd_273509 140441580330675628479661 := by
  unfold tailWord_273509
  simp only [CollatzResearch.WordTrace]
  refine ⟨9975692766131079463407581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6650461844087386308938387 9975692766131079463407581)
  ·
    refine ⟨3740884787299154798777843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9975692766131079463407581 3740884787299154798777843)
    ·
      refine ⟨5611327180948732198166765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740884787299154798777843 5611327180948732198166765)
      ·
        refine ⟨2104247692855774574312537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5611327180948732198166765 2104247692855774574312537)
        ·
          refine ⟨1578185769641830930734403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2104247692855774574312537 1578185769641830930734403)
          ·
            refine ⟨2367278654462746396101605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578185769641830930734403 2367278654462746396101605)
            ·
              refine ⟨443864747711764949269051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2367278654462746396101605 443864747711764949269051)
              ·
                refine ⟨665797121567647423903577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443864747711764949269051 665797121567647423903577)
                ·
                  refine ⟨499347841175735567927683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665797121567647423903577 499347841175735567927683)
                  ·
                    refine ⟨749021761763603351891525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 499347841175735567927683 749021761763603351891525)
                    ·
                      refine ⟨140441580330675628479661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 749021761763603351891525 140441580330675628479661)
                      ·
                        rfl

theorem cell23_273509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_273509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273509 prefixEnd_273509 := by exact prefixLift 273509
  have htrace : WordTrace (prefixWord ++ tailWord_273509) baseStart_273509 baseEnd_273509 := by
    simpa [prefixWord, tailWord_273509, baseEnd_273509] using wordTrace_append hprefix tailTrace_273509
  have hstable : (prefixWord ++ tailWord_273509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273509).length < 2 ^ (prefixWord ++ tailWord_273509).sum := by decide
  have hdescent : baseEnd_273509 < baseStart_273509 := by decide
  rcases family_descends (prefixWord ++ tailWord_273509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273522 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_273522 : Nat := 118140960795 + 273522 * 2 ^ 59
def prefixEnd_273522 : Nat := 4983230072969 + 3 ^ 40 * 273522 * 2
def baseEnd_273522 : Nat := 140448255579184077617101

theorem tailTrace_273522 : CollatzResearch.WordTrace tailWord_273522 prefixEnd_273522 140448255579184077617101 := by
  unfold tailWord_273522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494041728770995670907705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6650777943389321789087213 2494041728770995670907705)
  ·
    refine ⟨1870531296578246753180779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2494041728770995670907705 1870531296578246753180779)
    ·
      refine ⟨2805796944867370129771169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870531296578246753180779 2805796944867370129771169)
      ·
        refine ⟨2104347708650527597328377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2805796944867370129771169 2104347708650527597328377)
        ·
          refine ⟨1578260781487895697996283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2104347708650527597328377 1578260781487895697996283)
          ·
            refine ⟨2367391172231843546994425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578260781487895697996283 2367391172231843546994425)
            ·
              refine ⟨1775543379173882660245819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367391172231843546994425 1775543379173882660245819)
              ·
                refine ⟨2663315068760823990368729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775543379173882660245819 2663315068760823990368729)
                ·
                  refine ⟨1997486301570617992776547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2663315068760823990368729 1997486301570617992776547)
                  ·
                    refine ⟨2996229452355926989164821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1997486301570617992776547 2996229452355926989164821)
                    ·
                      refine ⟨140448255579184077617101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2996229452355926989164821 140448255579184077617101)
                      ·
                        rfl

theorem cell23_273522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_273522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273522 prefixEnd_273522 := by exact prefixLift 273522
  have htrace : WordTrace (prefixWord ++ tailWord_273522) baseStart_273522 baseEnd_273522 := by
    simpa [prefixWord, tailWord_273522, baseEnd_273522] using wordTrace_append hprefix tailTrace_273522
  have hstable : (prefixWord ++ tailWord_273522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273522).length < 2 ^ (prefixWord ++ tailWord_273522).sum := by decide
  have hdescent : baseEnd_273522 < baseStart_273522 := by decide
  rcases family_descends (prefixWord ++ tailWord_273522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273526 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_273526 : Nat := 118140960795 + 273526 * 2 ^ 59
def prefixEnd_273526 : Nat := 4983230072969 + 3 ^ 40 * 273526 * 2
def baseEnd_273526 : Nat := 140450309501802061967083

theorem tailTrace_273526 : CollatzResearch.WordTrace tailWord_273526 prefixEnd_273526 140450309501802061967083 := by
  unfold tailWord_273526
  simp only [CollatzResearch.WordTrace]
  refine ⟨623519550441843210423527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6650875204712994244517621 623519550441843210423527)
  ·
    refine ⟨935279325662764815635291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623519550441843210423527 935279325662764815635291)
    ·
      refine ⟨1402918988494147223452937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935279325662764815635291 1402918988494147223452937)
      ·
        refine ⟨1052189241370610417589703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1402918988494147223452937 1052189241370610417589703)
        ·
          refine ⟨1578283862055915626384555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052189241370610417589703 1578283862055915626384555)
          ·
            refine ⟨2367425793083873439576833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578283862055915626384555 2367425793083873439576833)
            ·
              refine ⟨1775569344812905079682625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367425793083873439576833 1775569344812905079682625)
              ·
                refine ⟨1331677008609678809761969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1775569344812905079682625 1331677008609678809761969)
                ·
                  refine ⟨998757756457259107321477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1331677008609678809761969 998757756457259107321477)
                  ·
                    refine ⟨187267079335736082622777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 998757756457259107321477 187267079335736082622777)
                    ·
                      refine ⟨140450309501802061967083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187267079335736082622777 140450309501802061967083)
                      ·
                        rfl

theorem cell23_273526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_273526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273526 prefixEnd_273526 := by exact prefixLift 273526
  have htrace : WordTrace (prefixWord ++ tailWord_273526) baseStart_273526 baseEnd_273526 := by
    simpa [prefixWord, tailWord_273526, baseEnd_273526] using wordTrace_append hprefix tailTrace_273526
  have hstable : (prefixWord ++ tailWord_273526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273526).length < 2 ^ (prefixWord ++ tailWord_273526).sum := by decide
  have hdescent : baseEnd_273526 < baseStart_273526 := by decide
  rcases family_descends (prefixWord ++ tailWord_273526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273570 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_273570 : Nat := 118140960795 + 273570 * 2 ^ 59
def prefixEnd_273570 : Nat := 4983230072969 + 3 ^ 40 * 273570 * 2
def baseEnd_273570 : Nat := 46824300883533296605627

theorem tailTrace_273570 : CollatzResearch.WordTrace tailWord_273570 prefixEnd_273570 46824300883533296605627 := by
  unfold tailWord_273570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494479404727521720344541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6651945079273391254252109 2494479404727521720344541)
  ·
    refine ⟨935429776772820645129203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2494479404727521720344541 935429776772820645129203)
    ·
      refine ⟨1403144665159230967693805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935429776772820645129203 1403144665159230967693805)
      ·
        refine ⟨526179249434711612885177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1403144665159230967693805 526179249434711612885177)
        ·
          refine ⟨394634437076033709663883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526179249434711612885177 394634437076033709663883)
          ·
            refine ⟨591951655614050564495825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394634437076033709663883 591951655614050564495825)
            ·
              refine ⟨443963741710537923371869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591951655614050564495825 443963741710537923371869)
              ·
                refine ⟨166486403141451721264451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 443963741710537923371869 166486403141451721264451)
                ·
                  refine ⟨249729604712177581896677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166486403141451721264451 249729604712177581896677)
                  ·
                    refine ⟨46824300883533296605627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249729604712177581896677 46824300883533296605627)
                    ·
                      rfl

theorem cell23_273570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_273570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273570 prefixEnd_273570 := by exact prefixLift 273570
  have htrace : WordTrace (prefixWord ++ tailWord_273570) baseStart_273570 baseEnd_273570 := by
    simpa [prefixWord, tailWord_273570, baseEnd_273570] using wordTrace_append hprefix tailTrace_273570
  have hstable : (prefixWord ++ tailWord_273570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273570).length < 2 ^ (prefixWord ++ tailWord_273570).sum := by decide
  have hdescent : baseEnd_273570 < baseStart_273570 := by decide
  rcases family_descends (prefixWord ++ tailWord_273570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273593 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 1, 1, 3]
def baseStart_273593 : Nat := 118140960795 + 273593 * 2 ^ 59
def prefixEnd_273593 : Nat := 4983230072969 + 3 ^ 40 * 273593 * 2
def baseEnd_273593 : Nat := 140484712705653299829275

theorem tailTrace_273593 : CollatzResearch.WordTrace tailWord_273593 prefixEnd_273593 140484712705653299829275 := by
  unfold tailWord_273593
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978756497826761809465433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6652504331884507872976955 9978756497826761809465433)
  ·
    refine ⟨7484067373370071357099075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9978756497826761809465433 7484067373370071357099075)
    ·
      refine ⟨11226101060055107035648613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7484067373370071357099075 11226101060055107035648613)
      ·
        refine ⟨2104893948760332569184115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11226101060055107035648613 2104893948760332569184115)
        ·
          refine ⟨3157340923140498853776173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104893948760332569184115 3157340923140498853776173)
          ·
            refine ⟨1184002846177687070166065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3157340923140498853776173 1184002846177687070166065)
            ·
              refine ⟨888002134633265302624549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184002846177687070166065 888002134633265302624549)
              ·
                refine ⟨166500400243737244242103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 888002134633265302624549 166500400243737244242103)
                ·
                  refine ⟨249750600365605866363155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166500400243737244242103 249750600365605866363155)
                  ·
                    refine ⟨374625900548408799544733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249750600365605866363155 374625900548408799544733)
                    ·
                      refine ⟨140484712705653299829275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374625900548408799544733 140484712705653299829275)
                      ·
                        rfl

theorem cell23_273593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_273593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273593 prefixEnd_273593 := by exact prefixLift 273593
  have htrace : WordTrace (prefixWord ++ tailWord_273593) baseStart_273593 baseEnd_273593 := by
    simpa [prefixWord, tailWord_273593, baseEnd_273593] using wordTrace_append hprefix tailTrace_273593
  have hstable : (prefixWord ++ tailWord_273593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273593).length < 2 ^ (prefixWord ++ tailWord_273593).sum := by decide
  have hdescent : baseEnd_273593 < baseStart_273593 := by decide
  rcases family_descends (prefixWord ++ tailWord_273593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273636 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_273636 : Nat := 118140960795 + 273636 * 2 ^ 59
def prefixEnd_273636 : Nat := 4983230072969 + 3 ^ 40 * 273636 * 2
def baseEnd_273636 : Nat := 140506792373796631591577

theorem tailTrace_273636 : CollatzResearch.WordTrace tailWord_273636 prefixEnd_273636 140506792373796631591577 := by
  unfold tailWord_273636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990162418335490076640381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6653549891113986768853841 4990162418335490076640381)
  ·
    refine ⟨1871310906875808778740143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4990162418335490076640381 1871310906875808778740143)
    ·
      refine ⟨2806966360313713168110215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871310906875808778740143 2806966360313713168110215)
      ·
        refine ⟨4210449540470569752165323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806966360313713168110215 4210449540470569752165323)
        ·
          refine ⟨6315674310705854628247985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210449540470569752165323 6315674310705854628247985)
          ·
            refine ⟨4736755733029390971185989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6315674310705854628247985 4736755733029390971185989)
            ·
              refine ⟨888141699943010807097373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4736755733029390971185989 888141699943010807097373)
              ·
                refine ⟨333053137478629052661515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888141699943010807097373 333053137478629052661515)
                ·
                  refine ⟨499579706217943578992273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333053137478629052661515 499579706217943578992273)
                  ·
                    refine ⟨374684779663457684244205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499579706217943578992273 374684779663457684244205)
                    ·
                      refine ⟨140506792373796631591577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374684779663457684244205 140506792373796631591577)
                      ·
                        rfl

theorem cell23_273636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_273636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273636 prefixEnd_273636 := by exact prefixLift 273636
  have htrace : WordTrace (prefixWord ++ tailWord_273636) baseStart_273636 baseEnd_273636 := by
    simpa [prefixWord, tailWord_273636, baseEnd_273636] using wordTrace_append hprefix tailTrace_273636
  have hstable : (prefixWord ++ tailWord_273636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273636).length < 2 ^ (prefixWord ++ tailWord_273636).sum := by decide
  have hdescent : baseEnd_273636 < baseStart_273636 := by decide
  rcases family_descends (prefixWord ++ tailWord_273636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273660 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_273660 : Nat := 118140960795 + 273660 * 2 ^ 59
def prefixEnd_273660 : Nat := 4983230072969 + 3 ^ 40 * 273660 * 2
def baseEnd_273660 : Nat := 46839705303168179230489

theorem tailTrace_273660 : CollatzResearch.WordTrace tailWord_273660 prefixEnd_273660 46839705303168179230489 := by
  unfold tailWord_273660
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990600094292016126077217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6654133459056021501436289 4990600094292016126077217)
  ·
    refine ⟨3742950070719012094557913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4990600094292016126077217 3742950070719012094557913)
    ·
      refine ⟨2807212553039259070918435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3742950070719012094557913 2807212553039259070918435)
      ·
        refine ⟨4210818829558888606377653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807212553039259070918435 4210818829558888606377653)
        ·
          refine ⟨394764265271145806847905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4210818829558888606377653 394764265271145806847905)
          ·
            refine ⟨296073198953359355135929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394764265271145806847905 296073198953359355135929)
            ·
              refine ⟨222054899215019516351947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296073198953359355135929 222054899215019516351947)
              ·
                refine ⟨333082348822529274527921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222054899215019516351947 333082348822529274527921)
                ·
                  refine ⟨249811761616896955895941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333082348822529274527921 249811761616896955895941)
                  ·
                    refine ⟨46839705303168179230489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249811761616896955895941 46839705303168179230489)
                    ·
                      rfl

theorem cell23_273660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_273660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273660 prefixEnd_273660 := by exact prefixLift 273660
  have htrace : WordTrace (prefixWord ++ tailWord_273660) baseStart_273660 baseEnd_273660 := by
    simpa [prefixWord, tailWord_273660, baseEnd_273660] using wordTrace_append hprefix tailTrace_273660
  have hstable : (prefixWord ++ tailWord_273660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273660).length < 2 ^ (prefixWord ++ tailWord_273660).sum := by decide
  have hdescent : baseEnd_273660 < baseStart_273660 := by decide
  rcases family_descends (prefixWord ++ tailWord_273660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273706 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_273706 : Nat := 118140960795 + 273706 * 2 ^ 59
def prefixEnd_273706 : Nat := 4983230072969 + 3 ^ 40 * 273706 * 2
def baseEnd_273706 : Nat := 140542736019611357716255

theorem tailTrace_273706 : CollatzResearch.WordTrace tailWord_273706 prefixEnd_273706 140542736019611357716255 := by
  unfold tailWord_273706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495719486604345527082243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6655251964278254738885981 2495719486604345527082243)
  ·
    refine ⟨3743579229906518290623365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495719486604345527082243 3743579229906518290623365)
    ·
      refine ⟨701921105607472179491881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3743579229906518290623365 701921105607472179491881)
      ·
        refine ⟨526440829205604134618911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701921105607472179491881 526440829205604134618911)
        ·
          refine ⟨789661243808406201928367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526440829205604134618911 789661243808406201928367)
          ·
            refine ⟨1184491865712609302892551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789661243808406201928367 1184491865712609302892551)
            ·
              refine ⟨1776737798568913954338827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184491865712609302892551 1776737798568913954338827)
              ·
                refine ⟨2665106697853370931508241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776737798568913954338827 2665106697853370931508241)
                ·
                  refine ⟨1998830023390028198631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665106697853370931508241 1998830023390028198631181)
                  ·
                    refine ⟨749561258771260574486693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1998830023390028198631181 749561258771260574486693)
                    ·
                      refine ⟨140542736019611357716255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 749561258771260574486693 140542736019611357716255)
                      ·
                        rfl

theorem cell23_273706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_273706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273706 prefixEnd_273706 := by exact prefixLift 273706
  have htrace : WordTrace (prefixWord ++ tailWord_273706) baseStart_273706 baseEnd_273706 := by
    simpa [prefixWord, tailWord_273706, baseEnd_273706] using wordTrace_append hprefix tailTrace_273706
  have hstable : (prefixWord ++ tailWord_273706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273706).length < 2 ^ (prefixWord ++ tailWord_273706).sum := by decide
  have hdescent : baseEnd_273706 < baseStart_273706 := by decide
  rcases family_descends (prefixWord ++ tailWord_273706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273716 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_273716 : Nat := 118140960795 + 273716 * 2 ^ 59
def prefixEnd_273716 : Nat := 4983230072969 + 3 ^ 40 * 273716 * 2
def baseEnd_273716 : Nat := 46849290275385439530403

theorem tailTrace_273716 : CollatzResearch.WordTrace tailWord_273716 prefixEnd_273716 46849290275385439530403 := by
  unfold tailWord_273716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4991621338190576908096501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6655495117587435877462001 4991621338190576908096501)
  ·
    refine ⟨467964500455366585134047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4991621338190576908096501 467964500455366585134047)
    ·
      refine ⟨701946750683049877701071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467964500455366585134047 701946750683049877701071)
      ·
        refine ⟨1052920126024574816551607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701946750683049877701071 1052920126024574816551607)
        ·
          refine ⟨1579380189036862224827411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052920126024574816551607 1579380189036862224827411)
          ·
            refine ⟨2369070283555293337241117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579380189036862224827411 2369070283555293337241117)
            ·
              refine ⟨888401356333235001465419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2369070283555293337241117 888401356333235001465419)
              ·
                refine ⟨1332602034499852502198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888401356333235001465419 1332602034499852502198129)
                ·
                  refine ⟨999451525874889376648597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332602034499852502198129 999451525874889376648597)
                  ·
                    refine ⟨46849290275385439530403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 999451525874889376648597 46849290275385439530403)
                    ·
                      rfl

theorem cell23_273716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_273716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273716 prefixEnd_273716 := by exact prefixLift 273716
  have htrace : WordTrace (prefixWord ++ tailWord_273716) baseStart_273716 baseEnd_273716 := by
    simpa [prefixWord, tailWord_273716, baseEnd_273716] using wordTrace_append hprefix tailTrace_273716
  have hstable : (prefixWord ++ tailWord_273716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273716).length < 2 ^ (prefixWord ++ tailWord_273716).sum := by decide
  have hdescent : baseEnd_273716 < baseStart_273716 := by decide
  rcases family_descends (prefixWord ++ tailWord_273716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273726 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_273726 : Nat := 118140960795 + 273726 * 2 ^ 59
def prefixEnd_273726 : Nat := 4983230072969 + 3 ^ 40 * 273726 * 2
def baseEnd_273726 : Nat := 140553005632701279466163

theorem tailTrace_273726 : CollatzResearch.WordTrace tailWord_273726 prefixEnd_273726 140553005632701279466163 := by
  unfold tailWord_273726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247950925793115690507129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6655738270896617016038021 1247950925793115690507129)
  ·
    refine ⟨935963194344836767880347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1247950925793115690507129 935963194344836767880347)
    ·
      refine ⟨1403944791517255151820521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935963194344836767880347 1403944791517255151820521)
      ·
        refine ⟨1052958593637941363865391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1403944791517255151820521 1052958593637941363865391)
        ·
          refine ⟨1579437890456912045798087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052958593637941363865391 1579437890456912045798087)
          ·
            refine ⟨2369156835685368068697131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579437890456912045798087 2369156835685368068697131)
            ·
              refine ⟨3553735253528052103045697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369156835685368068697131 3553735253528052103045697)
              ·
                refine ⟨2665301440146039077284273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3553735253528052103045697 2665301440146039077284273)
                ·
                  refine ⟨1998976080109529307963205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665301440146039077284273 1998976080109529307963205)
                  ·
                    refine ⟨374808015020536745243101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998976080109529307963205 374808015020536745243101)
                    ·
                      refine ⟨140553005632701279466163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 374808015020536745243101 140553005632701279466163)
                      ·
                        rfl

theorem cell23_273726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_273726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273726 prefixEnd_273726 := by exact prefixLift 273726
  have htrace : WordTrace (prefixWord ++ tailWord_273726) baseStart_273726 baseEnd_273726 := by
    simpa [prefixWord, tailWord_273726, baseEnd_273726] using wordTrace_append hprefix tailTrace_273726
  have hstable : (prefixWord ++ tailWord_273726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273726).length < 2 ^ (prefixWord ++ tailWord_273726).sum := by decide
  have hdescent : baseEnd_273726 < baseStart_273726 := by decide
  rcases family_descends (prefixWord ++ tailWord_273726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273759 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 4, 5]
def baseStart_273759 : Nat := 118140960795 + 273759 * 2 ^ 59
def prefixEnd_273759 : Nat := 4983230072969 + 3 ^ 40 * 273759 * 2
def baseEnd_273759 : Nat := 46856650164766550117837

theorem tailTrace_273759 : CollatzResearch.WordTrace tailWord_273759 prefixEnd_273759 46856650164766550117837 := by
  unfold tailWord_273759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9984811015225372160008331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6656540676816914773338887 9984811015225372160008331)
  ·
    refine ⟨14977216522838058240012497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9984811015225372160008331 14977216522838058240012497)
    ·
      refine ⟨11232912392128543680009373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14977216522838058240012497 11232912392128543680009373)
      ·
        refine ⟨4212342147048203880003515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11232912392128543680009373 4212342147048203880003515)
        ·
          refine ⟨6318513220572305820005273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212342147048203880003515 6318513220572305820005273)
          ·
            refine ⟨4738884915429229365003955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6318513220572305820005273 4738884915429229365003955)
            ·
              refine ⟨7108327373143844047505933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4738884915429229365003955 7108327373143844047505933)
              ·
                refine ⟨2665622764928941517814725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7108327373143844047505933 2665622764928941517814725)
                ·
                  refine ⟨499804268424176534590261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2665622764928941517814725 499804268424176534590261)
                  ·
                    refine ⟨46856650164766550117837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 499804268424176534590261 46856650164766550117837)
                    ·
                      rfl

theorem cell23_273759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_273759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273759 prefixEnd_273759 := by exact prefixLift 273759
  have htrace : WordTrace (prefixWord ++ tailWord_273759) baseStart_273759 baseEnd_273759 := by
    simpa [prefixWord, tailWord_273759, baseEnd_273759] using wordTrace_append hprefix tailTrace_273759
  have hstable : (prefixWord ++ tailWord_273759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273759).length < 2 ^ (prefixWord ++ tailWord_273759).sum := by decide
  have hdescent : baseEnd_273759 < baseStart_273759 := by decide
  rcases family_descends (prefixWord ++ tailWord_273759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273774 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_273774 : Nat := 118140960795 + 273774 * 2 ^ 59
def prefixEnd_273774 : Nat := 4983230072969 + 3 ^ 40 * 273774 * 2
def baseEnd_273774 : Nat := 140577652704117091665943

theorem tailTrace_273774 : CollatzResearch.WordTrace tailWord_273774 prefixEnd_273774 140577652704117091665943 := by
  unfold tailWord_273774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248169763771378715225547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6656905406780686481202917 1248169763771378715225547)
  ·
    refine ⟨1872254645657068072838321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1248169763771378715225547 1872254645657068072838321)
    ·
      refine ⟨1404190984242801054628741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1872254645657068072838321 1404190984242801054628741)
      ·
        refine ⟨263285809545525197742889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1404190984242801054628741 263285809545525197742889)
        ·
          refine ⟨197464357159143898307167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263285809545525197742889 197464357159143898307167)
          ·
            refine ⟨296196535738715847460751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197464357159143898307167 296196535738715847460751)
            ·
              refine ⟨444294803608073771191127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296196535738715847460751 444294803608073771191127)
              ·
                refine ⟨666442205412110656786691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444294803608073771191127 666442205412110656786691)
                ·
                  refine ⟨999663308118165985180037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666442205412110656786691 999663308118165985180037)
                  ·
                    refine ⟨187436870272156122221257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 999663308118165985180037 187436870272156122221257)
                    ·
                      refine ⟨140577652704117091665943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187436870272156122221257 140577652704117091665943)
                      ·
                        rfl

theorem cell23_273774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_273774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273774 prefixEnd_273774 := by exact prefixLift 273774
  have htrace : WordTrace (prefixWord ++ tailWord_273774) baseStart_273774 baseEnd_273774 := by
    simpa [prefixWord, tailWord_273774, baseEnd_273774] using wordTrace_append hprefix tailTrace_273774
  have hstable : (prefixWord ++ tailWord_273774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273774).length < 2 ^ (prefixWord ++ tailWord_273774).sum := by decide
  have hdescent : baseEnd_273774 < baseStart_273774 := by decide
  rcases family_descends (prefixWord ++ tailWord_273774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273789 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_273789 : Nat := 118140960795 + 273789 * 2 ^ 59
def prefixEnd_273789 : Nat := 4983230072969 + 3 ^ 40 * 273789 * 2
def baseEnd_273789 : Nat := 46861784971311510992791

theorem tailTrace_273789 : CollatzResearch.WordTrace tailWord_273789 prefixEnd_273789 46861784971311510992791 := by
  unfold tailWord_273789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985905205116687283600421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6657270136744458189066947 9985905205116687283600421)
  ·
    refine ⟨1872357225959378865675079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9985905205116687283600421 1872357225959378865675079)
    ·
      refine ⟨2808535838939068298512619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872357225959378865675079 2808535838939068298512619)
      ·
        refine ⟨4212803758408602447768929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808535838939068298512619 4212803758408602447768929)
        ·
          refine ⟨3159602818806451835826697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4212803758408602447768929 3159602818806451835826697)
          ·
            refine ⟨2369702114104838876870023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159602818806451835826697 2369702114104838876870023)
            ·
              refine ⟨3554553171157258315305035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369702114104838876870023 3554553171157258315305035)
              ·
                refine ⟨5331829756735887472957553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554553171157258315305035 5331829756735887472957553)
                ·
                  refine ⟨3998872317551915604718165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5331829756735887472957553 3998872317551915604718165)
                  ·
                    refine ⟨46861784971311510992791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3998872317551915604718165 46861784971311510992791)
                    ·
                      rfl

theorem cell23_273789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_273789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273789 prefixEnd_273789 := by exact prefixLift 273789
  have htrace : WordTrace (prefixWord ++ tailWord_273789) baseStart_273789 baseEnd_273789 := by
    simpa [prefixWord, tailWord_273789, baseEnd_273789] using wordTrace_append hprefix tailTrace_273789
  have hstable : (prefixWord ++ tailWord_273789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273789).length < 2 ^ (prefixWord ++ tailWord_273789).sum := by decide
  have hdescent : baseEnd_273789 < baseStart_273789 := by decide
  rcases family_descends (prefixWord ++ tailWord_273789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273796 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_273796 : Nat := 118140960795 + 273796 * 2 ^ 59
def prefixEnd_273796 : Nat := 4983230072969 + 3 ^ 40 * 273796 * 2
def baseEnd_273796 : Nat := 140588949278516005590841

theorem tailTrace_273796 : CollatzResearch.WordTrace tailWord_273796 prefixEnd_273796 140588949278516005590841 := by
  unfold tailWord_273796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993080258045663739552621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6657440344060884986070161 4993080258045663739552621)
  ·
    refine ⟨1872405096767123902332233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4993080258045663739552621 1872405096767123902332233)
    ·
      refine ⟨1404303822575342926749175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1872405096767123902332233 1404303822575342926749175)
      ·
        refine ⟨2106455733863014390123763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404303822575342926749175 2106455733863014390123763)
        ·
          refine ⟨3159683600794521585185645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106455733863014390123763 3159683600794521585185645)
          ·
            refine ⟨1184881350297945594444617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3159683600794521585185645 1184881350297945594444617)
            ·
              refine ⟨888661012723459195833463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184881350297945594444617 888661012723459195833463)
              ·
                refine ⟨1332991519085188793750195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888661012723459195833463 1332991519085188793750195)
                ·
                  refine ⟨1999487278627783190625293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332991519085188793750195 1999487278627783190625293)
                  ·
                    refine ⟨749807729485418696484485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1999487278627783190625293 749807729485418696484485)
                    ·
                      refine ⟨140588949278516005590841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 749807729485418696484485 140588949278516005590841)
                      ·
                        rfl

theorem cell23_273796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_273796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273796 prefixEnd_273796 := by exact prefixLift 273796
  have htrace : WordTrace (prefixWord ++ tailWord_273796) baseStart_273796 baseEnd_273796 := by
    simpa [prefixWord, tailWord_273796, baseEnd_273796] using wordTrace_append hprefix tailTrace_273796
  have hstable : (prefixWord ++ tailWord_273796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273796).length < 2 ^ (prefixWord ++ tailWord_273796).sum := by decide
  have hdescent : baseEnd_273796 < baseStart_273796 := by decide
  rcases family_descends (prefixWord ++ tailWord_273796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273809 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_273809 : Nat := 118140960795 + 273809 * 2 ^ 59
def prefixEnd_273809 : Nat := 4983230072969 + 3 ^ 40 * 273809 * 2
def baseEnd_273809 : Nat := 140595624527024454728281

theorem tailTrace_273809 : CollatzResearch.WordTrace tailWord_273809 prefixEnd_273809 140595624527024454728281 := by
  unfold tailWord_273809
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986634665044230699328481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6657756443362820466218987 9986634665044230699328481)
  ·
    refine ⟨7489975998783173024496361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9986634665044230699328481 7489975998783173024496361)
    ·
      refine ⟨5617481999087379768372271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7489975998783173024496361 5617481999087379768372271)
      ·
        refine ⟨8426222998631069652558407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5617481999087379768372271 8426222998631069652558407)
        ·
          refine ⟨12639334497946604478837611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8426222998631069652558407 12639334497946604478837611)
          ·
            refine ⟨18959001746919906718256417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12639334497946604478837611 18959001746919906718256417)
            ·
              refine ⟨14219251310189930038692313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18959001746919906718256417 14219251310189930038692313)
              ·
                refine ⟨10664438482642447529019235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14219251310189930038692313 10664438482642447529019235)
                ·
                  refine ⟨15996657723963671293528853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10664438482642447529019235 15996657723963671293528853)
                  ·
                    refine ⟨749843330810797091884165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15996657723963671293528853 749843330810797091884165)
                    ·
                      refine ⟨140595624527024454728281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 749843330810797091884165 140595624527024454728281)
                      ·
                        rfl

theorem cell23_273809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_273809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273809 prefixEnd_273809 := by exact prefixLift 273809
  have htrace : WordTrace (prefixWord ++ tailWord_273809) baseStart_273809 baseEnd_273809 := by
    simpa [prefixWord, tailWord_273809, baseEnd_273809] using wordTrace_append hprefix tailTrace_273809
  have hstable : (prefixWord ++ tailWord_273809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273809).length < 2 ^ (prefixWord ++ tailWord_273809).sum := by decide
  have hdescent : baseEnd_273809 < baseStart_273809 := by decide
  rcases family_descends (prefixWord ++ tailWord_273809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273810 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_273810 : Nat := 118140960795 + 273810 * 2 ^ 59
def prefixEnd_273810 : Nat := 4983230072969 + 3 ^ 40 * 273810 * 2
def baseEnd_273810 : Nat := 46865379335892983605259

theorem tailTrace_273810 : CollatzResearch.WordTrace tailWord_273810 prefixEnd_273810 46865379335892983605259 := by
  unfold tailWord_273810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496667784510151967528721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6657780758693738580076589 2496667784510151967528721)
  ·
    refine ⟨1872500838382613975646541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2496667784510151967528721 1872500838382613975646541)
    ·
      refine ⟨702187814393480240867453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1872500838382613975646541 702187814393480240867453)
      ·
        refine ⟨263320430397555090325295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 702187814393480240867453 263320430397555090325295)
        ·
          refine ⟨394980645596332635487943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263320430397555090325295 394980645596332635487943)
          ·
            refine ⟨592470968394498953231915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394980645596332635487943 592470968394498953231915)
            ·
              refine ⟨888706452591748429847873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592470968394498953231915 888706452591748429847873)
              ·
                refine ⟨666529839443811322385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888706452591748429847873 666529839443811322385905)
                ·
                  refine ⟨499897379582858491789429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666529839443811322385905 499897379582858491789429)
                  ·
                    refine ⟨46865379335892983605259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 499897379582858491789429 46865379335892983605259)
                    ·
                      rfl

theorem cell23_273810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_273810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273810 prefixEnd_273810 := by exact prefixLift 273810
  have htrace : WordTrace (prefixWord ++ tailWord_273810) baseStart_273810 baseEnd_273810 := by
    simpa [prefixWord, tailWord_273810, baseEnd_273810] using wordTrace_append hprefix tailTrace_273810
  have hstable : (prefixWord ++ tailWord_273810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273810).length < 2 ^ (prefixWord ++ tailWord_273810).sum := by decide
  have hdescent : baseEnd_273810 < baseStart_273810 := by decide
  rcases family_descends (prefixWord ++ tailWord_273810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273823 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 3, 4]
def baseStart_273823 : Nat := 118140960795 + 273823 * 2 ^ 59
def prefixEnd_273823 : Nat := 4983230072969 + 3 ^ 40 * 273823 * 2
def baseEnd_273823 : Nat := 46867604418729133317739

theorem tailTrace_273823 : CollatzResearch.WordTrace tailWord_273823 prefixEnd_273823 46867604418729133317739 := by
  unfold tailWord_273823
  simp only [CollatzResearch.WordTrace]
  refine ⟨9987145286993511090338123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6658096857995674060225415 9987145286993511090338123)
  ·
    refine ⟨14980717930490266635507185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9987145286993511090338123 14980717930490266635507185)
    ·
      refine ⟨11235538447867699976630389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14980717930490266635507185 11235538447867699976630389)
      ·
        refine ⟨1053331729487596872809099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11235538447867699976630389 1053331729487596872809099)
        ·
          refine ⟨1579997594231395309213649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053331729487596872809099 1579997594231395309213649)
          ·
            refine ⟨1184998195673546481910237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579997594231395309213649 1184998195673546481910237)
            ·
              refine ⟨444374323377579930716339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1184998195673546481910237 444374323377579930716339)
              ·
                refine ⟨666561485066369896074509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444374323377579930716339 666561485066369896074509)
                ·
                  refine ⟨249960556899888711027941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666561485066369896074509 249960556899888711027941)
                  ·
                    refine ⟨46867604418729133317739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249960556899888711027941 46867604418729133317739)
                    ·
                      rfl

theorem cell23_273823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_273823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273823 prefixEnd_273823 := by exact prefixLift 273823
  have htrace : WordTrace (prefixWord ++ tailWord_273823) baseStart_273823 baseEnd_273823 := by
    simpa [prefixWord, tailWord_273823, baseEnd_273823] using wordTrace_append hprefix tailTrace_273823
  have hstable : (prefixWord ++ tailWord_273823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273823).length < 2 ^ (prefixWord ++ tailWord_273823).sum := by decide
  have hdescent : baseEnd_273823 < baseStart_273823 := by decide
  rcases family_descends (prefixWord ++ tailWord_273823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273839 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_273839 : Nat := 118140960795 + 273839 * 2 ^ 59
def prefixEnd_273839 : Nat := 4983230072969 + 3 ^ 40 * 273839 * 2
def baseEnd_273839 : Nat := 140611028946659337353143

theorem tailTrace_273839 : CollatzResearch.WordTrace tailWord_273839 prefixEnd_273839 140611028946659337353143 := by
  unfold tailWord_273839
  simp only [CollatzResearch.WordTrace]
  refine ⟨9987728854935545822920571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6658485903290363881947047 9987728854935545822920571)
  ·
    refine ⟨14981593282403318734380857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9987728854935545822920571 14981593282403318734380857)
    ·
      refine ⟨11236194961802489050785643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14981593282403318734380857 11236194961802489050785643)
      ·
        refine ⟨16854292442703733576178465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11236194961802489050785643 16854292442703733576178465)
        ·
          refine ⟨12640719332027800182133849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16854292442703733576178465 12640719332027800182133849)
          ·
            refine ⟨9480539499020850136600387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12640719332027800182133849 9480539499020850136600387)
            ·
              refine ⟨14220809248531275204900581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9480539499020850136600387 14220809248531275204900581)
              ·
                refine ⟨2666401734099614100918859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14220809248531275204900581 2666401734099614100918859)
                ·
                  refine ⟨3999602601149421151378289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666401734099614100918859 3999602601149421151378289)
                  ·
                    refine ⟨2999701950862065863533717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999602601149421151378289 2999701950862065863533717)
                    ·
                      refine ⟨140611028946659337353143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2999701950862065863533717 140611028946659337353143)
                      ·
                        rfl

theorem cell23_273839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_273839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273839 prefixEnd_273839 := by exact prefixLift 273839
  have htrace : WordTrace (prefixWord ++ tailWord_273839) baseStart_273839 baseEnd_273839 := by
    simpa [prefixWord, tailWord_273839, baseEnd_273839] using wordTrace_append hprefix tailTrace_273839
  have hstable : (prefixWord ++ tailWord_273839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273839).length < 2 ^ (prefixWord ++ tailWord_273839).sum := by decide
  have hdescent : baseEnd_273839 < baseStart_273839 := by decide
  rcases family_descends (prefixWord ++ tailWord_273839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273930 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_273930 : Nat := 118140960795 + 273930 * 2 ^ 59
def prefixEnd_273930 : Nat := 4983230072969 + 3 ^ 40 * 273930 * 2
def baseEnd_273930 : Nat := 46885918562072827105075

theorem tailTrace_273930 : CollatzResearch.WordTrace tailWord_273930 prefixEnd_273930 46885918562072827105075 := by
  unfold tailWord_273930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2497761974401467091120811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6660698598403912242988829 2497761974401467091120811)
  ·
    refine ⟨3746642961602200636681217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2497761974401467091120811 3746642961602200636681217)
    ·
      refine ⟨2809982221201650477510913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3746642961602200636681217 2809982221201650477510913)
      ·
        refine ⟨2107486665901237858133185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2809982221201650477510913 2107486665901237858133185)
        ·
          refine ⟨1580614999425928393599889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2107486665901237858133185 1580614999425928393599889)
          ·
            refine ⟨1185461249569446295199917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1580614999425928393599889 1185461249569446295199917)
            ·
              refine ⟨444547968588542360699969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1185461249569446295199917 444547968588542360699969)
              ·
                refine ⟨333410976441406770524977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444547968588542360699969 333410976441406770524977)
                ·
                  refine ⟨250058232331055077893733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333410976441406770524977 250058232331055077893733)
                  ·
                    refine ⟨46885918562072827105075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250058232331055077893733 46885918562072827105075)
                    ·
                      rfl

theorem cell23_273930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_273930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273930 prefixEnd_273930 := by exact prefixLift 273930
  have htrace : WordTrace (prefixWord ++ tailWord_273930) baseStart_273930 baseEnd_273930 := by
    simpa [prefixWord, tailWord_273930, baseEnd_273930] using wordTrace_append hprefix tailTrace_273930
  have hstable : (prefixWord ++ tailWord_273930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273930).length < 2 ^ (prefixWord ++ tailWord_273930).sum := by decide
  have hdescent : baseEnd_273930 < baseStart_273930 := by decide
  rcases family_descends (prefixWord ++ tailWord_273930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273937 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 1, 2, 2]
def baseStart_273937 : Nat := 118140960795 + 273937 * 2 ^ 59
def prefixEnd_273937 : Nat := 4983230072969 + 3 ^ 40 * 273937 * 2
def baseEnd_273937 : Nat := 140661350050799953927693

theorem tailTrace_273937 : CollatzResearch.WordTrace tailWord_273937 prefixEnd_273937 140661350050799953927693 := by
  unfold tailWord_273937
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991303208580508559988065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6660868805720339039992043 9991303208580508559988065)
  ·
    refine ⟨7493477406435381419991049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9991303208580508559988065 7493477406435381419991049)
    ·
      refine ⟨5620108054826536064993287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7493477406435381419991049 5620108054826536064993287)
      ·
        refine ⟨8430162082239804097489931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620108054826536064993287 8430162082239804097489931)
        ·
          refine ⟨12645243123359706146234897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430162082239804097489931 12645243123359706146234897)
          ·
            refine ⟨9483932342519779609676173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12645243123359706146234897 9483932342519779609676173)
            ·
              refine ⟨3556474628444917353628565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9483932342519779609676173 3556474628444917353628565)
              ·
                refine ⟨166709748208355500951339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3556474628444917353628565 166709748208355500951339)
                ·
                  refine ⟨250064622312533251427009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166709748208355500951339 250064622312533251427009)
                  ·
                    refine ⟨187548466734399938570257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250064622312533251427009 187548466734399938570257)
                    ·
                      refine ⟨140661350050799953927693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187548466734399938570257 140661350050799953927693)
                      ·
                        rfl

theorem cell23_273937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_273937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_273937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_273937 prefixEnd_273937 := by exact prefixLift 273937
  have htrace : WordTrace (prefixWord ++ tailWord_273937) baseStart_273937 baseEnd_273937 := by
    simpa [prefixWord, tailWord_273937, baseEnd_273937] using wordTrace_append hprefix tailTrace_273937
  have hstable : (prefixWord ++ tailWord_273937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273937).length < 2 ^ (prefixWord ++ tailWord_273937).sum := by decide
  have hdescent : baseEnd_273937 < baseStart_273937 := by decide
  rcases family_descends (prefixWord ++ tailWord_273937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274016 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 9]
def baseStart_274016 : Nat := 118140960795 + 274016 * 2 ^ 59
def prefixEnd_274016 : Nat := 4983230072969 + 3 ^ 40 * 274016 * 2
def baseEnd_274016 : Nat := 15633546113611682759981

theorem tailTrace_274016 : CollatzResearch.WordTrace tailWord_274016 prefixEnd_274016 15633546113611682759981 := by
  unfold tailWord_274016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997092287647152526056951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6662789716862870034742601 4997092287647152526056951)
  ·
    refine ⟨7495638431470728789085427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4997092287647152526056951 7495638431470728789085427)
    ·
      refine ⟨11243457647206093183628141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7495638431470728789085427 11243457647206093183628141)
      ·
        refine ⟨4216296617702284943860553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11243457647206093183628141 4216296617702284943860553)
        ·
          refine ⟨3162222463276713707895415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4216296617702284943860553 3162222463276713707895415)
          ·
            refine ⟨4743333694915070561843123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162222463276713707895415 4743333694915070561843123)
            ·
              refine ⟨7115000542372605842764685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4743333694915070561843123 7115000542372605842764685)
              ·
                refine ⟨2668125203389727191036757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7115000542372605842764685 2668125203389727191036757)
                ·
                  refine ⟨15633546113611682759981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2668125203389727191036757 15633546113611682759981)
                  ·
                    rfl

theorem cell23_274016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_274016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274016 prefixEnd_274016 := by exact prefixLift 274016
  have htrace : WordTrace (prefixWord ++ tailWord_274016) baseStart_274016 baseEnd_274016 := by
    simpa [prefixWord, tailWord_274016, baseEnd_274016] using wordTrace_append hprefix tailTrace_274016
  have hstable : (prefixWord ++ tailWord_274016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274016).length < 2 ^ (prefixWord ++ tailWord_274016).sum := by decide
  have hdescent : baseEnd_274016 < baseStart_274016 := by decide
  rcases family_descends (prefixWord ++ tailWord_274016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274043 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3]
def baseStart_274043 : Nat := 118140960795 + 274043 * 2 ^ 59
def prefixEnd_274043 : Nat := 4983230072969 + 3 ^ 40 * 274043 * 2
def baseEnd_274043 : Nat := 140715779000176539202205

theorem tailTrace_274043 : CollatzResearch.WordTrace tailWord_274043 prefixEnd_274043 140715779000176539202205 := by
  unfold tailWord_274043
  simp only [CollatzResearch.WordTrace]
  refine ⟨9995169346196488663346783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6663446230797659108897855 9995169346196488663346783)
  ·
    refine ⟨14992754019294732995020175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9995169346196488663346783 14992754019294732995020175)
    ·
      refine ⟨22489131028942099492530263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14992754019294732995020175 22489131028942099492530263)
      ·
        refine ⟨33733696543413149238795395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22489131028942099492530263 33733696543413149238795395)
        ·
          refine ⟨50600544815119723858193093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33733696543413149238795395 50600544815119723858193093)
          ·
            refine ⟨9487602152834948223411205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50600544815119723858193093 9487602152834948223411205)
            ·
              refine ⟨1778925403656552791889601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9487602152834948223411205 1778925403656552791889601)
              ·
                refine ⟨1334194052742414593917201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778925403656552791889601 1334194052742414593917201)
                ·
                  refine ⟨1000645539556810945437901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334194052742414593917201 1000645539556810945437901)
                  ·
                    refine ⟨375242077333804104539213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000645539556810945437901 375242077333804104539213)
                    ·
                      refine ⟨140715779000176539202205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375242077333804104539213 140715779000176539202205)
                      ·
                        rfl

theorem cell23_274043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 3].length) (baseStart_274043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274043 prefixEnd_274043 := by exact prefixLift 274043
  have htrace : WordTrace (prefixWord ++ tailWord_274043) baseStart_274043 baseEnd_274043 := by
    simpa [prefixWord, tailWord_274043, baseEnd_274043] using wordTrace_append hprefix tailTrace_274043
  have hstable : (prefixWord ++ tailWord_274043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274043).length < 2 ^ (prefixWord ++ tailWord_274043).sum := by decide
  have hdescent : baseEnd_274043 < baseStart_274043 := by decide
  rcases family_descends (prefixWord ++ tailWord_274043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274080 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_274080 : Nat := 118140960795 + 274080 * 2 ^ 59
def prefixEnd_274080 : Nat := 4983230072969 + 3 ^ 40 * 274080 * 2
def baseEnd_274080 : Nat := 46911592594797631479845

theorem tailTrace_274080 : CollatzResearch.WordTrace tailWord_274080 prefixEnd_274080 46911592594797631479845 := by
  unfold tailWord_274080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998259423531221991221847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6664345898041629321629129 4998259423531221991221847)
  ·
    refine ⟨7497389135296832986832771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4998259423531221991221847 7497389135296832986832771)
    ·
      refine ⟨11246083702945249480249157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7497389135296832986832771 11246083702945249480249157)
      ·
        refine ⟨2108640694302234277546717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11246083702945249480249157 2108640694302234277546717)
        ·
          refine ⟨790740260363337854080019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2108640694302234277546717 790740260363337854080019)
          ·
            refine ⟨1186110390545006781120029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790740260363337854080019 1186110390545006781120029)
            ·
              refine ⟨444791396454377542920011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1186110390545006781120029 444791396454377542920011)
              ·
                refine ⟨667187094681566314380017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444791396454377542920011 667187094681566314380017)
                ·
                  refine ⟨500390321011174735785013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667187094681566314380017 500390321011174735785013)
                  ·
                    refine ⟨46911592594797631479845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 500390321011174735785013 46911592594797631479845)
                    ·
                      rfl

theorem cell23_274080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_274080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274080 prefixEnd_274080 := by exact prefixLift 274080
  have htrace : WordTrace (prefixWord ++ tailWord_274080) baseStart_274080 baseEnd_274080 := by
    simpa [prefixWord, tailWord_274080, baseEnd_274080] using wordTrace_append hprefix tailTrace_274080
  have hstable : (prefixWord ++ tailWord_274080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274080).length < 2 ^ (prefixWord ++ tailWord_274080).sum := by decide
  have hdescent : baseEnd_274080 < baseStart_274080 := by decide
  rcases family_descends (prefixWord ++ tailWord_274080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274083 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_274083 : Nat := 118140960795 + 274083 * 2 ^ 59
def prefixEnd_274083 : Nat := 4983230072969 + 3 ^ 40 * 274083 * 2
def baseEnd_274083 : Nat := 140736318226356382702021

theorem tailTrace_274083 : CollatzResearch.WordTrace tailWord_274083 prefixEnd_274083 140736318226356382702021 := by
  unfold tailWord_274083
  simp only [CollatzResearch.WordTrace]
  refine ⟨9996628266051575494802903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6664418844034383663201935 9996628266051575494802903)
  ·
    refine ⟨14994942399077363242204355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9996628266051575494802903 14994942399077363242204355)
    ·
      refine ⟨22492413598616044863306533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14994942399077363242204355 22492413598616044863306533)
      ·
        refine ⟨4217327549740508411869975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22492413598616044863306533 4217327549740508411869975)
        ·
          refine ⟨6325991324610762617804963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217327549740508411869975 6325991324610762617804963)
          ·
            refine ⟨9488986986916143926707445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6325991324610762617804963 9488986986916143926707445)
            ·
              refine ⟨889592530023388493128823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9488986986916143926707445 889592530023388493128823)
              ·
                refine ⟨1334388795035082739693235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889592530023388493128823 1334388795035082739693235)
                ·
                  refine ⟨2001583192552624109539853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334388795035082739693235 2001583192552624109539853)
                  ·
                    refine ⟨750593697207234041077445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001583192552624109539853 750593697207234041077445)
                    ·
                      refine ⟨140736318226356382702021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 750593697207234041077445 140736318226356382702021)
                      ·
                        rfl

theorem cell23_274083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_274083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274083 prefixEnd_274083 := by exact prefixLift 274083
  have htrace : WordTrace (prefixWord ++ tailWord_274083) baseStart_274083 baseEnd_274083 := by
    simpa [prefixWord, tailWord_274083, baseEnd_274083] using wordTrace_append hprefix tailTrace_274083
  have hstable : (prefixWord ++ tailWord_274083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274083).length < 2 ^ (prefixWord ++ tailWord_274083).sum := by decide
  have hdescent : baseEnd_274083 < baseStart_274083 := by decide
  rcases family_descends (prefixWord ++ tailWord_274083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274123 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 6]
def baseStart_274123 : Nat := 118140960795 + 274123 * 2 ^ 59
def prefixEnd_274123 : Nat := 4983230072969 + 3 ^ 40 * 274123 * 2
def baseEnd_274123 : Nat := 15639650828059580689093

theorem tailTrace_274123 : CollatzResearch.WordTrace tailWord_274123 prefixEnd_274123 15639650828059580689093 := by
  unfold tailWord_274123
  simp only [CollatzResearch.WordTrace]
  refine ⟨9998087185906662326259023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6665391457271108217506015 9998087185906662326259023)
  ·
    refine ⟨14997130778859993489388535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9998087185906662326259023 14997130778859993489388535)
    ·
      refine ⟨22495696168289990234082803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14997130778859993489388535 22495696168289990234082803)
      ·
        refine ⟨33743544252434985351124205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22495696168289990234082803 33743544252434985351124205)
        ·
          refine ⟨12653829094663119506671577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33743544252434985351124205 12653829094663119506671577)
          ·
            refine ⟨9490371820997339630003683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12653829094663119506671577 9490371820997339630003683)
            ·
              refine ⟨14235557731496009445005525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9490371820997339630003683 14235557731496009445005525)
              ·
                refine ⟨333645884331937721367317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14235557731496009445005525 333645884331937721367317)
                ·
                  refine ⟨15639650828059580689093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 333645884331937721367317 15639650828059580689093)
                  ·
                    rfl

theorem cell23_274123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 6].length) (baseStart_274123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274123 prefixEnd_274123 := by exact prefixLift 274123
  have htrace : WordTrace (prefixWord ++ tailWord_274123) baseStart_274123 baseEnd_274123 := by
    simpa [prefixWord, tailWord_274123, baseEnd_274123] using wordTrace_append hprefix tailTrace_274123
  have hstable : (prefixWord ++ tailWord_274123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274123).length < 2 ^ (prefixWord ++ tailWord_274123).sum := by decide
  have hdescent : baseEnd_274123 < baseStart_274123 := by decide
  rcases family_descends (prefixWord ++ tailWord_274123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274153 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_274153 : Nat := 118140960795 + 274153 * 2 ^ 59
def prefixEnd_274153 : Nat := 4983230072969 + 3 ^ 40 * 274153 * 2
def baseEnd_274153 : Nat := 46924087290723702942233

theorem tailTrace_274153 : CollatzResearch.WordTrace tailWord_274153 prefixEnd_274153 46924087290723702942233 := by
  unfold tailWord_274153
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999181375797977449851113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6666120917198651633234075 9999181375797977449851113)
  ·
    refine ⟨7499386031848483087388335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9999181375797977449851113 7499386031848483087388335)
    ·
      refine ⟨11249079047772724631082503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7499386031848483087388335 11249079047772724631082503)
      ·
        refine ⟨16873618571659086946623755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249079047772724631082503 16873618571659086946623755)
        ·
          refine ⟨25310427857488630419935633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16873618571659086946623755 25310427857488630419935633)
          ·
            refine ⟨18982820893116472814951725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25310427857488630419935633 18982820893116472814951725)
            ·
              refine ⟨7118557834918677305606897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18982820893116472814951725 7118557834918677305606897)
              ·
                refine ⟨5338918376189007979205173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118557834918677305606897 5338918376189007979205173)
                ·
                  refine ⟨500523597767719498050485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5338918376189007979205173 500523597767719498050485)
                  ·
                    refine ⟨46924087290723702942233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 500523597767719498050485 46924087290723702942233)
                    ·
                      rfl

theorem cell23_274153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_274153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274153 prefixEnd_274153 := by exact prefixLift 274153
  have htrace : WordTrace (prefixWord ++ tailWord_274153) baseStart_274153 baseEnd_274153 := by
    simpa [prefixWord, tailWord_274153, baseEnd_274153] using wordTrace_append hprefix tailTrace_274153
  have hstable : (prefixWord ++ tailWord_274153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274153).length < 2 ^ (prefixWord ++ tailWord_274153).sum := by decide
  have hdescent : baseEnd_274153 < baseStart_274153 := by decide
  rcases family_descends (prefixWord ++ tailWord_274153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274160 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2]
def baseStart_274160 : Nat := 118140960795 + 274160 * 2 ^ 59
def prefixEnd_274160 : Nat := 4983230072969 + 3 ^ 40 * 274160 * 2
def baseEnd_274160 : Nat := 140775856236752581439167

theorem tailTrace_274160 : CollatzResearch.WordTrace tailWord_274160 prefixEnd_274160 140775856236752581439167 := by
  unfold tailWord_274160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999718343386308822677967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6666291124515078430237289 4999718343386308822677967)
  ·
    refine ⟨7499577515079463234016951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4999718343386308822677967 7499577515079463234016951)
    ·
      refine ⟨11249366272619194851025427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7499577515079463234016951 11249366272619194851025427)
      ·
        refine ⟨16874049408928792276538141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249366272619194851025427 16874049408928792276538141)
        ·
          refine ⟨6327768528348297103701803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16874049408928792276538141 6327768528348297103701803)
          ·
            refine ⟨9491652792522445655552705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327768528348297103701803 9491652792522445655552705)
            ·
              refine ⟨7118739594391834241664529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9491652792522445655552705 7118739594391834241664529)
              ·
                refine ⟨5339054695793875681248397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118739594391834241664529 5339054695793875681248397)
                ·
                  refine ⟨2002145510922703380468149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5339054695793875681248397 2002145510922703380468149)
                  ·
                    refine ⟨187701141649003441918889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2002145510922703380468149 187701141649003441918889)
                    ·
                      refine ⟨140775856236752581439167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187701141649003441918889 140775856236752581439167)
                      ·
                        rfl

theorem cell23_274160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2].length) (baseStart_274160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274160 prefixEnd_274160 := by exact prefixLift 274160
  have htrace : WordTrace (prefixWord ++ tailWord_274160) baseStart_274160 baseEnd_274160 := by
    simpa [prefixWord, tailWord_274160, baseEnd_274160] using wordTrace_append hprefix tailTrace_274160
  have hstable : (prefixWord ++ tailWord_274160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274160).length < 2 ^ (prefixWord ++ tailWord_274160).sum := by decide
  have hdescent : baseEnd_274160 < baseStart_274160 := by decide
  rcases family_descends (prefixWord ++ tailWord_274160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274167 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_274167 : Nat := 118140960795 + 274167 * 2 ^ 59
def prefixEnd_274167 : Nat := 4983230072969 + 3 ^ 40 * 274167 * 2
def baseEnd_274167 : Nat := 140779450601334054051635

theorem tailTrace_274167 : CollatzResearch.WordTrace tailWord_274167 prefixEnd_274167 140779450601334054051635 := by
  unfold tailWord_274167
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999691997747257840860755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6666461331831505227240503 9999691997747257840860755)
  ·
    refine ⟨14999537996620886761291133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9999691997747257840860755 14999537996620886761291133)
    ·
      refine ⟨5624826748732832535484175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14999537996620886761291133 5624826748732832535484175)
      ·
        refine ⟨8437240123099248803226263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624826748732832535484175 8437240123099248803226263)
        ·
          refine ⟨12655860184648873204839395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8437240123099248803226263 12655860184648873204839395)
          ·
            refine ⟨18983790276973309807259093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12655860184648873204839395 18983790276973309807259093)
            ·
              refine ⟨444932584616561948607635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18983790276973309807259093 444932584616561948607635)
              ·
                refine ⟨667398876924842922911453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444932584616561948607635 667398876924842922911453)
                ·
                  refine ⟨250274578846816096091795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667398876924842922911453 250274578846816096091795)
                  ·
                    refine ⟨375411868270224144137693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 250274578846816096091795 375411868270224144137693)
                    ·
                      refine ⟨140779450601334054051635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375411868270224144137693 140779450601334054051635)
                      ·
                        rfl

theorem cell23_274167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_274167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274167 prefixEnd_274167 := by exact prefixLift 274167
  have htrace : WordTrace (prefixWord ++ tailWord_274167) baseStart_274167 baseEnd_274167 := by
    simpa [prefixWord, tailWord_274167, baseEnd_274167] using wordTrace_append hprefix tailTrace_274167
  have hstable : (prefixWord ++ tailWord_274167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274167).length < 2 ^ (prefixWord ++ tailWord_274167).sum := by decide
  have hdescent : baseEnd_274167 < baseStart_274167 := by decide
  rcases family_descends (prefixWord ++ tailWord_274167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274200 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_274200 : Nat := 118140960795 + 274200 * 2 ^ 59
def prefixEnd_274200 : Nat := 4983230072969 + 3 ^ 40 * 274200 * 2
def baseEnd_274200 : Nat := 46932131820977474979661

theorem tailTrace_274200 : CollatzResearch.WordTrace tailWord_274200 prefixEnd_274200 46932131820977474979661 := by
  unfold tailWord_274200
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000447803313852238406027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6667263737751802984541369 5000447803313852238406027)
  ·
    refine ⟨7500671704970778357609041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000447803313852238406027 7500671704970778357609041)
    ·
      refine ⟨5625503778728083768206781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7500671704970778357609041 5625503778728083768206781)
      ·
        refine ⟨2109563917023031413077543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5625503778728083768206781 2109563917023031413077543)
        ·
          refine ⟨3164345875534547119616315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109563917023031413077543 3164345875534547119616315)
          ·
            refine ⟨4746518813301820679424473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164345875534547119616315 4746518813301820679424473)
            ·
              refine ⟨3559889109976365509568355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4746518813301820679424473 3559889109976365509568355)
              ·
                refine ⟨5339833664964548264352533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559889109976365509568355 5339833664964548264352533)
                ·
                  refine ⟨250304703045213199891525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5339833664964548264352533 250304703045213199891525)
                  ·
                    refine ⟨46932131820977474979661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250304703045213199891525 46932131820977474979661)
                    ·
                      rfl

theorem cell23_274200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_274200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274200 prefixEnd_274200 := by exact prefixLift 274200
  have htrace : WordTrace (prefixWord ++ tailWord_274200) baseStart_274200 baseEnd_274200 := by
    simpa [prefixWord, tailWord_274200, baseEnd_274200] using wordTrace_append hprefix tailTrace_274200
  have hstable : (prefixWord ++ tailWord_274200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274200).length < 2 ^ (prefixWord ++ tailWord_274200).sum := by decide
  have hdescent : baseEnd_274200 < baseStart_274200 := by decide
  rcases family_descends (prefixWord ++ tailWord_274200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274213 : List Nat := [1, 3, 1, 2, 3, 13]
def baseStart_274213 : Nat := 118140960795 + 274213 * 2 ^ 59
def prefixEnd_274213 : Nat := 4983230072969 + 3 ^ 40 * 274213 * 2
def baseEnd_274213 : Nat := 579436504985353391261

theorem tailTrace_274213 : CollatzResearch.WordTrace tailWord_274213 prefixEnd_274213 579436504985353391261 := by
  unfold tailWord_274213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001369755580607697035293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6667579837053738464690195 10001369755580607697035293)
  ·
    refine ⟨3750513658342727886388235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10001369755580607697035293 3750513658342727886388235)
    ·
      refine ⟨5625770487514091829582353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750513658342727886388235 5625770487514091829582353)
      ·
        refine ⟨4219327865635568872186765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5625770487514091829582353 4219327865635568872186765)
        ·
          refine ⟨1582247949613338327070037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4219327865635568872186765 1582247949613338327070037)
          ·
            refine ⟨579436504985353391261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 1582247949613338327070037 579436504985353391261)
            ·
              rfl

theorem cell23_274213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 13].length) (baseStart_274213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274213 prefixEnd_274213 := by exact prefixLift 274213
  have htrace : WordTrace (prefixWord ++ tailWord_274213) baseStart_274213 baseEnd_274213 := by
    simpa [prefixWord, tailWord_274213, baseEnd_274213] using wordTrace_append hprefix tailTrace_274213
  have hstable : (prefixWord ++ tailWord_274213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274213).length < 2 ^ (prefixWord ++ tailWord_274213).sum := by decide
  have hdescent : baseEnd_274213 < baseStart_274213 := by decide
  rcases family_descends (prefixWord ++ tailWord_274213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274237 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_274237 : Nat := 118140960795 + 274237 * 2 ^ 59
def prefixEnd_274237 : Nat := 4983230072969 + 3 ^ 40 * 274237 * 2
def baseEnd_274237 : Nat := 140815394247148780176313

theorem tailTrace_274237 : CollatzResearch.WordTrace tailWord_274237 prefixEnd_274237 140815394247148780176313 := by
  unfold tailWord_274237
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002245107493659795908965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6668163404995773197272643 10002245107493659795908965)
  ·
    refine ⟨1875420957655061211732931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10002245107493659795908965 1875420957655061211732931)
    ·
      refine ⟨2813131436482591817599397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875420957655061211732931 2813131436482591817599397)
      ·
        refine ⟨527462144340485965799887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2813131436482591817599397 527462144340485965799887)
        ·
          refine ⟨791193216510728948699831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527462144340485965799887 791193216510728948699831)
          ·
            refine ⟨1186789824766093423049747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791193216510728948699831 1186789824766093423049747)
            ·
              refine ⟨1780184737149140134574621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186789824766093423049747 1780184737149140134574621)
              ·
                refine ⟨667569276430927550465483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1780184737149140134574621 667569276430927550465483)
                ·
                  refine ⟨1001353914646391325698225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667569276430927550465483 1001353914646391325698225)
                  ·
                    refine ⟨751015435984793494273669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1001353914646391325698225 751015435984793494273669)
                    ·
                      refine ⟨140815394247148780176313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 751015435984793494273669 140815394247148780176313)
                      ·
                        rfl

theorem cell23_274237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_274237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274237 prefixEnd_274237 := by exact prefixLift 274237
  have htrace : WordTrace (prefixWord ++ tailWord_274237) baseStart_274237 baseEnd_274237 := by
    simpa [prefixWord, tailWord_274237, baseEnd_274237] using wordTrace_append hprefix tailTrace_274237
  have hstable : (prefixWord ++ tailWord_274237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274237).length < 2 ^ (prefixWord ++ tailWord_274237).sum := by decide
  have hdescent : baseEnd_274237 < baseStart_274237 := by decide
  rcases family_descends (prefixWord ++ tailWord_274237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274257 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_274257 : Nat := 118140960795 + 274257 * 2 ^ 59
def prefixEnd_274257 : Nat := 4983230072969 + 3 ^ 40 * 274257 * 2
def baseEnd_274257 : Nat := 140825663860238701926221

theorem tailTrace_274257 : CollatzResearch.WordTrace tailWord_274257 prefixEnd_274257 140825663860238701926221 := by
  unfold tailWord_274257
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002974567421203211637025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6668649711614135474424683 10002974567421203211637025)
  ·
    refine ⟨7502230925565902408727769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10002974567421203211637025 7502230925565902408727769)
    ·
      refine ⟨5626673194174426806545827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7502230925565902408727769 5626673194174426806545827)
      ·
        refine ⟨8440009791261640209818741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5626673194174426806545827 8440009791261640209818741)
        ·
          refine ⟨791250917930778769670507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8440009791261640209818741 791250917930778769670507)
          ·
            refine ⟨1186876376896168154505761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791250917930778769670507 1186876376896168154505761)
            ·
              refine ⟨890157282672126115879321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186876376896168154505761 890157282672126115879321)
              ·
                refine ⟨667617962004094586909491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890157282672126115879321 667617962004094586909491)
                ·
                  refine ⟨1001426943006141880364237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667617962004094586909491 1001426943006141880364237)
                  ·
                    refine ⟨375535103627303205136589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001426943006141880364237 375535103627303205136589)
                    ·
                      refine ⟨140825663860238701926221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375535103627303205136589 140825663860238701926221)
                      ·
                        rfl

theorem cell23_274257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_274257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274257 prefixEnd_274257 := by exact prefixLift 274257
  have htrace : WordTrace (prefixWord ++ tailWord_274257) baseStart_274257 baseEnd_274257 := by
    simpa [prefixWord, tailWord_274257, baseEnd_274257] using wordTrace_append hprefix tailTrace_274257
  have hstable : (prefixWord ++ tailWord_274257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274257).length < 2 ^ (prefixWord ++ tailWord_274257).sum := by decide
  have hdescent : baseEnd_274257 < baseStart_274257 := by decide
  rcases family_descends (prefixWord ++ tailWord_274257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274258 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_274258 : Nat := 118140960795 + 274258 * 2 ^ 59
def prefixEnd_274258 : Nat := 4983230072969 + 3 ^ 40 * 274258 * 2
def baseEnd_274258 : Nat := 140826177340893198013717

theorem tailTrace_274258 : CollatzResearch.WordTrace tailWord_274258 prefixEnd_274258 140826177340893198013717 := by
  unfold tailWord_274258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500752760104395095605857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6668674026945053588282285 2500752760104395095605857)
  ·
    refine ⟨1875564570078296321704393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2500752760104395095605857 1875564570078296321704393)
    ·
      refine ⟨1406673427558722241278295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1875564570078296321704393 1406673427558722241278295)
      ·
        refine ⟨2110010141338083361917443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406673427558722241278295 2110010141338083361917443)
        ·
          refine ⟨3165015212007125042876165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110010141338083361917443 3165015212007125042876165)
          ·
            refine ⟨593440352251335945539281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3165015212007125042876165 593440352251335945539281)
            ·
              refine ⟨445080264188501959154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593440352251335945539281 445080264188501959154461)
              ·
                refine ⟨166905099070688234682923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445080264188501959154461 166905099070688234682923)
                ·
                  refine ⟨250357648606032352024385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166905099070688234682923 250357648606032352024385)
                  ·
                    refine ⟨187768236454524264018289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250357648606032352024385 187768236454524264018289)
                    ·
                      refine ⟨140826177340893198013717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187768236454524264018289 140826177340893198013717)
                      ·
                        rfl

theorem cell23_274258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_274258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274258 prefixEnd_274258 := by exact prefixLift 274258
  have htrace : WordTrace (prefixWord ++ tailWord_274258) baseStart_274258 baseEnd_274258 := by
    simpa [prefixWord, tailWord_274258, baseEnd_274258] using wordTrace_append hprefix tailTrace_274258
  have hstable : (prefixWord ++ tailWord_274258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274258).length < 2 ^ (prefixWord ++ tailWord_274258).sum := by decide
  have hdescent : baseEnd_274258 < baseStart_274258 := by decide
  rcases family_descends (prefixWord ++ tailWord_274258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274261 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_274261 : Nat := 118140960795 + 274261 * 2 ^ 59
def prefixEnd_274261 : Nat := 4983230072969 + 3 ^ 40 * 274261 * 2
def baseEnd_274261 : Nat := 140827717782856686276203

theorem tailTrace_274261 : CollatzResearch.WordTrace tailWord_274261 prefixEnd_274261 140827717782856686276203 := by
  unfold tailWord_274261
  simp only [CollatzResearch.WordTrace]
  refine ⟨10003120459406711894782637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6668746972937807929855091 10003120459406711894782637)
  ·
    refine ⟨3751170172277516960543489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10003120459406711894782637 3751170172277516960543489)
    ·
      refine ⟨2813377629208137720407617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3751170172277516960543489 2813377629208137720407617)
      ·
        refine ⟨2110033221906103290305713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813377629208137720407617 2110033221906103290305713)
        ·
          refine ⟨1582524916429577467729285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110033221906103290305713 1582524916429577467729285)
          ·
            refine ⟨296723421830545775199241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1582524916429577467729285 296723421830545775199241)
            ·
              refine ⟨222542566372909331399431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296723421830545775199241 222542566372909331399431)
              ·
                refine ⟨333813849559363997099147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222542566372909331399431 333813849559363997099147)
                ·
                  refine ⟨500720774339045995648721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333813849559363997099147 500720774339045995648721)
                  ·
                    refine ⟨375540580754284496736541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 500720774339045995648721 375540580754284496736541)
                    ·
                      refine ⟨140827717782856686276203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375540580754284496736541 140827717782856686276203)
                      ·
                        rfl

theorem cell23_274261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_274261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274261 prefixEnd_274261 := by exact prefixLift 274261
  have htrace : WordTrace (prefixWord ++ tailWord_274261) baseStart_274261 baseEnd_274261 := by
    simpa [prefixWord, tailWord_274261, baseEnd_274261] using wordTrace_append hprefix tailTrace_274261
  have hstable : (prefixWord ++ tailWord_274261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274261).length < 2 ^ (prefixWord ++ tailWord_274261).sum := by decide
  have hdescent : baseEnd_274261 < baseStart_274261 := by decide
  rcases family_descends (prefixWord ++ tailWord_274261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274268 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_274268 : Nat := 118140960795 + 274268 * 2 ^ 59
def prefixEnd_274268 : Nat := 4983230072969 + 3 ^ 40 * 274268 * 2
def baseEnd_274268 : Nat := 46943770715812719629557

theorem tailTrace_274268 : CollatzResearch.WordTrace tailWord_274268 prefixEnd_274268 46943770715812719629557 := by
  unfold tailWord_274268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001687885190676045143729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6668917180254234726858305 5001687885190676045143729)
  ·
    refine ⟨3751265913893007033857797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5001687885190676045143729 3751265913893007033857797)
    ·
      refine ⟨703362358854938818848337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3751265913893007033857797 703362358854938818848337)
      ·
        refine ⟨527521769141204114136253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 703362358854938818848337 527521769141204114136253)
        ·
          refine ⟨197820663427951542801095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527521769141204114136253 197820663427951542801095)
          ·
            refine ⟨296730995141927314201643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197820663427951542801095 296730995141927314201643)
            ·
              refine ⟨445096492712890971302465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296730995141927314201643 445096492712890971302465)
              ·
                refine ⟨333822369534668228476849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445096492712890971302465 333822369534668228476849)
                ·
                  refine ⟨250366777151001171357637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333822369534668228476849 250366777151001171357637)
                  ·
                    refine ⟨46943770715812719629557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250366777151001171357637 46943770715812719629557)
                    ·
                      rfl

theorem cell23_274268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_274268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274268 prefixEnd_274268 := by exact prefixLift 274268
  have htrace : WordTrace (prefixWord ++ tailWord_274268) baseStart_274268 baseEnd_274268 := by
    simpa [prefixWord, tailWord_274268, baseEnd_274268] using wordTrace_append hprefix tailTrace_274268
  have hstable : (prefixWord ++ tailWord_274268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274268).length < 2 ^ (prefixWord ++ tailWord_274268).sum := by decide
  have hdescent : baseEnd_274268 < baseStart_274268 := by decide
  rcases family_descends (prefixWord ++ tailWord_274268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274360 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_274360 : Nat := 118140960795 + 274360 * 2 ^ 59
def prefixEnd_274360 : Nat := 4983230072969 + 3 ^ 40 * 274360 * 2
def baseEnd_274360 : Nat := 140878552367651798938247

theorem tailTrace_274360 : CollatzResearch.WordTrace tailWord_274360 prefixEnd_274360 140878552367651798938247 := by
  unfold tailWord_274360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003365643024025901318267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6671154190698701201757689 5003365643024025901318267)
  ·
    refine ⟨7505048464536038851977401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5003365643024025901318267 7505048464536038851977401)
    ·
      refine ⟨5628786348402029138983051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7505048464536038851977401 5628786348402029138983051)
      ·
        refine ⟨8443179522603043708474577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628786348402029138983051 8443179522603043708474577)
        ·
          refine ⟨6332384641952282781355933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8443179522603043708474577 6332384641952282781355933)
          ·
            refine ⟨2374644240732106043008475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6332384641952282781355933 2374644240732106043008475)
            ·
              refine ⟨3561966361098159064512713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374644240732106043008475 3561966361098159064512713)
              ·
                refine ⟨2671474770823619298384535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561966361098159064512713 2671474770823619298384535)
                ·
                  refine ⟨4007212156235428947576803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671474770823619298384535 4007212156235428947576803)
                  ·
                    refine ⟨6010818234353143421365205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007212156235428947576803 6010818234353143421365205)
                    ·
                      refine ⟨140878552367651798938247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6010818234353143421365205 140878552367651798938247)
                      ·
                        rfl

theorem cell23_274360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_274360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274360 prefixEnd_274360 := by exact prefixLift 274360
  have htrace : WordTrace (prefixWord ++ tailWord_274360) baseStart_274360 baseEnd_274360 := by
    simpa [prefixWord, tailWord_274360, baseEnd_274360] using wordTrace_append hprefix tailTrace_274360
  have hstable : (prefixWord ++ tailWord_274360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274360).length < 2 ^ (prefixWord ++ tailWord_274360).sum := by decide
  have hdescent : baseEnd_274360 < baseStart_274360 := by decide
  rcases family_descends (prefixWord ++ tailWord_274360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274367 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 2, 5]
def baseStart_274367 : Nat := 118140960795 + 274367 * 2 ^ 59
def prefixEnd_274367 : Nat := 4983230072969 + 3 ^ 40 * 274367 * 2
def baseEnd_274367 : Nat := 46960715577411090516905

theorem tailTrace_274367 : CollatzResearch.WordTrace tailWord_274367 prefixEnd_274367 46960715577411090516905 := by
  unfold tailWord_274367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006986597022691998141355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6671324398015127998760903 10006986597022691998141355)
  ·
    refine ⟨15010479895534037997212033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10006986597022691998141355 15010479895534037997212033)
    ·
      refine ⟨11257859921650528497909025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15010479895534037997212033 11257859921650528497909025)
      ·
        refine ⟨8443394941237896373431769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11257859921650528497909025 8443394941237896373431769)
        ·
          refine ⟨6332546205928422280073827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8443394941237896373431769 6332546205928422280073827)
          ·
            refine ⟨9498819308892633420110741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6332546205928422280073827 9498819308892633420110741)
            ·
              refine ⟨445257155104342191567691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9498819308892633420110741 445257155104342191567691)
              ·
                refine ⟨667885732656513287351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445257155104342191567691 667885732656513287351537)
                ·
                  refine ⟨500914299492384965513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667885732656513287351537 500914299492384965513653)
                  ·
                    refine ⟨46960715577411090516905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 500914299492384965513653 46960715577411090516905)
                    ·
                      rfl

theorem cell23_274367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_274367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274367 prefixEnd_274367 := by exact prefixLift 274367
  have htrace : WordTrace (prefixWord ++ tailWord_274367) baseStart_274367 baseEnd_274367 := by
    simpa [prefixWord, tailWord_274367, baseEnd_274367] using wordTrace_append hprefix tailTrace_274367
  have hstable : (prefixWord ++ tailWord_274367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274367).length < 2 ^ (prefixWord ++ tailWord_274367).sum := by decide
  have hdescent : baseEnd_274367 < baseStart_274367 := by decide
  rcases family_descends (prefixWord ++ tailWord_274367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274404 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_274404 : Nat := 118140960795 + 274404 * 2 ^ 59
def prefixEnd_274404 : Nat := 4983230072969 + 3 ^ 40 * 274404 * 2
def baseEnd_274404 : Nat := 140901145516449626788045

theorem tailTrace_274404 : CollatzResearch.WordTrace tailWord_274404 prefixEnd_274404 140901145516449626788045 := by
  unfold tailWord_274404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004168048944323658619133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6672224065259098211492177 5004168048944323658619133)
  ·
    refine ⟨1876563018354121371982175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5004168048944323658619133 1876563018354121371982175)
    ·
      refine ⟨2814844527531182057973263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876563018354121371982175 2814844527531182057973263)
      ·
        refine ⟨4222266791296773086959895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814844527531182057973263 4222266791296773086959895)
        ·
          refine ⟨6333400186945159630439843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4222266791296773086959895 6333400186945159630439843)
          ·
            refine ⟨9500100280417739445659765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6333400186945159630439843 9500100280417739445659765)
            ·
              refine ⟨890634401289163073030603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9500100280417739445659765 890634401289163073030603)
              ·
                refine ⟨1335951601933744609545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890634401289163073030603 1335951601933744609545905)
                ·
                  refine ⟨1001963701450308457159429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335951601933744609545905 1001963701450308457159429)
                  ·
                    refine ⟨187868194021932835717393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001963701450308457159429 187868194021932835717393)
                    ·
                      refine ⟨140901145516449626788045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187868194021932835717393 140901145516449626788045)
                      ·
                        rfl

theorem cell23_274404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_274404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274404 prefixEnd_274404 := by exact prefixLift 274404
  have htrace : WordTrace (prefixWord ++ tailWord_274404) baseStart_274404 baseEnd_274404 := by
    simpa [prefixWord, tailWord_274404, baseEnd_274404] using wordTrace_append hprefix tailTrace_274404
  have hstable : (prefixWord ++ tailWord_274404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274404).length < 2 ^ (prefixWord ++ tailWord_274404).sum := by decide
  have hdescent : baseEnd_274404 < baseStart_274404 := by decide
  rcases family_descends (prefixWord ++ tailWord_274404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274414 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_274414 : Nat := 118140960795 + 274414 * 2 ^ 59
def prefixEnd_274414 : Nat := 4983230072969 + 3 ^ 40 * 274414 * 2
def baseEnd_274414 : Nat := 46968760107664862554333

theorem tailTrace_274414 : CollatzResearch.WordTrace tailWord_274414 prefixEnd_274414 46968760107664862554333 := by
  unfold tailWord_274414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251087603481552378137787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6672467218568279350068197 1251087603481552378137787)
  ·
    refine ⟨1876631405222328567206681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251087603481552378137787 1876631405222328567206681)
    ·
      refine ⟨1407473553916746425405011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876631405222328567206681 1407473553916746425405011)
      ·
        refine ⟨2111210330875119638107517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407473553916746425405011 2111210330875119638107517)
        ·
          refine ⟨791703874078169864290319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2111210330875119638107517 791703874078169864290319)
          ·
            refine ⟨1187555811117254796435479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791703874078169864290319 1187555811117254796435479)
            ·
              refine ⟨1781333716675882194653219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187555811117254796435479 1781333716675882194653219)
              ·
                refine ⟨2672000575013823291979829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781333716675882194653219 2672000575013823291979829)
                ·
                  refine ⟨250500053907545933623109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2672000575013823291979829 250500053907545933623109)
                  ·
                    refine ⟨46968760107664862554333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250500053907545933623109 46968760107664862554333)
                    ·
                      rfl

theorem cell23_274414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_274414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274414 prefixEnd_274414 := by exact prefixLift 274414
  have htrace : WordTrace (prefixWord ++ tailWord_274414) baseStart_274414 baseEnd_274414 := by
    simpa [prefixWord, tailWord_274414, baseEnd_274414] using wordTrace_append hprefix tailTrace_274414
  have hstable : (prefixWord ++ tailWord_274414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274414).length < 2 ^ (prefixWord ++ tailWord_274414).sum := by decide
  have hdescent : baseEnd_274414 < baseStart_274414 := by decide
  rcases family_descends (prefixWord ++ tailWord_274414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274424 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_274424 : Nat := 118140960795 + 274424 * 2 ^ 59
def prefixEnd_274424 : Nat := 4983230072969 + 3 ^ 40 * 274424 * 2
def baseEnd_274424 : Nat := 140911415129539548537953

theorem tailTrace_274424 : CollatzResearch.WordTrace tailWord_274424 prefixEnd_274424 140911415129539548537953 := by
  unfold tailWord_274424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004532778908095366483163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6672710371877460488644217 5004532778908095366483163)
  ·
    refine ⟨7506799168362143049724745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004532778908095366483163 7506799168362143049724745)
    ·
      refine ⟨5630099376271607287293559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7506799168362143049724745 5630099376271607287293559)
      ·
        refine ⟨8445149064407410930940339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5630099376271607287293559 8445149064407410930940339)
        ·
          refine ⟨12667723596611116396410509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8445149064407410930940339 12667723596611116396410509)
          ·
            refine ⟨4750396348729168648653941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12667723596611116396410509 4750396348729168648653941)
            ·
              refine ⟨445349657693359560811307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4750396348729168648653941 445349657693359560811307)
              ·
                refine ⟨668024486540039341216961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445349657693359560811307 668024486540039341216961)
                ·
                  refine ⟨501018364905029505912721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668024486540039341216961 501018364905029505912721)
                  ·
                    refine ⟨375763773678772129434541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501018364905029505912721 375763773678772129434541)
                    ·
                      refine ⟨140911415129539548537953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375763773678772129434541 140911415129539548537953)
                      ·
                        rfl

theorem cell23_274424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_274424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274424 prefixEnd_274424 := by exact prefixLift 274424
  have htrace : WordTrace (prefixWord ++ tailWord_274424) baseStart_274424 baseEnd_274424 := by
    simpa [prefixWord, tailWord_274424, baseEnd_274424] using wordTrace_append hprefix tailTrace_274424
  have hstable : (prefixWord ++ tailWord_274424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274424).length < 2 ^ (prefixWord ++ tailWord_274424).sum := by decide
  have hdescent : baseEnd_274424 < baseStart_274424 := by decide
  rcases family_descends (prefixWord ++ tailWord_274424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274461 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 6]
def baseStart_274461 : Nat := 118140960795 + 274461 * 2 ^ 59
def prefixEnd_274461 : Nat := 4983230072969 + 3 ^ 40 * 274461 * 2
def baseEnd_274461 : Nat := 15658934879306211530587

theorem tailTrace_274461 : CollatzResearch.WordTrace tailWord_274461 prefixEnd_274461 15658934879306211530587 := by
  unfold tailWord_274461
  simp only [CollatzResearch.WordTrace]
  refine ⟨10010415058682146052063237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6673610039121430701375491 10010415058682146052063237)
  ·
    refine ⟨1876952823502902384761857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10010415058682146052063237 1876952823502902384761857)
    ·
      refine ⟨1407714617627176788571393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876952823502902384761857 1407714617627176788571393)
      ·
        refine ⟨1055785963220382591428545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1407714617627176788571393 1055785963220382591428545)
        ·
          refine ⟨791839472415286943571409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055785963220382591428545 791839472415286943571409)
          ·
            refine ⟨593879604311465207678557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791839472415286943571409 593879604311465207678557)
            ·
              refine ⟨222704851616799452879459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593879604311465207678557 222704851616799452879459)
              ·
                refine ⟨334057277425199179319189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222704851616799452879459 334057277425199179319189)
                ·
                  refine ⟨15658934879306211530587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 334057277425199179319189 15658934879306211530587)
                  ·
                    rfl

theorem cell23_274461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_274461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274461 prefixEnd_274461 := by exact prefixLift 274461
  have htrace : WordTrace (prefixWord ++ tailWord_274461) baseStart_274461 baseEnd_274461 := by
    simpa [prefixWord, tailWord_274461, baseEnd_274461] using wordTrace_append hprefix tailTrace_274461
  have hstable : (prefixWord ++ tailWord_274461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274461).length < 2 ^ (prefixWord ++ tailWord_274461).sum := by decide
  have hdescent : baseEnd_274461 < baseStart_274461 := by decide
  rcases family_descends (prefixWord ++ tailWord_274461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274487 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 1, 6]
def baseStart_274487 : Nat := 118140960795 + 274487 * 2 ^ 59
def prefixEnd_274487 : Nat := 4983230072969 + 3 ^ 40 * 274487 * 2
def baseEnd_274487 : Nat := 46981254803590934016721

theorem tailTrace_274487 : CollatzResearch.WordTrace tailWord_274487 prefixEnd_274487 46981254803590934016721 := by
  unfold tailWord_274487
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011363356587952492509715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6674242237725301661673143 10011363356587952492509715)
  ·
    refine ⟨15017045034881928738764573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10011363356587952492509715 15017045034881928738764573)
    ·
      refine ⟨5631391888080723277036715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15017045034881928738764573 5631391888080723277036715)
      ·
        refine ⟨8447087832121084915555073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5631391888080723277036715 8447087832121084915555073)
        ·
          refine ⟨6335315874090813686666305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8447087832121084915555073 6335315874090813686666305)
          ·
            refine ⟨4751486905568110264999729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6335315874090813686666305 4751486905568110264999729)
            ·
              refine ⟨3563615179176082698749797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751486905568110264999729 3563615179176082698749797)
              ·
                refine ⟨668177846095515506015587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3563615179176082698749797 668177846095515506015587)
                ·
                  refine ⟨1002266769143273259023381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668177846095515506015587 1002266769143273259023381)
                  ·
                    refine ⟨46981254803590934016721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1002266769143273259023381 46981254803590934016721)
                    ·
                      rfl

theorem cell23_274487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_274487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274487 prefixEnd_274487 := by exact prefixLift 274487
  have htrace : WordTrace (prefixWord ++ tailWord_274487) baseStart_274487 baseEnd_274487 := by
    simpa [prefixWord, tailWord_274487, baseEnd_274487] using wordTrace_append hprefix tailTrace_274487
  have hstable : (prefixWord ++ tailWord_274487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274487).length < 2 ^ (prefixWord ++ tailWord_274487).sum := by decide
  have hdescent : baseEnd_274487 < baseStart_274487 := by decide
  rcases family_descends (prefixWord ++ tailWord_274487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274507 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_274507 : Nat := 118140960795 + 274507 * 2 ^ 59
def prefixEnd_274507 : Nat := 4983230072969 + 3 ^ 40 * 274507 * 2
def baseEnd_274507 : Nat := 140954034023862723800071

theorem tailTrace_274507 : CollatzResearch.WordTrace tailWord_274507 prefixEnd_274507 140954034023862723800071 := by
  unfold tailWord_274507
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012092816515495908237775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6674728544343663938825183 10012092816515495908237775)
  ·
    refine ⟨15018139224773243862356663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10012092816515495908237775 15018139224773243862356663)
    ·
      refine ⟨22527208837159865793534995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15018139224773243862356663 22527208837159865793534995)
      ·
        refine ⟨33790813255739798690302493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22527208837159865793534995 33790813255739798690302493)
        ·
          refine ⟨12671554970902424508863435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33790813255739798690302493 12671554970902424508863435)
          ·
            refine ⟨19007332456353636763295153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12671554970902424508863435 19007332456353636763295153)
            ·
              refine ⟨14255499342265227572471365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19007332456353636763295153 14255499342265227572471365)
              ·
                refine ⟨2672906126674730169838381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14255499342265227572471365 2672906126674730169838381)
                ·
                  refine ⟨1002339797503023813689393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2672906126674730169838381 1002339797503023813689393)
                  ·
                    refine ⟨751754848127267860267045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002339797503023813689393 751754848127267860267045)
                    ·
                      refine ⟨140954034023862723800071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 751754848127267860267045 140954034023862723800071)
                      ·
                        rfl

theorem cell23_274507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_274507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274507 prefixEnd_274507 := by exact prefixLift 274507
  have htrace : WordTrace (prefixWord ++ tailWord_274507) baseStart_274507 baseEnd_274507 := by
    simpa [prefixWord, tailWord_274507, baseEnd_274507] using wordTrace_append hprefix tailTrace_274507
  have hstable : (prefixWord ++ tailWord_274507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274507).length < 2 ^ (prefixWord ++ tailWord_274507).sum := by decide
  have hdescent : baseEnd_274507 < baseStart_274507 := by decide
  rcases family_descends (prefixWord ++ tailWord_274507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274517 : List Nat := [1, 3, 2, 2, 1, 3, 1, 10]
def baseStart_274517 : Nat := 118140960795 + 274517 * 2 ^ 59
def prefixEnd_274517 : Nat := 4983230072969 + 3 ^ 40 * 274517 * 2
def baseEnd_274517 : Nat := 5220709956681766099075

theorem tailTrace_274517 : CollatzResearch.WordTrace tailWord_274517 prefixEnd_274517 5220709956681766099075 := by
  unfold tailWord_274517
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012457546479267616101805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6674971697652845077401203 10012457546479267616101805)
  ·
    refine ⟨3754671579929725356038177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10012457546479267616101805 3754671579929725356038177)
    ·
      refine ⟨2816003684947294017028633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3754671579929725356038177 2816003684947294017028633)
      ·
        refine ⟨2112002763710470512771475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2816003684947294017028633 2112002763710470512771475)
        ·
          refine ⟨3168004145565705769157213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112002763710470512771475 3168004145565705769157213)
          ·
            refine ⟨1188001554587139663433955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3168004145565705769157213 1188001554587139663433955)
            ·
              refine ⟨1782002331880709495150933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188001554587139663433955 1782002331880709495150933)
              ·
                refine ⟨5220709956681766099075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1782002331880709495150933 5220709956681766099075)
                ·
                  rfl

theorem cell23_274517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 10].length) (baseStart_274517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274517 prefixEnd_274517 := by exact prefixLift 274517
  have htrace : WordTrace (prefixWord ++ tailWord_274517) baseStart_274517 baseEnd_274517 := by
    simpa [prefixWord, tailWord_274517, baseEnd_274517] using wordTrace_append hprefix tailTrace_274517
  have hstable : (prefixWord ++ tailWord_274517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274517).length < 2 ^ (prefixWord ++ tailWord_274517).sum := by decide
  have hdescent : baseEnd_274517 < baseStart_274517 := by decide
  rcases family_descends (prefixWord ++ tailWord_274517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274524 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_274524 : Nat := 118140960795 + 274524 * 2 ^ 59
def prefixEnd_274524 : Nat := 4983230072969 + 3 ^ 40 * 274524 * 2
def baseEnd_274524 : Nat := 140962763194989157287493

theorem tailTrace_274524 : CollatzResearch.WordTrace tailWord_274524 prefixEnd_274524 140962763194989157287493 := by
  unfold tailWord_274524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006356428726953905803313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6675141904969271874404417 5006356428726953905803313)
  ·
    refine ⟨3754767321545215429352485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5006356428726953905803313 3754767321545215429352485)
    ·
      refine ⟨704018872789727893003591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3754767321545215429352485 704018872789727893003591)
      ·
        refine ⟨1056028309184591839505387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704018872789727893003591 1056028309184591839505387)
        ·
          refine ⟨1584042463776887759258081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056028309184591839505387 1584042463776887759258081)
          ·
            refine ⟨1188031847832665819443561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584042463776887759258081 1188031847832665819443561)
            ·
              refine ⟨891023885874499364582671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188031847832665819443561 891023885874499364582671)
              ·
                refine ⟨1336535828811749046874007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891023885874499364582671 1336535828811749046874007)
                ·
                  refine ⟨2004803743217623570311011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336535828811749046874007 2004803743217623570311011)
                  ·
                    refine ⟨3007205614826435355466517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004803743217623570311011 3007205614826435355466517)
                    ·
                      refine ⟨140962763194989157287493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3007205614826435355466517 140962763194989157287493)
                      ·
                        rfl

theorem cell23_274524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_274524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274524 prefixEnd_274524 := by exact prefixLift 274524
  have htrace : WordTrace (prefixWord ++ tailWord_274524) baseStart_274524 baseEnd_274524 := by
    simpa [prefixWord, tailWord_274524, baseEnd_274524] using wordTrace_append hprefix tailTrace_274524
  have hstable : (prefixWord ++ tailWord_274524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274524).length < 2 ^ (prefixWord ++ tailWord_274524).sum := by decide
  have hdescent : baseEnd_274524 < baseStart_274524 := by decide
  rcases family_descends (prefixWord ++ tailWord_274524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274531 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 3]
def baseStart_274531 : Nat := 118140960795 + 274531 * 2 ^ 59
def prefixEnd_274531 : Nat := 4983230072969 + 3 ^ 40 * 274531 * 2
def baseEnd_274531 : Nat := 140966357559570629899961

theorem tailTrace_274531 : CollatzResearch.WordTrace tailWord_274531 prefixEnd_274531 140966357559570629899961 := by
  unfold tailWord_274531
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012968168428548007111447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6675312112285698671407631 10012968168428548007111447)
  ·
    refine ⟨15019452252642822010667171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10012968168428548007111447 15019452252642822010667171)
    ·
      refine ⟨22529178378964233016000757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15019452252642822010667171 22529178378964233016000757)
      ·
        refine ⟨2112110473027896845250071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22529178378964233016000757 2112110473027896845250071)
        ·
          refine ⟨3168165709541845267875107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112110473027896845250071 3168165709541845267875107)
          ·
            refine ⟨4752248564312767901812661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168165709541845267875107 4752248564312767901812661)
            ·
              refine ⟨445523302904321990794937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4752248564312767901812661 445523302904321990794937)
              ·
                refine ⟨334142477178241493096203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445523302904321990794937 334142477178241493096203)
                ·
                  refine ⟨501213715767362239644305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334142477178241493096203 501213715767362239644305)
                  ·
                    refine ⟨375910286825521679733229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501213715767362239644305 375910286825521679733229)
                    ·
                      refine ⟨140966357559570629899961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375910286825521679733229 140966357559570629899961)
                      ·
                        rfl

theorem cell23_274531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_274531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274531 prefixEnd_274531 := by exact prefixLift 274531
  have htrace : WordTrace (prefixWord ++ tailWord_274531) baseStart_274531 baseEnd_274531 := by
    simpa [prefixWord, tailWord_274531, baseEnd_274531] using wordTrace_append hprefix tailTrace_274531
  have hstable : (prefixWord ++ tailWord_274531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274531).length < 2 ^ (prefixWord ++ tailWord_274531).sum := by decide
  have hdescent : baseEnd_274531 < baseStart_274531 := by decide
  rcases family_descends (prefixWord ++ tailWord_274531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274544 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_274544 : Nat := 118140960795 + 274544 * 2 ^ 59
def prefixEnd_274544 : Nat := 4983230072969 + 3 ^ 40 * 274544 * 2
def baseEnd_274544 : Nat := 140973032808079079037401

theorem tailTrace_274544 : CollatzResearch.WordTrace tailWord_274544 prefixEnd_274544 140973032808079079037401 := by
  unfold tailWord_274544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006721158690725613667343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6675628211587634151556457 5006721158690725613667343)
  ·
    refine ⟨7510081738036088420501015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006721158690725613667343 7510081738036088420501015)
    ·
      refine ⟨11265122607054132630751523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7510081738036088420501015 11265122607054132630751523)
      ·
        refine ⟨16897683910581198946127285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11265122607054132630751523 16897683910581198946127285)
        ·
          refine ⟨1584157866616987401199433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16897683910581198946127285 1584157866616987401199433)
          ·
            refine ⟨1188118399962740550899575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584157866616987401199433 1188118399962740550899575)
            ·
              refine ⟨1782177599944110826349363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188118399962740550899575 1782177599944110826349363)
              ·
                refine ⟨2673266399916166239524045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782177599944110826349363 2673266399916166239524045)
                ·
                  refine ⟨1002474899968562339821517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2673266399916166239524045 1002474899968562339821517)
                  ·
                    refine ⟨375928087488210877433069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1002474899968562339821517 375928087488210877433069)
                    ·
                      refine ⟨140973032808079079037401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375928087488210877433069 140973032808079079037401)
                      ·
                        rfl

theorem cell23_274544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_274544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274544 prefixEnd_274544 := by exact prefixLift 274544
  have htrace : WordTrace (prefixWord ++ tailWord_274544) baseStart_274544 baseEnd_274544 := by
    simpa [prefixWord, tailWord_274544, baseEnd_274544] using wordTrace_append hprefix tailTrace_274544
  have hstable : (prefixWord ++ tailWord_274544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274544).length < 2 ^ (prefixWord ++ tailWord_274544).sum := by decide
  have hdescent : baseEnd_274544 < baseStart_274544 := by decide
  rcases family_descends (prefixWord ++ tailWord_274544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274578 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_274578 : Nat := 118140960795 + 274578 * 2 ^ 59
def prefixEnd_274578 : Nat := 4983230072969 + 3 ^ 40 * 274578 * 2
def baseEnd_274578 : Nat := 140990491150331946012245

theorem tailTrace_274578 : CollatzResearch.WordTrace tailWord_274578 prefixEnd_274578 140990491150331946012245 := by
  unfold tailWord_274578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503670599814568758518097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6676454932838850022714925 2503670599814568758518097)
  ·
    refine ⟨1877752949860926568888573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2503670599814568758518097 1877752949860926568888573)
    ·
      refine ⟨704157356197847463333215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1877752949860926568888573 704157356197847463333215)
      ·
        refine ⟨1056236034296771194999823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704157356197847463333215 1056236034296771194999823)
        ·
          refine ⟨1584354051445156792499735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056236034296771194999823 1584354051445156792499735)
          ·
            refine ⟨2376531077167735188749603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584354051445156792499735 2376531077167735188749603)
            ·
              refine ⟨3564796615751602783124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376531077167735188749603 3564796615751602783124405)
              ·
                refine ⟨334199682726712760917913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3564796615751602783124405 334199682726712760917913)
                ·
                  refine ⟨250649762045034570688435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334199682726712760917913 250649762045034570688435)
                  ·
                    refine ⟨375974643067551856032653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 250649762045034570688435 375974643067551856032653)
                    ·
                      refine ⟨140990491150331946012245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 375974643067551856032653 140990491150331946012245)
                      ·
                        rfl

theorem cell23_274578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_274578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274578 prefixEnd_274578 := by exact prefixLift 274578
  have htrace : WordTrace (prefixWord ++ tailWord_274578) baseStart_274578 baseEnd_274578 := by
    simpa [prefixWord, tailWord_274578, baseEnd_274578] using wordTrace_append hprefix tailTrace_274578
  have hstable : (prefixWord ++ tailWord_274578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274578).length < 2 ^ (prefixWord ++ tailWord_274578).sum := by decide
  have hdescent : baseEnd_274578 < baseStart_274578 := by decide
  rcases family_descends (prefixWord ++ tailWord_274578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274587 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_274587 : Nat := 118140960795 + 274587 * 2 ^ 59
def prefixEnd_274587 : Nat := 4983230072969 + 3 ^ 40 * 274587 * 2
def baseEnd_274587 : Nat := 140995112476222410799703

theorem tailTrace_274587 : CollatzResearch.WordTrace tailWord_274587 prefixEnd_274587 140995112476222410799703 := by
  unfold tailWord_274587
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015010656225669571150015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6676673770817113047433343 10015010656225669571150015)
  ·
    refine ⟨15022515984338504356725023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015010656225669571150015 15022515984338504356725023)
    ·
      refine ⟨22533773976507756535087535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15022515984338504356725023 22533773976507756535087535)
      ·
        refine ⟨33800660964761634802631303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22533773976507756535087535 33800660964761634802631303)
        ·
          refine ⟨50700991447142452203946955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33800660964761634802631303 50700991447142452203946955)
          ·
            refine ⟨76051487170713678305920433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50700991447142452203946955 76051487170713678305920433)
            ·
              refine ⟨57038615378035258729440325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76051487170713678305920433 57038615378035258729440325)
              ·
                refine ⟨10694740383381611011770061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57038615378035258729440325 10694740383381611011770061)
                ·
                  refine ⟨4010527643768104129413773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10694740383381611011770061 4010527643768104129413773)
                  ·
                    refine ⟨1503947866413039048530165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4010527643768104129413773 1503947866413039048530165)
                    ·
                      refine ⟨140995112476222410799703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1503947866413039048530165 140995112476222410799703)
                      ·
                        rfl

theorem cell23_274587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_274587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274587 prefixEnd_274587 := by exact prefixLift 274587
  have htrace : WordTrace (prefixWord ++ tailWord_274587) baseStart_274587 baseEnd_274587 := by
    simpa [prefixWord, tailWord_274587, baseEnd_274587] using wordTrace_append hprefix tailTrace_274587
  have hstable : (prefixWord ++ tailWord_274587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274587).length < 2 ^ (prefixWord ++ tailWord_274587).sum := by decide
  have hdescent : baseEnd_274587 < baseStart_274587 := by decide
  rcases family_descends (prefixWord ++ tailWord_274587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274588 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_274588 : Nat := 118140960795 + 274588 * 2 ^ 59
def prefixEnd_274588 : Nat := 4983230072969 + 3 ^ 40 * 274588 * 2
def baseEnd_274588 : Nat := 140995625956876906887199

theorem tailTrace_274588 : CollatzResearch.WordTrace tailWord_274588 prefixEnd_274588 140995625956876906887199 := by
  unfold tailWord_274588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007523564611023370968209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6676698086148031161290945 5007523564611023370968209)
  ·
    refine ⟨3755642673458267528226157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5007523564611023370968209 3755642673458267528226157)
    ·
      refine ⟨1408366002546850323084809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3755642673458267528226157 1408366002546850323084809)
      ·
        refine ⟨1056274501910137742313607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408366002546850323084809 1056274501910137742313607)
        ·
          refine ⟨1584411752865206613470411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056274501910137742313607 1584411752865206613470411)
          ·
            refine ⟨2376617629297809920205617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584411752865206613470411 2376617629297809920205617)
            ·
              refine ⟨1782463221973357440154213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376617629297809920205617 1782463221973357440154213)
              ·
                refine ⟨334211854120004520028915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1782463221973357440154213 334211854120004520028915)
                ·
                  refine ⟨501317781180006780043373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334211854120004520028915 501317781180006780043373)
                  ·
                    refine ⟨187994167942502542516265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501317781180006780043373 187994167942502542516265)
                    ·
                      refine ⟨140995625956876906887199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 187994167942502542516265 140995625956876906887199)
                      ·
                        rfl

theorem cell23_274588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_274588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274588 prefixEnd_274588 := by exact prefixLift 274588
  have htrace : WordTrace (prefixWord ++ tailWord_274588) baseStart_274588 baseEnd_274588 := by
    simpa [prefixWord, tailWord_274588, baseEnd_274588] using wordTrace_append hprefix tailTrace_274588
  have hstable : (prefixWord ++ tailWord_274588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274588).length < 2 ^ (prefixWord ++ tailWord_274588).sum := by decide
  have hdescent : baseEnd_274588 < baseStart_274588 := by decide
  rcases family_descends (prefixWord ++ tailWord_274588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274605 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_274605 : Nat := 118140960795 + 274605 * 2 ^ 59
def prefixEnd_274605 : Nat := 4983230072969 + 3 ^ 40 * 274605 * 2
def baseEnd_274605 : Nat := 141004355128003340374621

theorem tailTrace_274605 : CollatzResearch.WordTrace tailWord_274605 prefixEnd_274605 141004355128003340374621 := by
  unfold tailWord_274605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015667170160458645305269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6677111446773639096870179 10015667170160458645305269)
  ·
    refine ⟨938968797202542997997369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10015667170160458645305269 938968797202542997997369)
    ·
      refine ⟨704226597901907248498027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 938968797202542997997369 704226597901907248498027)
      ·
        refine ⟨1056339896852860872747041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704226597901907248498027 1056339896852860872747041)
        ·
          refine ⟨792254922639645654560281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056339896852860872747041 792254922639645654560281)
          ·
            refine ⟨594191191979734240920211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792254922639645654560281 594191191979734240920211)
            ·
              refine ⟨891286787969601361380317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594191191979734240920211 891286787969601361380317)
              ·
                refine ⟨334232545488600510517619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 891286787969601361380317 334232545488600510517619)
                ·
                  refine ⟨501348818232900765776429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334232545488600510517619 501348818232900765776429)
                  ·
                    refine ⟨188005806837337787166161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501348818232900765776429 188005806837337787166161)
                    ·
                      refine ⟨141004355128003340374621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188005806837337787166161 141004355128003340374621)
                      ·
                        rfl

theorem cell23_274605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_274605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274605 prefixEnd_274605 := by exact prefixLift 274605
  have htrace : WordTrace (prefixWord ++ tailWord_274605) baseStart_274605 baseEnd_274605 := by
    simpa [prefixWord, tailWord_274605, baseEnd_274605] using wordTrace_append hprefix tailTrace_274605
  have hstable : (prefixWord ++ tailWord_274605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274605).length < 2 ^ (prefixWord ++ tailWord_274605).sum := by decide
  have hdescent : baseEnd_274605 < baseStart_274605 := by decide
  rcases family_descends (prefixWord ++ tailWord_274605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274607 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 11]
def baseStart_274607 : Nat := 118140960795 + 274607 * 2 ^ 59
def prefixEnd_274607 : Nat := 4983230072969 + 3 ^ 40 * 274607 * 2
def baseEnd_274607 : Nat := 15667264676590259172179

theorem tailTrace_274607 : CollatzResearch.WordTrace tailWord_274607 prefixEnd_274607 15667264676590259172179 := by
  unfold tailWord_274607
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015740116153212986878075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6677160077435475324585383 10015740116153212986878075)
  ·
    refine ⟨15023610174229819480317113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015740116153212986878075 15023610174229819480317113)
    ·
      refine ⟨11267707630672364610237835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15023610174229819480317113 11267707630672364610237835)
      ·
        refine ⟨16901561446008546915356753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11267707630672364610237835 16901561446008546915356753)
        ·
          refine ⟨12676171084506410186517565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16901561446008546915356753 12676171084506410186517565)
          ·
            refine ⟨4753564156689903819944087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12676171084506410186517565 4753564156689903819944087)
            ·
              refine ⟨7130346235034855729916131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753564156689903819944087 7130346235034855729916131)
              ·
                refine ⟨10695519352552283594874197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7130346235034855729916131 10695519352552283594874197)
                ·
                  refine ⟨15667264676590259172179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 10695519352552283594874197 15667264676590259172179)
                  ·
                    rfl

theorem cell23_274607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 11].length) (baseStart_274607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274607 prefixEnd_274607 := by exact prefixLift 274607
  have htrace : WordTrace (prefixWord ++ tailWord_274607) baseStart_274607 baseEnd_274607 := by
    simpa [prefixWord, tailWord_274607, baseEnd_274607] using wordTrace_append hprefix tailTrace_274607
  have hstable : (prefixWord ++ tailWord_274607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274607).length < 2 ^ (prefixWord ++ tailWord_274607).sum := by decide
  have hdescent : baseEnd_274607 < baseStart_274607 := by decide
  rcases family_descends (prefixWord ++ tailWord_274607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274624 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 7]
def baseStart_274624 : Nat := 118140960795 + 274624 * 2 ^ 59
def prefixEnd_274624 : Nat := 4983230072969 + 3 ^ 40 * 274624 * 2
def baseEnd_274624 : Nat := 15668234584493196226337

theorem tailTrace_274624 : CollatzResearch.WordTrace tailWord_274624 prefixEnd_274624 15668234584493196226337 := by
  unfold tailWord_274624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008180078545812445123463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6677573438061083260164617 5008180078545812445123463)
  ·
    refine ⟨7512270117818718667685195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008180078545812445123463 7512270117818718667685195)
    ·
      refine ⟨11268405176728078001527793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7512270117818718667685195 11268405176728078001527793)
      ·
        refine ⟨8451303882546058501145845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11268405176728078001527793 8451303882546058501145845)
        ·
          refine ⟨792309738988692984482423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8451303882546058501145845 792309738988692984482423)
          ·
            refine ⟨1188464608483039476723635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792309738988692984482423 1188464608483039476723635)
            ·
              refine ⟨1782696912724559215085453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188464608483039476723635 1782696912724559215085453)
              ·
                refine ⟨668511342271709705657045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1782696912724559215085453 668511342271709705657045)
                ·
                  refine ⟨15668234584493196226337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 668511342271709705657045 15668234584493196226337)
                  ·
                    rfl

theorem cell23_274624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_274624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274624 prefixEnd_274624 := by exact prefixLift 274624
  have htrace : WordTrace (prefixWord ++ tailWord_274624) baseStart_274624 baseEnd_274624 := by
    simpa [prefixWord, tailWord_274624, baseEnd_274624] using wordTrace_append hprefix tailTrace_274624
  have hstable : (prefixWord ++ tailWord_274624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274624).length < 2 ^ (prefixWord ++ tailWord_274624).sum := by decide
  have hdescent : baseEnd_274624 < baseStart_274624 := by decide
  rcases family_descends (prefixWord ++ tailWord_274624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274635 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 2, 2, 2]
def baseStart_274635 : Nat := 118140960795 + 274635 * 2 ^ 59
def prefixEnd_274635 : Nat := 4983230072969 + 3 ^ 40 * 274635 * 2
def baseEnd_274635 : Nat := 141019759547638222999483

theorem tailTrace_274635 : CollatzResearch.WordTrace tailWord_274635 prefixEnd_274635 141019759547638222999483 := by
  unfold tailWord_274635
  simp only [CollatzResearch.WordTrace]
  refine ⟨10016761360051773768897359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6677840906701182512598239 10016761360051773768897359)
  ·
    refine ⟨15025142040077660653346039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10016761360051773768897359 15025142040077660653346039)
    ·
      refine ⟨22537713060116490980019059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15025142040077660653346039 22537713060116490980019059)
      ·
        refine ⟨33806569590174736470028589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22537713060116490980019059 33806569590174736470028589)
        ·
          refine ⟨12677463596315526176260721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33806569590174736470028589 12677463596315526176260721)
          ·
            refine ⟨9508097697236644632195541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12677463596315526176260721 9508097697236644632195541)
            ·
              refine ⟨222846039778983858567083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9508097697236644632195541 222846039778983858567083)
              ·
                refine ⟨334269059668475787850625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222846039778983858567083 334269059668475787850625)
                ·
                  refine ⟨250701794751356840887969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334269059668475787850625 250701794751356840887969)
                  ·
                    refine ⟨188026346063517630665977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250701794751356840887969 188026346063517630665977)
                    ·
                      refine ⟨141019759547638222999483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188026346063517630665977 141019759547638222999483)
                      ·
                        rfl

theorem cell23_274635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 2, 2].length) (baseStart_274635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274635 prefixEnd_274635 := by exact prefixLift 274635
  have htrace : WordTrace (prefixWord ++ tailWord_274635) baseStart_274635 baseEnd_274635 := by
    simpa [prefixWord, tailWord_274635, baseEnd_274635] using wordTrace_append hprefix tailTrace_274635
  have hstable : (prefixWord ++ tailWord_274635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274635).length < 2 ^ (prefixWord ++ tailWord_274635).sum := by decide
  have hdescent : baseEnd_274635 < baseStart_274635 := by decide
  rcases family_descends (prefixWord ++ tailWord_274635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274671 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 2, 5]
def baseStart_274671 : Nat := 118140960795 + 274671 * 2 ^ 59
def prefixEnd_274671 : Nat := 4983230072969 + 3 ^ 40 * 274671 * 2
def baseEnd_274671 : Nat := 47012748283733360716439

theorem tailTrace_274671 : CollatzResearch.WordTrace tailWord_274671 prefixEnd_274671 47012748283733360716439 := by
  unfold tailWord_274671
  simp only [CollatzResearch.WordTrace]
  refine ⟨10018074387921351917207867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6678716258614234611471911 10018074387921351917207867)
  ·
    refine ⟨15027111581882027875811801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10018074387921351917207867 15027111581882027875811801)
    ·
      refine ⟨11270333686411520906858851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15027111581882027875811801 11270333686411520906858851)
      ·
        refine ⟨16905500529617281360288277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11270333686411520906858851 16905500529617281360288277)
        ·
          refine ⟨792445337325810063763513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16905500529617281360288277 792445337325810063763513)
          ·
            refine ⟨594334002994357547822635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792445337325810063763513 594334002994357547822635)
            ·
              refine ⟨891501004491536321733953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594334002994357547822635 891501004491536321733953)
              ·
                refine ⟨668625753368652241300465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891501004491536321733953 668625753368652241300465)
                ·
                  refine ⟨501469315026489180975349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668625753368652241300465 501469315026489180975349)
                  ·
                    refine ⟨47012748283733360716439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 501469315026489180975349 47012748283733360716439)
                    ·
                      rfl

theorem cell23_274671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_274671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274671 prefixEnd_274671 := by exact prefixLift 274671
  have htrace : WordTrace (prefixWord ++ tailWord_274671) baseStart_274671 baseEnd_274671 := by
    simpa [prefixWord, tailWord_274671, baseEnd_274671] using wordTrace_append hprefix tailTrace_274671
  have hstable : (prefixWord ++ tailWord_274671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274671).length < 2 ^ (prefixWord ++ tailWord_274671).sum := by decide
  have hdescent : baseEnd_274671 < baseStart_274671 := by decide
  rcases family_descends (prefixWord ++ tailWord_274671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274691 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 6, 2]
def baseStart_274691 : Nat := 118140960795 + 274691 * 2 ^ 59
def prefixEnd_274691 : Nat := 4983230072969 + 3 ^ 40 * 274691 * 2
def baseEnd_274691 : Nat := 141048514464290003899225

theorem tailTrace_274691 : CollatzResearch.WordTrace tailWord_274691 prefixEnd_274691 141048514464290003899225 := by
  unfold tailWord_274691
  simp only [CollatzResearch.WordTrace]
  refine ⟨10018803847848895332935927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6679202565232596888623951 10018803847848895332935927)
  ·
    refine ⟨15028205771773342999403891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10018803847848895332935927 15028205771773342999403891)
    ·
      refine ⟨22542308657660014499105837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15028205771773342999403891 22542308657660014499105837)
      ·
        refine ⟨8453365746622505437164689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22542308657660014499105837 8453365746622505437164689)
        ·
          refine ⟨6340024309966879077873517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8453365746622505437164689 6340024309966879077873517)
          ·
            refine ⟨2377509116237579654202569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6340024309966879077873517 2377509116237579654202569)
            ·
              refine ⟨1783131837178184740651927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377509116237579654202569 1783131837178184740651927)
              ·
                refine ⟨2674697755767277110977891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783131837178184740651927 2674697755767277110977891)
                ·
                  refine ⟨4012046633650915666466837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674697755767277110977891 4012046633650915666466837)
                  ·
                    refine ⟨188064685952386671865633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4012046633650915666466837 188064685952386671865633)
                    ·
                      refine ⟨141048514464290003899225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188064685952386671865633 141048514464290003899225)
                      ·
                        rfl

theorem cell23_274691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_274691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274691 prefixEnd_274691 := by exact prefixLift 274691
  have htrace : WordTrace (prefixWord ++ tailWord_274691) baseStart_274691 baseEnd_274691 := by
    simpa [prefixWord, tailWord_274691, baseEnd_274691] using wordTrace_append hprefix tailTrace_274691
  have hstable : (prefixWord ++ tailWord_274691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274691).length < 2 ^ (prefixWord ++ tailWord_274691).sum := by decide
  have hdescent : baseEnd_274691 < baseStart_274691 := by decide
  rcases family_descends (prefixWord ++ tailWord_274691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274735 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 1, 4]
def baseStart_274735 : Nat := 118140960795 + 274735 * 2 ^ 59
def prefixEnd_274735 : Nat := 4983230072969 + 3 ^ 40 * 274735 * 2
def baseEnd_274735 : Nat := 47023702537695943916341

theorem tailTrace_274735 : CollatzResearch.WordTrace tailWord_274735 prefixEnd_274735 47023702537695943916341 := by
  unfold tailWord_274735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020408659689490847537659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6680272439792993898358439 10020408659689490847537659)
  ·
    refine ⟨15030612989534236271306489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10020408659689490847537659 15030612989534236271306489)
    ·
      refine ⟨11272959742150677203479867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15030612989534236271306489 11272959742150677203479867)
      ·
        refine ⟨16909439613226015805219801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272959742150677203479867 16909439613226015805219801)
        ·
          refine ⟨12682079709919511853914851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16909439613226015805219801 12682079709919511853914851)
          ·
            refine ⟨19023119564879267780872277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12682079709919511853914851 19023119564879267780872277)
            ·
              refine ⟨222927182400928919307097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 19023119564879267780872277 222927182400928919307097)
              ·
                refine ⟨167195386800696689480323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222927182400928919307097 167195386800696689480323)
                ·
                  refine ⟨250793080201045034220485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167195386800696689480323 250793080201045034220485)
                  ·
                    refine ⟨47023702537695943916341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250793080201045034220485 47023702537695943916341)
                    ·
                      rfl

theorem cell23_274735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 4].length) (baseStart_274735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274735 prefixEnd_274735 := by exact prefixLift 274735
  have htrace : WordTrace (prefixWord ++ tailWord_274735) baseStart_274735 baseEnd_274735 := by
    simpa [prefixWord, tailWord_274735, baseEnd_274735] using wordTrace_append hprefix tailTrace_274735
  have hstable : (prefixWord ++ tailWord_274735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274735).length < 2 ^ (prefixWord ++ tailWord_274735).sum := by decide
  have hdescent : baseEnd_274735 < baseStart_274735 := by decide
  rcases family_descends (prefixWord ++ tailWord_274735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274761 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_274761 : Nat := 118140960795 + 274761 * 2 ^ 59
def prefixEnd_274761 : Nat := 4983230072969 + 3 ^ 40 * 274761 * 2
def baseEnd_274761 : Nat := 47028152703368243341301

theorem tailTrace_274761 : CollatzResearch.WordTrace tailWord_274761 prefixEnd_274761 47028152703368243341301 := by
  unfold tailWord_274761
  simp only [CollatzResearch.WordTrace]
  refine ⟨10021356957595297287984137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6680904638396864858656091 10021356957595297287984137)
  ·
    refine ⟨7516017718196472965988103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10021356957595297287984137 7516017718196472965988103)
    ·
      refine ⟨11274026577294709448982155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516017718196472965988103 11274026577294709448982155)
      ·
        refine ⟨16911039865942064173473233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11274026577294709448982155 16911039865942064173473233)
        ·
          refine ⟨12683279899456548130104925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16911039865942064173473233 12683279899456548130104925)
          ·
            refine ⟨4756229962296205548789347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12683279899456548130104925 4756229962296205548789347)
            ·
              refine ⟨7134344943444308323184021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756229962296205548789347 7134344943444308323184021)
              ·
                refine ⟨334422419223951952649251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7134344943444308323184021 334422419223951952649251)
                ·
                  refine ⟨501633628835927928973877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334422419223951952649251 501633628835927928973877)
                  ·
                    refine ⟨47028152703368243341301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 501633628835927928973877 47028152703368243341301)
                    ·
                      rfl

theorem cell23_274761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_274761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274761 prefixEnd_274761 := by exact prefixLift 274761
  have htrace : WordTrace (prefixWord ++ tailWord_274761) baseStart_274761 baseEnd_274761 := by
    simpa [prefixWord, tailWord_274761, baseEnd_274761] using wordTrace_append hprefix tailTrace_274761
  have hstable : (prefixWord ++ tailWord_274761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274761).length < 2 ^ (prefixWord ++ tailWord_274761).sum := by decide
  have hdescent : baseEnd_274761 < baseStart_274761 := by decide
  rcases family_descends (prefixWord ++ tailWord_274761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274768 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2]
def baseStart_274768 : Nat := 118140960795 + 274768 * 2 ^ 59
def prefixEnd_274768 : Nat := 4983230072969 + 3 ^ 40 * 274768 * 2
def baseEnd_274768 : Nat := 141088052474686202636371

theorem tailTrace_274768 : CollatzResearch.WordTrace tailWord_274768 prefixEnd_274768 141088052474686202636371 := by
  unfold tailWord_274768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010806134284968741744479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6681074845713291655659305 5010806134284968741744479)
  ·
    refine ⟨7516209201427453112616719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5010806134284968741744479 7516209201427453112616719)
    ·
      refine ⟨11274313802141179668925079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516209201427453112616719 11274313802141179668925079)
      ·
        refine ⟨16911470703211769503387619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11274313802141179668925079 16911470703211769503387619)
        ·
          refine ⟨25367206054817654255081429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16911470703211769503387619 25367206054817654255081429)
          ·
            refine ⟨594543891909788771603471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25367206054817654255081429 594543891909788771603471)
            ·
              refine ⟨891815837864683157405207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594543891909788771603471 891815837864683157405207)
              ·
                refine ⟨1337723756797024736107811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891815837864683157405207 1337723756797024736107811)
                ·
                  refine ⟨2006585635195537104161717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337723756797024736107811 2006585635195537104161717)
                  ·
                    refine ⟨188117403299581603515161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2006585635195537104161717 188117403299581603515161)
                    ·
                      refine ⟨141088052474686202636371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188117403299581603515161 141088052474686202636371)
                      ·
                        rfl

theorem cell23_274768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 5, 2].length) (baseStart_274768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274768 prefixEnd_274768 := by exact prefixLift 274768
  have htrace : WordTrace (prefixWord ++ tailWord_274768) baseStart_274768 baseEnd_274768 := by
    simpa [prefixWord, tailWord_274768, baseEnd_274768] using wordTrace_append hprefix tailTrace_274768
  have hstable : (prefixWord ++ tailWord_274768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274768).length < 2 ^ (prefixWord ++ tailWord_274768).sum := by decide
  have hdescent : baseEnd_274768 < baseStart_274768 := by decide
  rcases family_descends (prefixWord ++ tailWord_274768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274792 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_274792 : Nat := 118140960795 + 274792 * 2 ^ 59
def prefixEnd_274792 : Nat := 4983230072969 + 3 ^ 40 * 274792 * 2
def baseEnd_274792 : Nat := 141100376010394108736261

theorem tailTrace_274792 : CollatzResearch.WordTrace tailWord_274792 prefixEnd_274792 141100376010394108736261 := by
  unfold tailWord_274792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011243810241494791181315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6681658413655326388241753 5011243810241494791181315)
  ·
    refine ⟨7516865715362242186771973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011243810241494791181315 7516865715362242186771973)
    ·
      refine ⟨1409412321630420410019745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7516865715362242186771973 1409412321630420410019745)
      ·
        refine ⟨1057059241222815307514809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1409412321630420410019745 1057059241222815307514809)
        ·
          refine ⟨792794430917111480636107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057059241222815307514809 792794430917111480636107)
          ·
            refine ⟨1189191646375667220954161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792794430917111480636107 1189191646375667220954161)
            ·
              refine ⟨891893734781750415715621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189191646375667220954161 891893734781750415715621)
              ·
                refine ⟨167230075271578202946679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 891893734781750415715621 167230075271578202946679)
                ·
                  refine ⟨250845112907367304420019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167230075271578202946679 250845112907367304420019)
                  ·
                    refine ⟨376267669361050956630029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 250845112907367304420019 376267669361050956630029)
                    ·
                      refine ⟨141100376010394108736261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376267669361050956630029 141100376010394108736261)
                      ·
                        rfl

theorem cell23_274792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_274792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274792 prefixEnd_274792 := by exact prefixLift 274792
  have htrace : WordTrace (prefixWord ++ tailWord_274792) baseStart_274792 baseEnd_274792 := by
    simpa [prefixWord, tailWord_274792, baseEnd_274792] using wordTrace_append hprefix tailTrace_274792
  have hstable : (prefixWord ++ tailWord_274792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274792).length < 2 ^ (prefixWord ++ tailWord_274792).sum := by decide
  have hdescent : baseEnd_274792 < baseStart_274792 := by decide
  rcases family_descends (prefixWord ++ tailWord_274792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274811 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6]
def baseStart_274811 : Nat := 118140960795 + 274811 * 2 ^ 59
def prefixEnd_274811 : Nat := 4983230072969 + 3 ^ 40 * 274811 * 2
def baseEnd_274811 : Nat := 141110132142829534398673

theorem tailTrace_274811 : CollatzResearch.WordTrace tailWord_274811 prefixEnd_274811 141110132142829534398673 := by
  unfold tailWord_274811
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023180607414155827304287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6682120404942770551536191 10023180607414155827304287)
  ·
    refine ⟨15034770911121233740956431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10023180607414155827304287 15034770911121233740956431)
    ·
      refine ⟨22552156366681850611434647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15034770911121233740956431 22552156366681850611434647)
      ·
        refine ⟨33828234550022775917151971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22552156366681850611434647 33828234550022775917151971)
        ·
          refine ⟨50742351825034163875727957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33828234550022775917151971 50742351825034163875727957)
          ·
            refine ⟨594636935449619107918687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 50742351825034163875727957 594636935449619107918687)
            ·
              refine ⟨891955403174428661878031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594636935449619107918687 891955403174428661878031)
              ·
                refine ⟨1337933104761642992817047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891955403174428661878031 1337933104761642992817047)
                ·
                  refine ⟨2006899657142464489225571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337933104761642992817047 2006899657142464489225571)
                  ·
                    refine ⟨3010349485713696733838357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2006899657142464489225571 3010349485713696733838357)
                    ·
                      refine ⟨141110132142829534398673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3010349485713696733838357 141110132142829534398673)
                      ·
                        rfl

theorem cell23_274811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_274811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274811 prefixEnd_274811 := by exact prefixLift 274811
  have htrace : WordTrace (prefixWord ++ tailWord_274811) baseStart_274811 baseEnd_274811 := by
    simpa [prefixWord, tailWord_274811, baseEnd_274811] using wordTrace_append hprefix tailTrace_274811
  have hstable : (prefixWord ++ tailWord_274811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274811).length < 2 ^ (prefixWord ++ tailWord_274811).sum := by decide
  have hdescent : baseEnd_274811 < baseStart_274811 := by decide
  rcases family_descends (prefixWord ++ tailWord_274811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274826 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_274826 : Nat := 118140960795 + 274826 * 2 ^ 59
def prefixEnd_274826 : Nat := 4983230072969 + 3 ^ 40 * 274826 * 2
def baseEnd_274826 : Nat := 141117834352646975711105

theorem tailTrace_274826 : CollatzResearch.WordTrace tailWord_274826 prefixEnd_274826 141117834352646975711105 := by
  unfold tailWord_274826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505931925589953347275083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6682485134906542259400221 2505931925589953347275083)
  ·
    refine ⟨3758897888384930020912625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505931925589953347275083 3758897888384930020912625)
    ·
      refine ⟨2819173416288697515684469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3758897888384930020912625 2819173416288697515684469)
      ·
        refine ⟨264297507777065392095419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2819173416288697515684469 264297507777065392095419)
        ·
          refine ⟨396446261665598088143129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264297507777065392095419 396446261665598088143129)
          ·
            refine ⟨297334696249198566107347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396446261665598088143129 297334696249198566107347)
            ·
              refine ⟨446002044373797849161021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297334696249198566107347 446002044373797849161021)
              ·
                refine ⟨167250766640174193435383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446002044373797849161021 167250766640174193435383)
                ·
                  refine ⟨250876149960261290153075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167250766640174193435383 250876149960261290153075)
                  ·
                    refine ⟨376314224940391935229613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 250876149960261290153075 376314224940391935229613)
                    ·
                      refine ⟨141117834352646975711105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376314224940391935229613 141117834352646975711105)
                      ·
                        rfl

theorem cell23_274826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_274826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274826 prefixEnd_274826 := by exact prefixLift 274826
  have htrace : WordTrace (prefixWord ++ tailWord_274826) baseStart_274826 baseEnd_274826 := by
    simpa [prefixWord, tailWord_274826, baseEnd_274826] using wordTrace_append hprefix tailTrace_274826
  have hstable : (prefixWord ++ tailWord_274826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274826).length < 2 ^ (prefixWord ++ tailWord_274826).sum := by decide
  have hdescent : baseEnd_274826 < baseStart_274826 := by decide
  rcases family_descends (prefixWord ++ tailWord_274826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274869 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_274869 : Nat := 118140960795 + 274869 * 2 ^ 59
def prefixEnd_274869 : Nat := 4983230072969 + 3 ^ 40 * 274869 * 2
def baseEnd_274869 : Nat := 141139914020790307473407

theorem tailTrace_274869 : CollatzResearch.WordTrace tailWord_274869 prefixEnd_274869 141139914020790307473407 := by
  unfold tailWord_274869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10025296041204031732915661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6683530694136021155277107 10025296041204031732915661)
  ·
    refine ⟨3759486015451511899843373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10025296041204031732915661 3759486015451511899843373)
    ·
      refine ⟨1409807255794316962441265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3759486015451511899843373 1409807255794316962441265)
      ·
        refine ⟨1057355441845737721830949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1409807255794316962441265 1057355441845737721830949)
        ·
          refine ⟨198254145346075822843303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1057355441845737721830949 198254145346075822843303)
          ·
            refine ⟨297381218019113734264955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198254145346075822843303 297381218019113734264955)
            ·
              refine ⟨446071827028670601397433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297381218019113734264955 446071827028670601397433)
              ·
                refine ⟨334553870271502951048075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446071827028670601397433 334553870271502951048075)
                ·
                  refine ⟨501830805407254426572113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334553870271502951048075 501830805407254426572113)
                  ·
                    refine ⟨376373104055440819929085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501830805407254426572113 376373104055440819929085)
                    ·
                      refine ⟨141139914020790307473407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376373104055440819929085 141139914020790307473407)
                      ·
                        rfl

theorem cell23_274869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_274869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274869 prefixEnd_274869 := by exact prefixLift 274869
  have htrace : WordTrace (prefixWord ++ tailWord_274869) baseStart_274869 baseEnd_274869 := by
    simpa [prefixWord, tailWord_274869, baseEnd_274869] using wordTrace_append hprefix tailTrace_274869
  have hstable : (prefixWord ++ tailWord_274869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274869).length < 2 ^ (prefixWord ++ tailWord_274869).sum := by decide
  have hdescent : baseEnd_274869 < baseStart_274869 := by decide
  rcases family_descends (prefixWord ++ tailWord_274869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274922 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_274922 : Nat := 118140960795 + 274922 * 2 ^ 59
def prefixEnd_274922 : Nat := 4983230072969 + 3 ^ 40 * 274922 * 2
def baseEnd_274922 : Nat := 141167128495478600110663

theorem tailTrace_274922 : CollatzResearch.WordTrace tailWord_274922 prefixEnd_274922 141167128495478600110663 := by
  unfold tailWord_274922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506807277503005446148755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6684819406674681189730013 2506807277503005446148755)
  ·
    refine ⟨3760210916254508169223133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2506807277503005446148755 3760210916254508169223133)
    ·
      refine ⟨1410079093595440563458675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3760210916254508169223133 1410079093595440563458675)
      ·
        refine ⟨2115118640393160845188013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410079093595440563458675 2115118640393160845188013)
        ·
          refine ⟨793169490147435316945505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2115118640393160845188013 793169490147435316945505)
          ·
            refine ⟨594877117610576487709129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793169490147435316945505 594877117610576487709129)
            ·
              refine ⟨446157838207932365781847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594877117610576487709129 446157838207932365781847)
              ·
                refine ⟨669236757311898548672771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446157838207932365781847 669236757311898548672771)
                ·
                  refine ⟨1003855135967847823009157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669236757311898548672771 1003855135967847823009157)
                  ·
                    refine ⟨188222837993971466814217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003855135967847823009157 188222837993971466814217)
                    ·
                      refine ⟨141167128495478600110663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188222837993971466814217 141167128495478600110663)
                      ·
                        rfl

theorem cell23_274922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_274922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274922 prefixEnd_274922 := by exact prefixLift 274922
  have htrace : WordTrace (prefixWord ++ tailWord_274922) baseStart_274922 baseEnd_274922 := by
    simpa [prefixWord, tailWord_274922, baseEnd_274922] using wordTrace_append hprefix tailTrace_274922
  have hstable : (prefixWord ++ tailWord_274922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274922).length < 2 ^ (prefixWord ++ tailWord_274922).sum := by decide
  have hdescent : baseEnd_274922 < baseStart_274922 := by decide
  rcases family_descends (prefixWord ++ tailWord_274922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274945 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 5]
def baseStart_274945 : Nat := 118140960795 + 274945 * 2 ^ 59
def prefixEnd_274945 : Nat := 4983230072969 + 3 ^ 40 * 274945 * 2
def baseEnd_274945 : Nat := 15686548727836890013673

theorem tailTrace_274945 : CollatzResearch.WordTrace tailWord_274945 prefixEnd_274945 15686548727836890013673 := by
  unfold tailWord_274945
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028067988928696712682289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6685378659285797808454859 10028067988928696712682289)
  ·
    refine ⟨7521050991696522534511717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10028067988928696712682289 7521050991696522534511717)
    ·
      refine ⟨1410197060943097975220947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7521050991696522534511717 1410197060943097975220947)
      ·
        refine ⟨2115295591414646962831421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410197060943097975220947 2115295591414646962831421)
        ·
          refine ⟨793235846780492611061783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2115295591414646962831421 793235846780492611061783)
          ·
            refine ⟨1189853770170738916592675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793235846780492611061783 1189853770170738916592675)
            ·
              refine ⟨1784780655256108374889013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189853770170738916592675 1784780655256108374889013)
              ·
                refine ⟨167323186430260160145845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1784780655256108374889013 167323186430260160145845)
                ·
                  refine ⟨15686548727836890013673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167323186430260160145845 15686548727836890013673)
                  ·
                    rfl

theorem cell23_274945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 5].length) (baseStart_274945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274945 prefixEnd_274945 := by exact prefixLift 274945
  have htrace : WordTrace (prefixWord ++ tailWord_274945) baseStart_274945 baseEnd_274945 := by
    simpa [prefixWord, tailWord_274945, baseEnd_274945] using wordTrace_append hprefix tailTrace_274945
  have hstable : (prefixWord ++ tailWord_274945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274945).length < 2 ^ (prefixWord ++ tailWord_274945).sum := by decide
  have hdescent : baseEnd_274945 < baseStart_274945 := by decide
  rcases family_descends (prefixWord ++ tailWord_274945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274996 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 5]
def baseStart_274996 : Nat := 118140960795 + 274996 * 2 ^ 59
def prefixEnd_274996 : Nat := 4983230072969 + 3 ^ 40 * 274996 * 2
def baseEnd_274996 : Nat := 15689458451545701176147

theorem tailTrace_274996 : CollatzResearch.WordTrace tailWord_274996 prefixEnd_274996 15689458451545701176147 := by
  unfold tailWord_274996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014964055871966211394421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6686618741162621615192561 5014964055871966211394421)
  ·
    refine ⟨470152880237996832318227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5014964055871966211394421 470152880237996832318227)
    ·
      refine ⟨705229320356995248477341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470152880237996832318227 705229320356995248477341)
      ·
        refine ⟨264460995133873218179003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 705229320356995248477341 264460995133873218179003)
        ·
          refine ⟨396691492700809827268505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264460995133873218179003 396691492700809827268505)
          ·
            refine ⟨297518619525607370451379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396691492700809827268505 297518619525607370451379)
            ·
              refine ⟨446277929288411055677069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297518619525607370451379 446277929288411055677069)
              ·
                refine ⟨167354223483154145878901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446277929288411055677069 167354223483154145878901)
                ·
                  refine ⟨15689458451545701176147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167354223483154145878901 15689458451545701176147)
                  ·
                    rfl

theorem cell23_274996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_274996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_274996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_274996 prefixEnd_274996 := by exact prefixLift 274996
  have htrace : WordTrace (prefixWord ++ tailWord_274996) baseStart_274996 baseEnd_274996 := by
    simpa [prefixWord, tailWord_274996, baseEnd_274996] using wordTrace_append hprefix tailTrace_274996
  have hstable : (prefixWord ++ tailWord_274996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274996).length < 2 ^ (prefixWord ++ tailWord_274996).sum := by decide
  have hdescent : baseEnd_274996 < baseStart_274996 := by decide
  rcases family_descends (prefixWord ++ tailWord_274996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275015 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_275015 : Nat := 118140960795 + 275015 * 2 ^ 59
def prefixEnd_275015 : Nat := 4983230072969 + 3 ^ 40 * 275015 * 2
def baseEnd_275015 : Nat := 141214882196346736247735

theorem tailTrace_275015 : CollatzResearch.WordTrace tailWord_275015 prefixEnd_275015 141214882196346736247735 := by
  unfold tailWord_275015
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030621098675098667730499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6687080732450065778486999 10030621098675098667730499)
  ·
    refine ⟨15045931648012648001595749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030621098675098667730499 15045931648012648001595749)
    ·
      refine ⟨2821112184002371500299203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15045931648012648001595749 2821112184002371500299203)
      ·
        refine ⟨4231668276003557250448805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821112184002371500299203 4231668276003557250448805)
        ·
          refine ⟨793437801750666984459151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4231668276003557250448805 793437801750666984459151)
          ·
            refine ⟨1190156702626000476688727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793437801750666984459151 1190156702626000476688727)
            ·
              refine ⟨1785235053939000715033091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190156702626000476688727 1785235053939000715033091)
              ·
                refine ⟨2677852580908501072549637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785235053939000715033091 2677852580908501072549637)
                ·
                  refine ⟨502097358920343951103057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2677852580908501072549637 502097358920343951103057)
                  ·
                    refine ⟨376573019190257963327293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502097358920343951103057 376573019190257963327293)
                    ·
                      refine ⟨141214882196346736247735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376573019190257963327293 141214882196346736247735)
                      ·
                        rfl

theorem cell23_275015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_275015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275015 prefixEnd_275015 := by exact prefixLift 275015
  have htrace : WordTrace (prefixWord ++ tailWord_275015) baseStart_275015 baseEnd_275015 := by
    simpa [prefixWord, tailWord_275015, baseEnd_275015] using wordTrace_append hprefix tailTrace_275015
  have hstable : (prefixWord ++ tailWord_275015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275015).length < 2 ^ (prefixWord ++ tailWord_275015).sum := by decide
  have hdescent : baseEnd_275015 < baseStart_275015 := by decide
  rcases family_descends (prefixWord ++ tailWord_275015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275018 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_275018 : Nat := 118140960795 + 275018 * 2 ^ 59
def prefixEnd_275018 : Nat := 4983230072969 + 3 ^ 40 * 275018 * 2
def baseEnd_275018 : Nat := 15690713626478913834469

theorem tailTrace_275018 : CollatzResearch.WordTrace tailWord_275018 prefixEnd_275018 15690713626478913834469 := by
  unfold tailWord_275018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507682629416057545022427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6687153678442820120059805 2507682629416057545022427)
  ·
    refine ⟨3761523944124086317533641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2507682629416057545022427 3761523944124086317533641)
    ·
      refine ⟨2821142958093064738150231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3761523944124086317533641 2821142958093064738150231)
      ·
        refine ⟨4231714437139597107225347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821142958093064738150231 4231714437139597107225347)
        ·
          refine ⟨6347571655709395660838021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231714437139597107225347 6347571655709395660838021)
          ·
            refine ⟨1190169685445511686407129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6347571655709395660838021 1190169685445511686407129)
            ·
              refine ⟨892627264084133764805347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190169685445511686407129 892627264084133764805347)
              ·
                refine ⟨1338940896126200647208021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892627264084133764805347 1338940896126200647208021)
                ·
                  refine ⟨15690713626478913834469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1338940896126200647208021 15690713626478913834469)
                  ·
                    rfl

theorem cell23_275018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_275018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275018 prefixEnd_275018 := by exact prefixLift 275018
  have htrace : WordTrace (prefixWord ++ tailWord_275018) baseStart_275018 baseEnd_275018 := by
    simpa [prefixWord, tailWord_275018, baseEnd_275018] using wordTrace_append hprefix tailTrace_275018
  have hstable : (prefixWord ++ tailWord_275018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275018).length < 2 ^ (prefixWord ++ tailWord_275018).sum := by decide
  have hdescent : baseEnd_275018 < baseStart_275018 := by decide
  rcases family_descends (prefixWord ++ tailWord_275018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275022 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_275022 : Nat := 118140960795 + 275022 * 2 ^ 59
def prefixEnd_275022 : Nat := 4983230072969 + 3 ^ 40 * 275022 * 2
def baseEnd_275022 : Nat := 47072825520309402953401

theorem tailTrace_275022 : CollatzResearch.WordTrace tailWord_275022 prefixEnd_275022 47072825520309402953401 := by
  unfold tailWord_275022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253859551206217357904415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6687250939766492575490213 1253859551206217357904415)
  ·
    refine ⟨1880789326809326036856623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253859551206217357904415 1880789326809326036856623)
    ·
      refine ⟨2821183990213989055284935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880789326809326036856623 2821183990213989055284935)
      ·
        refine ⟨4231775985320983582927403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821183990213989055284935 4231775985320983582927403)
        ·
          refine ⟨6347663977981475374391105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231775985320983582927403 6347663977981475374391105)
          ·
            refine ⟨4760747983486106530793329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347663977981475374391105 4760747983486106530793329)
            ·
              refine ⟨3570560987614579898094997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760747983486106530793329 3570560987614579898094997)
              ·
                refine ⟨167370046294433432723203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3570560987614579898094997 167370046294433432723203)
                ·
                  refine ⟨251055069441650149084805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167370046294433432723203 251055069441650149084805)
                  ·
                    refine ⟨47072825520309402953401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251055069441650149084805 47072825520309402953401)
                    ·
                      rfl

theorem cell23_275022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_275022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275022 prefixEnd_275022 := by exact prefixLift 275022
  have htrace : WordTrace (prefixWord ++ tailWord_275022) baseStart_275022 baseEnd_275022 := by
    simpa [prefixWord, tailWord_275022, baseEnd_275022] using wordTrace_append hprefix tailTrace_275022
  have hstable : (prefixWord ++ tailWord_275022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275022).length < 2 ^ (prefixWord ++ tailWord_275022).sum := by decide
  have hdescent : baseEnd_275022 < baseStart_275022 := by decide
  rcases family_descends (prefixWord ++ tailWord_275022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275055 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 5, 2]
def baseStart_275055 : Nat := 118140960795 + 275055 * 2 ^ 59
def prefixEnd_275055 : Nat := 4983230072969 + 3 ^ 40 * 275055 * 2
def baseEnd_275055 : Nat := 141235421422526579747551

theorem tailTrace_275055 : CollatzResearch.WordTrace tailWord_275055 prefixEnd_275055 141235421422526579747551 := by
  unfold tailWord_275055
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032080018530185499186619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6688053345686790332791079 10032080018530185499186619)
  ·
    refine ⟨15048120027795278248779929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10032080018530185499186619 15048120027795278248779929)
    ·
      refine ⟨11286090020846458686584947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15048120027795278248779929 11286090020846458686584947)
      ·
        refine ⟨16929135031269688029877421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286090020846458686584947 16929135031269688029877421)
        ·
          refine ⟨6348425636726133011204033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16929135031269688029877421 6348425636726133011204033)
          ·
            refine ⟨4761319227544599758403025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6348425636726133011204033 4761319227544599758403025)
            ·
              refine ⟨3570989420658449818802269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761319227544599758403025 3570989420658449818802269)
              ·
                refine ⟨1339121032746918682050851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3570989420658449818802269 1339121032746918682050851)
                ·
                  refine ⟨2008681549120378023076277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339121032746918682050851 2008681549120378023076277)
                  ·
                    refine ⟨188313895230035439663401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2008681549120378023076277 188313895230035439663401)
                    ·
                      refine ⟨141235421422526579747551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188313895230035439663401 141235421422526579747551)
                      ·
                        rfl

theorem cell23_275055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5, 2].length) (baseStart_275055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275055 prefixEnd_275055 := by exact prefixLift 275055
  have htrace : WordTrace (prefixWord ++ tailWord_275055) baseStart_275055 baseEnd_275055 := by
    simpa [prefixWord, tailWord_275055, baseEnd_275055] using wordTrace_append hprefix tailTrace_275055
  have hstable : (prefixWord ++ tailWord_275055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275055).length < 2 ^ (prefixWord ++ tailWord_275055).sum := by decide
  have hdescent : baseEnd_275055 < baseStart_275055 := by decide
  rcases family_descends (prefixWord ++ tailWord_275055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275072 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2]
def baseStart_275072 : Nat := 118140960795 + 275072 * 2 ^ 59
def prefixEnd_275072 : Nat := 4983230072969 + 3 ^ 40 * 275072 * 2
def baseEnd_275072 : Nat := 141244150593653013234973

theorem tailTrace_275072 : CollatzResearch.WordTrace tailWord_275072 prefixEnd_275072 141244150593653013234973 := by
  unfold tailWord_275072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016350029734298701277735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6688466706312398268370313 5016350029734298701277735)
  ·
    refine ⟨7524525044601448051916603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016350029734298701277735 7524525044601448051916603)
    ·
      refine ⟨11286787566902172077874905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7524525044601448051916603 11286787566902172077874905)
      ·
        refine ⟨8465090675176629058406179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11286787566902172077874905 8465090675176629058406179)
        ·
          refine ⟨12697636012764943587609269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8465090675176629058406179 12697636012764943587609269)
          ·
            refine ⟨1190403376196713461338369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12697636012764943587609269 1190403376196713461338369)
            ·
              refine ⟨892802532147535096003777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190403376196713461338369 892802532147535096003777)
              ·
                refine ⟨669601899110651322002833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892802532147535096003777 669601899110651322002833)
                ·
                  refine ⟨502201424332988491502125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669601899110651322002833 502201424332988491502125)
                  ·
                    refine ⟨188325534124870684313297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502201424332988491502125 188325534124870684313297)
                    ·
                      refine ⟨141244150593653013234973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188325534124870684313297 141244150593653013234973)
                      ·
                        rfl

theorem cell23_275072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_275072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275072 prefixEnd_275072 := by exact prefixLift 275072
  have htrace : WordTrace (prefixWord ++ tailWord_275072) baseStart_275072 baseEnd_275072 := by
    simpa [prefixWord, tailWord_275072, baseEnd_275072] using wordTrace_append hprefix tailTrace_275072
  have hstable : (prefixWord ++ tailWord_275072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275072).length < 2 ^ (prefixWord ++ tailWord_275072).sum := by decide
  have hdescent : baseEnd_275072 < baseStart_275072 := by decide
  rcases family_descends (prefixWord ++ tailWord_275072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275079 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_275079 : Nat := 118140960795 + 275079 * 2 ^ 59
def prefixEnd_275079 : Nat := 4983230072969 + 3 ^ 40 * 275079 * 2
def baseEnd_275079 : Nat := 141247744958234485847441

theorem tailTrace_275079 : CollatzResearch.WordTrace tailWord_275079 prefixEnd_275079 141247744958234485847441 := by
  unfold tailWord_275079
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032955370443237598060291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6688636913628825065373527 10032955370443237598060291)
  ·
    refine ⟨15049433055664856397090437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10032955370443237598060291 15049433055664856397090437)
    ·
      refine ⟨2821768697937160574454457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15049433055664856397090437 2821768697937160574454457)
      ·
        refine ⟨2116326523452870430840843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2821768697937160574454457 2116326523452870430840843)
        ·
          refine ⟨3174489785179305646261265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116326523452870430840843 3174489785179305646261265)
          ·
            refine ⟨2380867338884479234695949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3174489785179305646261265 2380867338884479234695949)
            ·
              refine ⟨892825252081679713010981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2380867338884479234695949 892825252081679713010981)
              ·
                refine ⟨167404734765314946189559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 892825252081679713010981 167404734765314946189559)
                ·
                  refine ⟨251107102147972419284339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167404734765314946189559 251107102147972419284339)
                  ·
                    refine ⟨376660653221958628926509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251107102147972419284339 376660653221958628926509)
                    ·
                      refine ⟨141247744958234485847441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376660653221958628926509 141247744958234485847441)
                      ·
                        rfl

theorem cell23_275079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_275079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275079 prefixEnd_275079 := by exact prefixLift 275079
  have htrace : WordTrace (prefixWord ++ tailWord_275079) baseStart_275079 baseEnd_275079 := by
    simpa [prefixWord, tailWord_275079, baseEnd_275079] using wordTrace_append hprefix tailTrace_275079
  have hstable : (prefixWord ++ tailWord_275079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275079).length < 2 ^ (prefixWord ++ tailWord_275079).sum := by decide
  have hdescent : baseEnd_275079 < baseStart_275079 := by decide
  rcases family_descends (prefixWord ++ tailWord_275079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275095 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 1, 6]
def baseStart_275095 : Nat := 118140960795 + 275095 * 2 ^ 59
def prefixEnd_275095 : Nat := 4983230072969 + 3 ^ 40 * 275095 * 2
def baseEnd_275095 : Nat := 47085320216235474415789

theorem tailTrace_275095 : CollatzResearch.WordTrace tailWord_275095 prefixEnd_275095 47085320216235474415789 := by
  unfold tailWord_275095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033538938385272330642739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6689025958923514887095159 10033538938385272330642739)
  ·
    refine ⟨15050308407577908495964109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10033538938385272330642739 15050308407577908495964109)
    ·
      refine ⟨5643865652841715685986541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15050308407577908495964109 5643865652841715685986541)
      ·
        refine ⟨2116449619815643382244953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5643865652841715685986541 2116449619815643382244953)
        ·
          refine ⟨1587337214861732536683715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2116449619815643382244953 1587337214861732536683715)
          ·
            refine ⟨2381005822292598805025573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587337214861732536683715 2381005822292598805025573)
            ·
              refine ⟨446438591679862275942295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2381005822292598805025573 446438591679862275942295)
              ·
                refine ⟨669657887519793413913443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446438591679862275942295 669657887519793413913443)
                ·
                  refine ⟨1004486831279690120870165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669657887519793413913443 1004486831279690120870165)
                  ·
                    refine ⟨47085320216235474415789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1004486831279690120870165 47085320216235474415789)
                    ·
                      rfl

theorem cell23_275095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_275095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275095 prefixEnd_275095 := by exact prefixLift 275095
  have htrace : WordTrace (prefixWord ++ tailWord_275095) baseStart_275095 baseEnd_275095 := by
    simpa [prefixWord, tailWord_275095, baseEnd_275095] using wordTrace_append hprefix tailTrace_275095
  have hstable : (prefixWord ++ tailWord_275095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275095).length < 2 ^ (prefixWord ++ tailWord_275095).sum := by decide
  have hdescent : baseEnd_275095 < baseStart_275095 := by decide
  rcases family_descends (prefixWord ++ tailWord_275095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275102 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_275102 : Nat := 118140960795 + 275102 * 2 ^ 59
def prefixEnd_275102 : Nat := 4983230072969 + 3 ^ 40 * 275102 * 2
def baseEnd_275102 : Nat := 141259555013287895859835

theorem tailTrace_275102 : CollatzResearch.WordTrace tailWord_275102 prefixEnd_275102 141259555013287895859835 := by
  unfold tailWord_275102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254224281169989065768445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6689196166239941684098373 1254224281169989065768445)
  ·
    refine ⟨470334105438745899663167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1254224281169989065768445 470334105438745899663167)
    ·
      refine ⟨705501158158118849494751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470334105438745899663167 705501158158118849494751)
      ·
        refine ⟨1058251737237178274242127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705501158158118849494751 1058251737237178274242127)
        ·
          refine ⟨1587377605855767411363191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058251737237178274242127 1587377605855767411363191)
          ·
            refine ⟨2381066408783651117044787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587377605855767411363191 2381066408783651117044787)
            ·
              refine ⟨3571599613175476675567181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381066408783651117044787 3571599613175476675567181)
              ·
                refine ⟨1339349854940803753337693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3571599613175476675567181 1339349854940803753337693)
                ·
                  refine ⟨502256195602801407501635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1339349854940803753337693 502256195602801407501635)
                  ·
                    refine ⟨753384293404202111252453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502256195602801407501635 753384293404202111252453)
                    ·
                      refine ⟨141259555013287895859835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 753384293404202111252453 141259555013287895859835)
                      ·
                        rfl

theorem cell23_275102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_275102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275102 prefixEnd_275102 := by exact prefixLift 275102
  have htrace : WordTrace (prefixWord ++ tailWord_275102) baseStart_275102 baseEnd_275102 := by
    simpa [prefixWord, tailWord_275102, baseEnd_275102] using wordTrace_append hprefix tailTrace_275102
  have hstable : (prefixWord ++ tailWord_275102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275102).length < 2 ^ (prefixWord ++ tailWord_275102).sum := by decide
  have hdescent : baseEnd_275102 < baseStart_275102 := by decide
  rcases family_descends (prefixWord ++ tailWord_275102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275119 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 1, 1, 4]
def baseStart_275119 : Nat := 118140960795 + 275119 * 2 ^ 59
def prefixEnd_275119 : Nat := 4983230072969 + 3 ^ 40 * 275119 * 2
def baseEnd_275119 : Nat := 141268284184414329347257

theorem tailTrace_275119 : CollatzResearch.WordTrace tailWord_275119 prefixEnd_275119 141268284184414329347257 := by
  unfold tailWord_275119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10034414290298324429516411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6689609526865549619677607 10034414290298324429516411)
  ·
    refine ⟨15051621435447486644274617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10034414290298324429516411 15051621435447486644274617)
    ·
      refine ⟨11288716076585614983205963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15051621435447486644274617 11288716076585614983205963)
      ·
        refine ⟨16933074114878422474808945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11288716076585614983205963 16933074114878422474808945)
        ·
          refine ⟨12699805586158816856106709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16933074114878422474808945 12699805586158816856106709)
          ·
            refine ⟨297651693425597270065001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12699805586158816856106709 297651693425597270065001)
            ·
              refine ⟨223238770069197952548751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297651693425597270065001 223238770069197952548751)
              ·
                refine ⟨334858155103796928823127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223238770069197952548751 334858155103796928823127)
                ·
                  refine ⟨502287232655695393234691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334858155103796928823127 502287232655695393234691)
                  ·
                    refine ⟨753430848983543089852037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502287232655695393234691 753430848983543089852037)
                    ·
                      refine ⟨141268284184414329347257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 753430848983543089852037 141268284184414329347257)
                      ·
                        rfl

theorem cell23_275119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 1, 4].length) (baseStart_275119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275119 prefixEnd_275119 := by exact prefixLift 275119
  have htrace : WordTrace (prefixWord ++ tailWord_275119) baseStart_275119 baseEnd_275119 := by
    simpa [prefixWord, tailWord_275119, baseEnd_275119] using wordTrace_append hprefix tailTrace_275119
  have hstable : (prefixWord ++ tailWord_275119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275119).length < 2 ^ (prefixWord ++ tailWord_275119).sum := by decide
  have hdescent : baseEnd_275119 < baseStart_275119 := by decide
  rcases family_descends (prefixWord ++ tailWord_275119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275125 : List Nat := [1, 3, 3, 3, 1, 2, 10]
def baseStart_275125 : Nat := 118140960795 + 275125 * 2 ^ 59
def prefixEnd_275125 : Nat := 4983230072969 + 3 ^ 40 * 275125 * 2
def baseEnd_275125 : Nat := 1744090926769645751509

theorem tailTrace_275125 : CollatzResearch.WordTrace tailWord_275125 prefixEnd_275125 1744090926769645751509 := by
  unfold tailWord_275125
  simp only [CollatzResearch.WordTrace]
  refine ⟨10034633128276587454234829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6689755418851058302823219 10034633128276587454234829)
  ·
    refine ⟨3762987423103720295338061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10034633128276587454234829 3762987423103720295338061)
    ·
      refine ⟨1411120283663895110751773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3762987423103720295338061 1411120283663895110751773)
      ·
        refine ⟨529170106373960666531915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1411120283663895110751773 529170106373960666531915)
        ·
          refine ⟨793755159560940999797873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529170106373960666531915 793755159560940999797873)
          ·
            refine ⟨595316369670705749848405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793755159560940999797873 595316369670705749848405)
            ·
              refine ⟨1744090926769645751509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 595316369670705749848405 1744090926769645751509)
              ·
                rfl

theorem cell23_275125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 10].length) (baseStart_275125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275125 prefixEnd_275125 := by exact prefixLift 275125
  have htrace : WordTrace (prefixWord ++ tailWord_275125) baseStart_275125 baseEnd_275125 := by
    simpa [prefixWord, tailWord_275125, baseEnd_275125] using wordTrace_append hprefix tailTrace_275125
  have hstable : (prefixWord ++ tailWord_275125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275125).length < 2 ^ (prefixWord ++ tailWord_275125).sum := by decide
  have hdescent : baseEnd_275125 < baseStart_275125 := by decide
  rcases family_descends (prefixWord ++ tailWord_275125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275128 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_275128 : Nat := 118140960795 + 275128 * 2 ^ 59
def prefixEnd_275128 : Nat := 4983230072969 + 3 ^ 40 * 275128 * 2
def baseEnd_275128 : Nat := 141272905510304794134715

theorem tailTrace_275128 : CollatzResearch.WordTrace tailWord_275128 prefixEnd_275128 141272905510304794134715 := by
  unfold tailWord_275128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017371273632859483297019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6689828364843812644396025 5017371273632859483297019)
  ·
    refine ⟨7526056910449289224945529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017371273632859483297019 7526056910449289224945529)
    ·
      refine ⟨5644542682836966918709147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7526056910449289224945529 5644542682836966918709147)
      ·
        refine ⟨8466814024255450378063721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644542682836966918709147 8466814024255450378063721)
        ·
          refine ⟨6350110518191587783547791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8466814024255450378063721 6350110518191587783547791)
          ·
            refine ⟨9525165777287381675321687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350110518191587783547791 9525165777287381675321687)
            ·
              refine ⟨14287748665931072512982531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525165777287381675321687 14287748665931072512982531)
              ·
                refine ⟨21431622998896608769473797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14287748665931072512982531 21431622998896608769473797)
                ·
                  refine ⟨4018429312293114144276337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21431622998896608769473797 4018429312293114144276337)
                  ·
                    refine ⟨3013821984219835608207253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4018429312293114144276337 3013821984219835608207253)
                    ·
                      refine ⟨141272905510304794134715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3013821984219835608207253 141272905510304794134715)
                      ·
                        rfl

theorem cell23_275128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_275128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275128 prefixEnd_275128 := by exact prefixLift 275128
  have htrace : WordTrace (prefixWord ++ tailWord_275128) baseStart_275128 baseEnd_275128 := by
    simpa [prefixWord, tailWord_275128, baseEnd_275128] using wordTrace_append hprefix tailTrace_275128
  have hstable : (prefixWord ++ tailWord_275128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275128).length < 2 ^ (prefixWord ++ tailWord_275128).sum := by decide
  have hdescent : baseEnd_275128 < baseStart_275128 := by decide
  rcases family_descends (prefixWord ++ tailWord_275128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275136 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 1, 2, 2]
def baseStart_275136 : Nat := 118140960795 + 275136 * 2 ^ 59
def prefixEnd_275136 : Nat := 4983230072969 + 3 ^ 40 * 275136 * 2
def baseEnd_275136 : Nat := 141277013355540762834679

theorem tailTrace_275136 : CollatzResearch.WordTrace tailWord_275136 prefixEnd_275136 141277013355540762834679 := by
  unfold tailWord_275136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017517165618368166442631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6690022887491157555256841 5017517165618368166442631)
  ·
    refine ⟨7526275748427552249663947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017517165618368166442631 7526275748427552249663947)
    ·
      refine ⟨11289413622641328374495921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7526275748427552249663947 11289413622641328374495921)
      ·
        refine ⟨8467060216980996280871941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11289413622641328374495921 8467060216980996280871941)
        ·
          refine ⟨1587573790683936802663489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8467060216980996280871941 1587573790683936802663489)
          ·
            refine ⟨1190680343012952601997617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587573790683936802663489 1190680343012952601997617)
            ·
              refine ⟨893010257259714451498213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190680343012952601997617 893010257259714451498213)
              ·
                refine ⟨167439423236196459655915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 893010257259714451498213 167439423236196459655915)
                ·
                  refine ⟨251159134854294689483873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167439423236196459655915 251159134854294689483873)
                  ·
                    refine ⟨188369351140721017112905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251159134854294689483873 188369351140721017112905)
                    ·
                      refine ⟨141277013355540762834679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188369351140721017112905 141277013355540762834679)
                      ·
                        rfl

theorem cell23_275136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_275136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275136 prefixEnd_275136 := by exact prefixLift 275136
  have htrace : WordTrace (prefixWord ++ tailWord_275136) baseStart_275136 baseEnd_275136 := by
    simpa [prefixWord, tailWord_275136, baseEnd_275136] using wordTrace_append hprefix tailTrace_275136
  have hstable : (prefixWord ++ tailWord_275136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275136).length < 2 ^ (prefixWord ++ tailWord_275136).sum := by decide
  have hdescent : baseEnd_275136 < baseStart_275136 := by decide
  rcases family_descends (prefixWord ++ tailWord_275136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275149 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_275149 : Nat := 118140960795 + 275149 * 2 ^ 59
def prefixEnd_275149 : Nat := 4983230072969 + 3 ^ 40 * 275149 * 2
def baseEnd_275149 : Nat := 141283688604049211972119

theorem tailTrace_275149 : CollatzResearch.WordTrace tailWord_275149 prefixEnd_275149 141283688604049211972119 := by
  unfold tailWord_275149
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035508480189639553108501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6690338986793093035405667 10035508480189639553108501)
  ·
    refine ⟨470414460008889354051961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10035508480189639553108501 470414460008889354051961)
    ·
      refine ⟨352810845006667015538971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 470414460008889354051961 352810845006667015538971)
      ·
        refine ⟨529216267510000523308457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352810845006667015538971 529216267510000523308457)
        ·
          refine ⟨396912200632500392481343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529216267510000523308457 396912200632500392481343)
          ·
            refine ⟨595368300948750588722015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396912200632500392481343 595368300948750588722015)
            ·
              refine ⟨893052451423125883083023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595368300948750588722015 893052451423125883083023)
              ·
                refine ⟨1339578677134688824624535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893052451423125883083023 1339578677134688824624535)
                ·
                  refine ⟨2009368015702033236936803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339578677134688824624535 2009368015702033236936803)
                  ·
                    refine ⟨3014052023553049855405205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009368015702033236936803 3014052023553049855405205)
                    ·
                      refine ⟨141283688604049211972119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3014052023553049855405205 141283688604049211972119)
                      ·
                        rfl

theorem cell23_275149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_275149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275149 prefixEnd_275149 := by exact prefixLift 275149
  have htrace : WordTrace (prefixWord ++ tailWord_275149) baseStart_275149 baseEnd_275149 := by
    simpa [prefixWord, tailWord_275149, baseEnd_275149] using wordTrace_append hprefix tailTrace_275149
  have hstable : (prefixWord ++ tailWord_275149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275149).length < 2 ^ (prefixWord ++ tailWord_275149).sum := by decide
  have hdescent : baseEnd_275149 < baseStart_275149 := by decide
  rcases family_descends (prefixWord ++ tailWord_275149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275156 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_275156 : Nat := 118140960795 + 275156 * 2 ^ 59
def prefixEnd_275156 : Nat := 4983230072969 + 3 ^ 40 * 275156 * 2
def baseEnd_275156 : Nat := 141287282968630684584587

theorem tailTrace_275156 : CollatzResearch.WordTrace tailWord_275156 prefixEnd_275156 141287282968630684584587 := by
  unfold tailWord_275156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017881895582139874306661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6690509194109519832408881 5017881895582139874306661)
  ·
    refine ⟨940852855421651226432499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5017881895582139874306661 940852855421651226432499)
    ·
      refine ⟨1411279283132476839648749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940852855421651226432499 1411279283132476839648749)
      ·
        refine ⟨529229731174678814868281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1411279283132476839648749 529229731174678814868281)
        ·
          refine ⟨396922298381009111151211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529229731174678814868281 396922298381009111151211)
          ·
            refine ⟨595383447571513666726817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396922298381009111151211 595383447571513666726817)
            ·
              refine ⟨446537585678635250045113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595383447571513666726817 446537585678635250045113)
              ·
                refine ⟨334903189258976437533835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446537585678635250045113 334903189258976437533835)
                ·
                  refine ⟨502354783888464656300753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334903189258976437533835 502354783888464656300753)
                  ·
                    refine ⟨376766087916348492225565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502354783888464656300753 376766087916348492225565)
                    ·
                      refine ⟨141287282968630684584587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376766087916348492225565 141287282968630684584587)
                      ·
                        rfl

theorem cell23_275156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_275156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275156 prefixEnd_275156 := by exact prefixLift 275156
  have htrace : WordTrace (prefixWord ++ tailWord_275156) baseStart_275156 baseEnd_275156 := by
    simpa [prefixWord, tailWord_275156, baseEnd_275156] using wordTrace_append hprefix tailTrace_275156
  have hstable : (prefixWord ++ tailWord_275156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275156).length < 2 ^ (prefixWord ++ tailWord_275156).sum := by decide
  have hdescent : baseEnd_275156 < baseStart_275156 := by decide
  rcases family_descends (prefixWord ++ tailWord_275156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275205 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_275205 : Nat := 118140960795 + 275205 * 2 ^ 59
def prefixEnd_275205 : Nat := 4983230072969 + 3 ^ 40 * 275205 * 2
def baseEnd_275205 : Nat := 141312443520700992871861

theorem tailTrace_275205 : CollatzResearch.WordTrace tailWord_275205 prefixEnd_275205 141312443520700992871861 := by
  unfold tailWord_275205
  simp only [CollatzResearch.WordTrace]
  refine ⟨10037550967986761117147069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6691700645324507411431379 10037550967986761117147069)
  ·
    refine ⟨3764081612995035418930151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10037550967986761117147069 3764081612995035418930151)
    ·
      refine ⟨5646122419492553128395227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3764081612995035418930151 5646122419492553128395227)
      ·
        refine ⟨8469183629238829692592841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646122419492553128395227 8469183629238829692592841)
        ·
          refine ⟨6351887721929122269444631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8469183629238829692592841 6351887721929122269444631)
          ·
            refine ⟨9527831582893683404166947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351887721929122269444631 9527831582893683404166947)
            ·
              refine ⟨14291747374340525106250421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9527831582893683404166947 14291747374340525106250421)
              ·
                refine ⟨1339851316344424228710977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14291747374340525106250421 1339851316344424228710977)
                ·
                  refine ⟨1004888487258318171533233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339851316344424228710977 1004888487258318171533233)
                  ·
                    refine ⟨753666365443738628649925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1004888487258318171533233 753666365443738628649925)
                    ·
                      refine ⟨141312443520700992871861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 753666365443738628649925 141312443520700992871861)
                      ·
                        rfl

theorem cell23_275205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_275205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275205 prefixEnd_275205 := by exact prefixLift 275205
  have htrace : WordTrace (prefixWord ++ tailWord_275205) baseStart_275205 baseEnd_275205 := by
    simpa [prefixWord, tailWord_275205, baseEnd_275205] using wordTrace_append hprefix tailTrace_275205
  have hstable : (prefixWord ++ tailWord_275205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275205).length < 2 ^ (prefixWord ++ tailWord_275205).sum := by decide
  have hdescent : baseEnd_275205 < baseStart_275205 := by decide
  rcases family_descends (prefixWord ++ tailWord_275205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275225 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_275225 : Nat := 118140960795 + 275225 * 2 ^ 59
def prefixEnd_275225 : Nat := 4983230072969 + 3 ^ 40 * 275225 * 2
def baseEnd_275225 : Nat := 141322713133790914621769

theorem tailTrace_275225 : CollatzResearch.WordTrace tailWord_275225 prefixEnd_275225 141322713133790914621769 := by
  unfold tailWord_275225
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038280427914304532875129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6692186951942869688583419 10038280427914304532875129)
  ·
    refine ⟨7528710320935728399656347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10038280427914304532875129 7528710320935728399656347)
    ·
      refine ⟨11293065481403592599484521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7528710320935728399656347 11293065481403592599484521)
      ·
        refine ⟨8469799111052694449613391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11293065481403592599484521 8469799111052694449613391)
        ·
          refine ⟨12704698666579041674420087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8469799111052694449613391 12704698666579041674420087)
          ·
            refine ⟨19057047999868562511630131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12704698666579041674420087 19057047999868562511630131)
            ·
              refine ⟨28585571999802843767445197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19057047999868562511630131 28585571999802843767445197)
              ·
                refine ⟨10719589499926066412791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28585571999802843767445197 10719589499926066412791949)
                ·
                  refine ⟨4019846062472274904796981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10719589499926066412791949 4019846062472274904796981)
                  ·
                    refine ⟨376860568356775772324717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019846062472274904796981 376860568356775772324717)
                    ·
                      refine ⟨141322713133790914621769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 376860568356775772324717 141322713133790914621769)
                      ·
                        rfl

theorem cell23_275225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_275225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275225 prefixEnd_275225 := by exact prefixLift 275225
  have htrace : WordTrace (prefixWord ++ tailWord_275225) baseStart_275225 baseEnd_275225 := by
    simpa [prefixWord, tailWord_275225, baseEnd_275225] using wordTrace_append hprefix tailTrace_275225
  have hstable : (prefixWord ++ tailWord_275225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275225).length < 2 ^ (prefixWord ++ tailWord_275225).sum := by decide
  have hdescent : baseEnd_275225 < baseStart_275225 := by decide
  rcases family_descends (prefixWord ++ tailWord_275225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275255 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_275255 : Nat := 118140960795 + 275255 * 2 ^ 59
def prefixEnd_275255 : Nat := 4983230072969 + 3 ^ 40 * 275255 * 2
def baseEnd_275255 : Nat := 141338117553425797246631

theorem tailTrace_275255 : CollatzResearch.WordTrace tailWord_275255 prefixEnd_275255 141338117553425797246631 := by
  unfold tailWord_275255
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039374617805619656467219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6692916411870413104311479 10039374617805619656467219)
  ·
    refine ⟨15059061926708429484700829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10039374617805619656467219 15059061926708429484700829)
    ·
      refine ⟨5647148222515661056762811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15059061926708429484700829 5647148222515661056762811)
      ·
        refine ⟨8470722333773491585144217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647148222515661056762811 8470722333773491585144217)
        ·
          refine ⟨6353041750330118688858163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8470722333773491585144217 6353041750330118688858163)
          ·
            refine ⟨9529562625495178033287245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6353041750330118688858163 9529562625495178033287245)
            ·
              refine ⟨3573585984560691762482717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9529562625495178033287245 3573585984560691762482717)
              ·
                refine ⟨1340094744210259410931019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3573585984560691762482717 1340094744210259410931019)
                ·
                  refine ⟨2010142116315389116396529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340094744210259410931019 2010142116315389116396529)
                  ·
                    refine ⟨1507606587236541837297397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010142116315389116396529 1507606587236541837297397)
                    ·
                      refine ⟨141338117553425797246631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1507606587236541837297397 141338117553425797246631)
                      ·
                        rfl

theorem cell23_275255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_275255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275255 prefixEnd_275255 := by exact prefixLift 275255
  have htrace : WordTrace (prefixWord ++ tailWord_275255) baseStart_275255 baseEnd_275255 := by
    simpa [prefixWord, tailWord_275255, baseEnd_275255] using wordTrace_append hprefix tailTrace_275255
  have hstable : (prefixWord ++ tailWord_275255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275255).length < 2 ^ (prefixWord ++ tailWord_275255).sum := by decide
  have hdescent : baseEnd_275255 < baseStart_275255 := by decide
  rcases family_descends (prefixWord ++ tailWord_275255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275282 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_275282 : Nat := 118140960795 + 275282 * 2 ^ 59
def prefixEnd_275282 : Nat := 4983230072969 + 3 ^ 40 * 275282 * 2
def baseEnd_275282 : Nat := 141351981531097191609007

theorem tailTrace_275282 : CollatzResearch.WordTrace tailWord_275282 prefixEnd_275282 141351981531097191609007 := by
  unfold tailWord_275282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510089847176950816925025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6693572925805202178466733 2510089847176950816925025)
  ·
    refine ⟨1882567385382713112693769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2510089847176950816925025 1882567385382713112693769)
    ·
      refine ⟨1411925539037034834520327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1882567385382713112693769 1411925539037034834520327)
      ·
        refine ⟨2117888308555552251780491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411925539037034834520327 2117888308555552251780491)
        ·
          refine ⟨3176832462833328377670737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117888308555552251780491 3176832462833328377670737)
          ·
            refine ⟨2382624347124996283253053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176832462833328377670737 2382624347124996283253053)
            ·
              refine ⟨893484130171873606219895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382624347124996283253053 893484130171873606219895)
              ·
                refine ⟨1340226195257810409329843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893484130171873606219895 1340226195257810409329843)
                ·
                  refine ⟨2010339292886715613994765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340226195257810409329843 2010339292886715613994765)
                  ·
                    refine ⟨753877234832518355248037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010339292886715613994765 753877234832518355248037)
                    ·
                      refine ⟨141351981531097191609007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 753877234832518355248037 141351981531097191609007)
                      ·
                        rfl

theorem cell23_275282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_275282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275282 prefixEnd_275282 := by exact prefixLift 275282
  have htrace : WordTrace (prefixWord ++ tailWord_275282) baseStart_275282 baseEnd_275282 := by
    simpa [prefixWord, tailWord_275282, baseEnd_275282] using wordTrace_append hprefix tailTrace_275282
  have hstable : (prefixWord ++ tailWord_275282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275282).length < 2 ^ (prefixWord ++ tailWord_275282).sum := by decide
  have hdescent : baseEnd_275282 < baseStart_275282 := by decide
  rcases family_descends (prefixWord ++ tailWord_275282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275295 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_275295 : Nat := 118140960795 + 275295 * 2 ^ 59
def prefixEnd_275295 : Nat := 4983230072969 + 3 ^ 40 * 275295 * 2
def baseEnd_275295 : Nat := 141358656779605640746447

theorem tailTrace_275295 : CollatzResearch.WordTrace tailWord_275295 prefixEnd_275295 141358656779605640746447 := by
  unfold tailWord_275295
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040833537660706487923339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6693889025107137658615559 10040833537660706487923339)
  ·
    refine ⟨15061250306491059731885009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10040833537660706487923339 15061250306491059731885009)
    ·
      refine ⟨11295937729868294798913757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15061250306491059731885009 11295937729868294798913757)
      ·
        refine ⟨4235976648700610549592659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11295937729868294798913757 4235976648700610549592659)
        ·
          refine ⟨6353964973050915824388989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235976648700610549592659 6353964973050915824388989)
          ·
            refine ⟨2382736864894093434145871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6353964973050915824388989 2382736864894093434145871)
            ·
              refine ⟨3574105297341140151218807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382736864894093434145871 3574105297341140151218807)
              ·
                refine ⟨5361157946011710226828211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574105297341140151218807 5361157946011710226828211)
                ·
                  refine ⟨8041736919017565340242317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5361157946011710226828211 8041736919017565340242317)
                  ·
                    refine ⟨3015651344631587002590869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8041736919017565340242317 3015651344631587002590869)
                    ·
                      refine ⟨141358656779605640746447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3015651344631587002590869 141358656779605640746447)
                      ·
                        rfl

theorem cell23_275295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_275295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275295 prefixEnd_275295 := by exact prefixLift 275295
  have htrace : WordTrace (prefixWord ++ tailWord_275295) baseStart_275295 baseEnd_275295 := by
    simpa [prefixWord, tailWord_275295, baseEnd_275295] using wordTrace_append hprefix tailTrace_275295
  have hstable : (prefixWord ++ tailWord_275295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275295).length < 2 ^ (prefixWord ++ tailWord_275295).sum := by decide
  have hdescent : baseEnd_275295 < baseStart_275295 := by decide
  rcases family_descends (prefixWord ++ tailWord_275295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275299 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 2, 4, 2]
def baseStart_275299 : Nat := 118140960795 + 275299 * 2 ^ 59
def prefixEnd_275299 : Nat := 4983230072969 + 3 ^ 40 * 275299 * 2
def baseEnd_275299 : Nat := 141360710702223625096429

theorem tailTrace_275299 : CollatzResearch.WordTrace tailWord_275299 prefixEnd_275299 141360710702223625096429 := by
  unfold tailWord_275299
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040979429646215171068951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6693986286430810114045967 10040979429646215171068951)
  ·
    refine ⟨15061469144469322756603427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10040979429646215171068951 15061469144469322756603427)
    ·
      refine ⟨22592203716703984134905141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15061469144469322756603427 22592203716703984134905141)
      ·
        refine ⟨2118019098440998512647357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22592203716703984134905141 2118019098440998512647357)
        ·
          refine ⟨794257161915374442242759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118019098440998512647357 794257161915374442242759)
          ·
            refine ⟨1191385742873061663364139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794257161915374442242759 1191385742873061663364139)
            ·
              refine ⟨1787078614309592495046209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191385742873061663364139 1787078614309592495046209)
              ·
                refine ⟨1340308960732194371284657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787078614309592495046209 1340308960732194371284657)
                ·
                  refine ⟨1005231720549145778463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340308960732194371284657 1005231720549145778463493)
                  ·
                    refine ⟨188480947602964833461905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005231720549145778463493 188480947602964833461905)
                    ·
                      refine ⟨141360710702223625096429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188480947602964833461905 141360710702223625096429)
                      ·
                        rfl

theorem cell23_275299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_275299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275299 prefixEnd_275299 := by exact prefixLift 275299
  have htrace : WordTrace (prefixWord ++ tailWord_275299) baseStart_275299 baseEnd_275299 := by
    simpa [prefixWord, tailWord_275299, baseEnd_275299] using wordTrace_append hprefix tailTrace_275299
  have hstable : (prefixWord ++ tailWord_275299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275299).length < 2 ^ (prefixWord ++ tailWord_275299).sum := by decide
  have hdescent : baseEnd_275299 < baseStart_275299 := by decide
  rcases family_descends (prefixWord ++ tailWord_275299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275332 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_275332 : Nat := 118140960795 + 275332 * 2 ^ 59
def prefixEnd_275332 : Nat := 4983230072969 + 3 ^ 40 * 275332 * 2
def baseEnd_275332 : Nat := 141377655563821995983777

theorem tailTrace_275332 : CollatzResearch.WordTrace tailWord_275332 prefixEnd_275332 141377655563821995983777 := by
  unfold tailWord_275332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021091519263330903510125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6694788692351107871346833 5021091519263330903510125)
  ·
    refine ⟨1882909319723749088816297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5021091519263330903510125 1882909319723749088816297)
    ·
      refine ⟨1412181989792811816612223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1882909319723749088816297 1412181989792811816612223)
      ·
        refine ⟨2118272984689217724918335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412181989792811816612223 2118272984689217724918335)
        ·
          refine ⟨3177409477033826587377503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118272984689217724918335 3177409477033826587377503)
          ·
            refine ⟨4766114215550739881066255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177409477033826587377503 4766114215550739881066255)
            ·
              refine ⟨7149171323326109821599383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4766114215550739881066255 7149171323326109821599383)
              ·
                refine ⟨10723756984989164732399075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7149171323326109821599383 10723756984989164732399075)
                ·
                  refine ⟨16085635477483747098598613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10723756984989164732399075 16085635477483747098598613)
                  ·
                    refine ⟨377007081503525322623405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16085635477483747098598613 377007081503525322623405)
                    ·
                      refine ⟨141377655563821995983777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377007081503525322623405 141377655563821995983777)
                      ·
                        rfl

theorem cell23_275332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_275332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275332 prefixEnd_275332 := by exact prefixLift 275332
  have htrace : WordTrace (prefixWord ++ tailWord_275332) baseStart_275332 baseEnd_275332 := by
    simpa [prefixWord, tailWord_275332, baseEnd_275332] using wordTrace_append hprefix tailTrace_275332
  have hstable : (prefixWord ++ tailWord_275332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275332).length < 2 ^ (prefixWord ++ tailWord_275332).sum := by decide
  have hdescent : baseEnd_275332 < baseStart_275332 := by decide
  rcases family_descends (prefixWord ++ tailWord_275332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275372 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_275372 : Nat := 118140960795 + 275372 * 2 ^ 59
def prefixEnd_275372 : Nat := 4983230072969 + 3 ^ 40 * 275372 * 2
def baseEnd_275372 : Nat := 141398194790001839483593

theorem tailTrace_275372 : CollatzResearch.WordTrace tailWord_275372 prefixEnd_275372 141398194790001839483593 := by
  unfold tailWord_275372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021820979190874319238185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6695761305587832425650913 5021820979190874319238185)
  ·
    refine ⟨3766365734393155739428639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5021820979190874319238185 3766365734393155739428639)
    ·
      refine ⟨5649548601589733609142959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766365734393155739428639 5649548601589733609142959)
      ·
        refine ⟨8474322902384600413714439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649548601589733609142959 8474322902384600413714439)
        ·
          refine ⟨12711484353576900620571659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8474322902384600413714439 12711484353576900620571659)
          ·
            refine ⟨19067226530365350930857489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12711484353576900620571659 19067226530365350930857489)
            ·
              refine ⟨14300419897774013198143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19067226530365350930857489 14300419897774013198143117)
              ·
                refine ⟨5362657461665254949303669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14300419897774013198143117 5362657461665254949303669)
                ·
                  refine ⟨502749137031117651497219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5362657461665254949303669 502749137031117651497219)
                  ·
                    refine ⟨754123705546676477245829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502749137031117651497219 754123705546676477245829)
                    ·
                      refine ⟨141398194790001839483593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 754123705546676477245829 141398194790001839483593)
                      ·
                        rfl

theorem cell23_275372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_275372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275372 prefixEnd_275372 := by exact prefixLift 275372
  have htrace : WordTrace (prefixWord ++ tailWord_275372) baseStart_275372 baseEnd_275372 := by
    simpa [prefixWord, tailWord_275372, baseEnd_275372] using wordTrace_append hprefix tailTrace_275372
  have hstable : (prefixWord ++ tailWord_275372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275372).length < 2 ^ (prefixWord ++ tailWord_275372).sum := by decide
  have hdescent : baseEnd_275372 < baseStart_275372 := by decide
  rcases family_descends (prefixWord ++ tailWord_275372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275412 : List Nat := [2, 4, 1, 2, 1, 13]
def baseStart_275412 : Nat := 118140960795 + 275412 * 2 ^ 59
def prefixEnd_275412 : Nat := 4983230072969 + 3 ^ 40 * 275412 * 2
def baseEnd_275412 : Nat := 581970098832023386763

theorem tailTrace_275412 : CollatzResearch.WordTrace tailWord_275412 prefixEnd_275412 581970098832023386763 := by
  unfold tailWord_275412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022550439118417734966245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6696733918824556979954993 5022550439118417734966245)
  ·
    refine ⟨941728207334703325306171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5022550439118417734966245 941728207334703325306171)
    ·
      refine ⟨1412592311002054987959257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941728207334703325306171 1412592311002054987959257)
      ·
        refine ⟨1059444233251541240969443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1412592311002054987959257 1059444233251541240969443)
        ·
          refine ⟨1589166349877311861454165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059444233251541240969443 1589166349877311861454165)
          ·
            refine ⟨581970098832023386763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 1589166349877311861454165 581970098832023386763)
            ·
              rfl

theorem cell23_275412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 13].length) (baseStart_275412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275412 prefixEnd_275412 := by exact prefixLift 275412
  have htrace : WordTrace (prefixWord ++ tailWord_275412) baseStart_275412 baseEnd_275412 := by
    simpa [prefixWord, tailWord_275412, baseEnd_275412] using wordTrace_append hprefix tailTrace_275412
  have hstable : (prefixWord ++ tailWord_275412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275412).length < 2 ^ (prefixWord ++ tailWord_275412).sum := by decide
  have hdescent : baseEnd_275412 < baseStart_275412 := by decide
  rcases family_descends (prefixWord ++ tailWord_275412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275416 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_275416 : Nat := 118140960795 + 275416 * 2 ^ 59
def prefixEnd_275416 : Nat := 4983230072969 + 3 ^ 40 * 275416 * 2
def baseEnd_275416 : Nat := 47140262646266555777797

theorem tailTrace_275416 : CollatzResearch.WordTrace tailWord_275416 prefixEnd_275416 47140262646266555777797 := by
  unfold tailWord_275416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022623385111172076539051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6696831180148229435385401 5022623385111172076539051)
  ·
    refine ⟨7533935077666758114808577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022623385111172076539051 7533935077666758114808577)
    ·
      refine ⟨5650451308250068586106433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7533935077666758114808577 5650451308250068586106433)
      ·
        refine ⟨4237838481187551439579825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5650451308250068586106433 4237838481187551439579825)
        ·
          refine ⟨3178378860890663579684869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4237838481187551439579825 3178378860890663579684869)
          ·
            refine ⟨595946036416999421190913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3178378860890663579684869 595946036416999421190913)
            ·
              refine ⟨446959527312749565893185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595946036416999421190913 446959527312749565893185)
              ·
                refine ⟨335219645484562174419889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446959527312749565893185 335219645484562174419889)
                ·
                  refine ⟨251414734113421630814917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335219645484562174419889 251414734113421630814917)
                  ·
                    refine ⟨47140262646266555777797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251414734113421630814917 47140262646266555777797)
                    ·
                      rfl

theorem cell23_275416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_275416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275416 prefixEnd_275416 := by exact prefixLift 275416
  have htrace : WordTrace (prefixWord ++ tailWord_275416) baseStart_275416 baseEnd_275416 := by
    simpa [prefixWord, tailWord_275416, baseEnd_275416] using wordTrace_append hprefix tailTrace_275416
  have hstable : (prefixWord ++ tailWord_275416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275416).length < 2 ^ (prefixWord ++ tailWord_275416).sum := by decide
  have hdescent : baseEnd_275416 < baseStart_275416 := by decide
  rcases family_descends (prefixWord ++ tailWord_275416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275432 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_275432 : Nat := 118140960795 + 275432 * 2 ^ 59
def prefixEnd_275432 : Nat := 4983230072969 + 3 ^ 40 * 275432 * 2
def baseEnd_275432 : Nat := 141429003629271604733317

theorem tailTrace_275432 : CollatzResearch.WordTrace tailWord_275432 prefixEnd_275432 141429003629271604733317 := by
  unfold tailWord_275432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022915169082189442830275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6697220225442919257107033 5022915169082189442830275)
  ·
    refine ⟨7534372753623284164245413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022915169082189442830275 7534372753623284164245413)
    ·
      refine ⟨1412694891304365780796015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7534372753623284164245413 1412694891304365780796015)
      ·
        refine ⟨2119042336956548671194023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412694891304365780796015 2119042336956548671194023)
        ·
          refine ⟨3178563505434823006791035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119042336956548671194023 3178563505434823006791035)
          ·
            refine ⟨4767845258152234510186553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178563505434823006791035 4767845258152234510186553)
            ·
              refine ⟨3575883943614175882639915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4767845258152234510186553 3575883943614175882639915)
              ·
                refine ⟨5363825915421263823959873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575883943614175882639915 5363825915421263823959873)
                ·
                  refine ⟨4022869436565947867969905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363825915421263823959873 4022869436565947867969905)
                  ·
                    refine ⟨3017152077424460900977429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022869436565947867969905 3017152077424460900977429)
                    ·
                      refine ⟨141429003629271604733317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3017152077424460900977429 141429003629271604733317)
                      ·
                        rfl

theorem cell23_275432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_275432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275432 prefixEnd_275432 := by exact prefixLift 275432
  have htrace : WordTrace (prefixWord ++ tailWord_275432) baseStart_275432 baseEnd_275432 := by
    simpa [prefixWord, tailWord_275432, baseEnd_275432] using wordTrace_append hprefix tailTrace_275432
  have hstable : (prefixWord ++ tailWord_275432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275432).length < 2 ^ (prefixWord ++ tailWord_275432).sum := by decide
  have hdescent : baseEnd_275432 < baseStart_275432 := by decide
  rcases family_descends (prefixWord ++ tailWord_275432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275439 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_275439 : Nat := 118140960795 + 275439 * 2 ^ 59
def prefixEnd_275439 : Nat := 4983230072969 + 3 ^ 40 * 275439 * 2
def baseEnd_275439 : Nat := 141432597993853077345785

theorem tailTrace_275439 : CollatzResearch.WordTrace tailWord_275439 prefixEnd_275439 141432597993853077345785 := by
  unfold tailWord_275439
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046085649139019081165371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6697390432759346054110247 10046085649139019081165371)
  ·
    refine ⟨15069128473708528621748057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10046085649139019081165371 15069128473708528621748057)
    ·
      refine ⟨11301846355281396466311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15069128473708528621748057 11301846355281396466311043)
      ·
        refine ⟨16952769532922094699466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11301846355281396466311043 16952769532922094699466565)
        ·
          refine ⟨3178644287422892756149981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16952769532922094699466565 3178644287422892756149981)
          ·
            refine ⟨1191991607783584783556243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3178644287422892756149981 1191991607783584783556243)
            ·
              refine ⟨1787987411675377175334365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191991607783584783556243 1787987411675377175334365)
              ·
                refine ⟨670495279378266440750387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1787987411675377175334365 670495279378266440750387)
                ·
                  refine ⟨1005742919067399661125581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670495279378266440750387 1005742919067399661125581)
                  ·
                    refine ⟨377153594650274872922093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005742919067399661125581 377153594650274872922093)
                    ·
                      refine ⟨141432597993853077345785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377153594650274872922093 141432597993853077345785)
                      ·
                        rfl

theorem cell23_275439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_275439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275439 prefixEnd_275439 := by exact prefixLift 275439
  have htrace : WordTrace (prefixWord ++ tailWord_275439) baseStart_275439 baseEnd_275439 := by
    simpa [prefixWord, tailWord_275439, baseEnd_275439] using wordTrace_append hprefix tailTrace_275439
  have hstable : (prefixWord ++ tailWord_275439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275439).length < 2 ^ (prefixWord ++ tailWord_275439).sum := by decide
  have hdescent : baseEnd_275439 < baseStart_275439 := by decide
  rcases family_descends (prefixWord ++ tailWord_275439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275446 : List Nat := [5, 1, 1, 1, 3, 2, 3, 7]
def baseStart_275446 : Nat := 118140960795 + 275446 * 2 ^ 59
def prefixEnd_275446 : Nat := 4983230072969 + 3 ^ 40 * 275446 * 2
def baseEnd_275446 : Nat := 5238377494756835183639

theorem tailTrace_275446 : CollatzResearch.WordTrace tailWord_275446 prefixEnd_275446 5238377494756835183639 := by
  unfold tailWord_275446
  simp only [CollatzResearch.WordTrace]
  refine ⟨627896310007103704791887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6697560640075772851113461 627896310007103704791887)
  ·
    refine ⟨941844465010655557187831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627896310007103704791887 941844465010655557187831)
    ·
      refine ⟨1412766697515983335781747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941844465010655557187831 1412766697515983335781747)
      ·
        refine ⟨2119150046273975003672621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412766697515983335781747 2119150046273975003672621)
        ·
          refine ⟨794681267352740626377233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119150046273975003672621 794681267352740626377233)
          ·
            refine ⟨596010950514555469782925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794681267352740626377233 596010950514555469782925)
            ·
              refine ⟨223504106442958301168597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 596010950514555469782925 223504106442958301168597)
              ·
                refine ⟨5238377494756835183639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 223504106442958301168597 5238377494756835183639)
                ·
                  rfl

theorem cell23_275446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_275446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275446 prefixEnd_275446 := by exact prefixLift 275446
  have htrace : WordTrace (prefixWord ++ tailWord_275446) baseStart_275446 baseEnd_275446 := by
    simpa [prefixWord, tailWord_275446, baseEnd_275446] using wordTrace_append hprefix tailTrace_275446
  have hstable : (prefixWord ++ tailWord_275446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275446).length < 2 ^ (prefixWord ++ tailWord_275446).sum := by decide
  have hdescent : baseEnd_275446 < baseStart_275446 := by decide
  rcases family_descends (prefixWord ++ tailWord_275446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275474 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_275474 : Nat := 118140960795 + 275474 * 2 ^ 59
def prefixEnd_275474 : Nat := 4983230072969 + 3 ^ 40 * 275474 * 2
def baseEnd_275474 : Nat := 141450569816760440408125

theorem tailTrace_275474 : CollatzResearch.WordTrace tailWord_275474 prefixEnd_275474 141450569816760440408125 := by
  unfold tailWord_275474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511840551003055014672369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6698241469341480039126317 2511840551003055014672369)
  ·
    refine ⟨1883880413252291261004277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2511840551003055014672369 1883880413252291261004277)
    ·
      refine ⟨176613788742402305719151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1883880413252291261004277 176613788742402305719151)
      ·
        refine ⟨264920683113603458578727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176613788742402305719151 264920683113603458578727)
        ·
          refine ⟨397381024670405187868091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264920683113603458578727 397381024670405187868091)
          ·
            refine ⟨596071537005607781802137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397381024670405187868091 596071537005607781802137)
            ·
              refine ⟨447053652754205836351603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596071537005607781802137 447053652754205836351603)
              ·
                refine ⟨670580479131308754527405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447053652754205836351603 670580479131308754527405)
                ·
                  refine ⟨251467679674240782947777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670580479131308754527405 251467679674240782947777)
                  ·
                    refine ⟨188600759755680587210833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251467679674240782947777 188600759755680587210833)
                    ·
                      refine ⟨141450569816760440408125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188600759755680587210833 141450569816760440408125)
                      ·
                        rfl

theorem cell23_275474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_275474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275474 prefixEnd_275474 := by exact prefixLift 275474
  have htrace : WordTrace (prefixWord ++ tailWord_275474) baseStart_275474 baseEnd_275474 := by
    simpa [prefixWord, tailWord_275474, baseEnd_275474] using wordTrace_append hprefix tailTrace_275474
  have hstable : (prefixWord ++ tailWord_275474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275474).length < 2 ^ (prefixWord ++ tailWord_275474).sum := by decide
  have hdescent : baseEnd_275474 < baseStart_275474 := by decide
  rcases family_descends (prefixWord ++ tailWord_275474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275489 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_275489 : Nat := 118140960795 + 275489 * 2 ^ 59
def prefixEnd_275489 : Nat := 4983230072969 + 3 ^ 40 * 275489 * 2
def baseEnd_275489 : Nat := 47152757342192627240185

theorem tailTrace_275489 : CollatzResearch.WordTrace tailWord_275489 prefixEnd_275489 47152757342192627240185 := by
  unfold tailWord_275489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047909298957877620485521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6698606199305251746990347 10047909298957877620485521)
  ·
    refine ⟨7535931974218408215364141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10047909298957877620485521 7535931974218408215364141)
    ·
      refine ⟨2825974490331903080761553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7535931974218408215364141 2825974490331903080761553)
      ·
        refine ⟨2119480867748927310571165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825974490331903080761553 2119480867748927310571165)
        ·
          refine ⟨794805325405847741464187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119480867748927310571165 794805325405847741464187)
          ·
            refine ⟨1192207988108771612196281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794805325405847741464187 1192207988108771612196281)
            ·
              refine ⟨894155991081578709147211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192207988108771612196281 894155991081578709147211)
              ·
                refine ⟨1341233986622368063720817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894155991081578709147211 1341233986622368063720817)
                ·
                  refine ⟨1005925489966776047790613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1341233986622368063720817 1005925489966776047790613)
                  ·
                    refine ⟨47152757342192627240185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1005925489966776047790613 47152757342192627240185)
                    ·
                      rfl

theorem cell23_275489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_275489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275489 prefixEnd_275489 := by exact prefixLift 275489
  have htrace : WordTrace (prefixWord ++ tailWord_275489) baseStart_275489 baseEnd_275489 := by
    simpa [prefixWord, tailWord_275489, baseEnd_275489] using wordTrace_append hprefix tailTrace_275489
  have hstable : (prefixWord ++ tailWord_275489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275489).length < 2 ^ (prefixWord ++ tailWord_275489).sum := by decide
  have hdescent : baseEnd_275489 < baseStart_275489 := by decide
  rcases family_descends (prefixWord ++ tailWord_275489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275490 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_275490 : Nat := 118140960795 + 275490 * 2 ^ 59
def prefixEnd_275490 : Nat := 4983230072969 + 3 ^ 40 * 275490 * 2
def baseEnd_275490 : Nat := 141458785507232377808051

theorem tailTrace_275490 : CollatzResearch.WordTrace tailWord_275490 prefixEnd_275490 141458785507232377808051 := by
  unfold tailWord_275490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511986442988563697817981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6698630514636169860847949 2511986442988563697817981)
  ·
    refine ⟨941994916120711386681743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2511986442988563697817981 941994916120711386681743)
    ·
      refine ⟨1412992374181067080022615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941994916120711386681743 1412992374181067080022615)
      ·
        refine ⟨2119488561271600620033923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412992374181067080022615 2119488561271600620033923)
        ·
          refine ⟨3179232841907400930050885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119488561271600620033923 3179232841907400930050885)
          ·
            refine ⟨596106157857637674384541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3179232841907400930050885 596106157857637674384541)
            ·
              refine ⟨223539809196614127894203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 596106157857637674384541 223539809196614127894203)
              ·
                refine ⟨335309713794921191841305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223539809196614127894203 335309713794921191841305)
                ·
                  refine ⟨251482285346190893880979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335309713794921191841305 251482285346190893880979)
                  ·
                    refine ⟨377223428019286340821469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251482285346190893880979 377223428019286340821469)
                    ·
                      refine ⟨141458785507232377808051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377223428019286340821469 141458785507232377808051)
                      ·
                        rfl

theorem cell23_275490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_275490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275490 prefixEnd_275490 := by exact prefixLift 275490
  have htrace : WordTrace (prefixWord ++ tailWord_275490) baseStart_275490 baseEnd_275490 := by
    simpa [prefixWord, tailWord_275490, baseEnd_275490] using wordTrace_append hprefix tailTrace_275490
  have hstable : (prefixWord ++ tailWord_275490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275490).length < 2 ^ (prefixWord ++ tailWord_275490).sum := by decide
  have hdescent : baseEnd_275490 < baseStart_275490 := by decide
  rcases family_descends (prefixWord ++ tailWord_275490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275513 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 4, 2, 2]
def baseStart_275513 : Nat := 118140960795 + 275513 * 2 ^ 59
def prefixEnd_275513 : Nat := 4983230072969 + 3 ^ 40 * 275513 * 2
def baseEnd_275513 : Nat := 141470595562285787820445

theorem tailTrace_275513 : CollatzResearch.WordTrace tailWord_275513 prefixEnd_275513 141470595562285787820445 := by
  unfold tailWord_275513
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048784650870929719359193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6699189767247286479572795 10048784650870929719359193)
  ·
    refine ⟨7536588488153197289519395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10048784650870929719359193 7536588488153197289519395)
    ·
      refine ⟨11304882732229795934279093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7536588488153197289519395 11304882732229795934279093)
      ·
        refine ⟨1059832756146543368838665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11304882732229795934279093 1059832756146543368838665)
        ·
          refine ⟨794874567109907526628999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1059832756146543368838665 794874567109907526628999)
          ·
            refine ⟨1192311850664861289943499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794874567109907526628999 1192311850664861289943499)
            ·
              refine ⟨1788467775997291934915249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192311850664861289943499 1788467775997291934915249)
              ·
                refine ⟨1341350831997968951186437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788467775997291934915249 1341350831997968951186437)
                ·
                  refine ⟨251503280999619178347457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341350831997968951186437 251503280999619178347457)
                  ·
                    refine ⟨188627460749714383760593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251503280999619178347457 188627460749714383760593)
                    ·
                      refine ⟨141470595562285787820445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188627460749714383760593 141470595562285787820445)
                      ·
                        rfl

theorem cell23_275513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_275513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275513 prefixEnd_275513 := by exact prefixLift 275513
  have htrace : WordTrace (prefixWord ++ tailWord_275513) baseStart_275513 baseEnd_275513 := by
    simpa [prefixWord, tailWord_275513, baseEnd_275513] using wordTrace_append hprefix tailTrace_275513
  have hstable : (prefixWord ++ tailWord_275513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275513).length < 2 ^ (prefixWord ++ tailWord_275513).sum := by decide
  have hdescent : baseEnd_275513 < baseStart_275513 := by decide
  rcases family_descends (prefixWord ++ tailWord_275513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275529 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_275529 : Nat := 118140960795 + 275529 * 2 ^ 59
def prefixEnd_275529 : Nat := 4983230072969 + 3 ^ 40 * 275529 * 2
def baseEnd_275529 : Nat := 141478811252757725220371

theorem tailTrace_275529 : CollatzResearch.WordTrace tailWord_275529 prefixEnd_275529 141478811252757725220371 := by
  unfold tailWord_275529
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049368218812964451941641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6699578812541976301294427 10049368218812964451941641)
  ·
    refine ⟨7537026164109723338956231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10049368218812964451941641 7537026164109723338956231)
    ·
      refine ⟨11305539246164585008434347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7537026164109723338956231 11305539246164585008434347)
      ·
        refine ⟨16958308869246877512651521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11305539246164585008434347 16958308869246877512651521)
        ·
          refine ⟨12718731651935158134488641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16958308869246877512651521 12718731651935158134488641)
          ·
            refine ⟨9539048738951368600866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12718731651935158134488641 9539048738951368600866481)
            ·
              refine ⟨7154286554213526450649861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9539048738951368600866481 7154286554213526450649861)
              ·
                refine ⟨1341428728915036209496849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7154286554213526450649861 1341428728915036209496849)
                ·
                  refine ⟨1006071546686277157122637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1341428728915036209496849 1006071546686277157122637)
                  ·
                    refine ⟨377276830007353933920989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006071546686277157122637 377276830007353933920989)
                    ·
                      refine ⟨141478811252757725220371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377276830007353933920989 141478811252757725220371)
                      ·
                        rfl

theorem cell23_275529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_275529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275529 prefixEnd_275529 := by exact prefixLift 275529
  have htrace : WordTrace (prefixWord ++ tailWord_275529) baseStart_275529 baseEnd_275529 := by
    simpa [prefixWord, tailWord_275529, baseEnd_275529] using wordTrace_append hprefix tailTrace_275529
  have hstable : (prefixWord ++ tailWord_275529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275529).length < 2 ^ (prefixWord ++ tailWord_275529).sum := by decide
  have hdescent : baseEnd_275529 < baseStart_275529 := by decide
  rcases family_descends (prefixWord ++ tailWord_275529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275566 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_275566 : Nat := 118140960795 + 275566 * 2 ^ 59
def prefixEnd_275566 : Nat := 4983230072969 + 3 ^ 40 * 275566 * 2
def baseEnd_275566 : Nat := 47165936678991360152567

theorem tailTrace_275566 : CollatzResearch.WordTrace tailWord_275566 prefixEnd_275566 47165936678991360152567 := by
  unfold tailWord_275566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256339714959864971379819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6700478479785946514025701 1256339714959864971379819)
  ·
    refine ⟨1884509572439797457069729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256339714959864971379819 1884509572439797457069729)
    ·
      refine ⟨1413382179329848092802297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884509572439797457069729 1413382179329848092802297)
      ·
        refine ⟨1060036634497386069601723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1413382179329848092802297 1060036634497386069601723)
        ·
          refine ⟨1590054951746079104402585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060036634497386069601723 1590054951746079104402585)
          ·
            refine ⟨1192541213809559328301939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590054951746079104402585 1192541213809559328301939)
            ·
              refine ⟨1788811820714338992452909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192541213809559328301939 1788811820714338992452909)
              ·
                refine ⟨670804432767877122169841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1788811820714338992452909 670804432767877122169841)
                ·
                  refine ⟨503103324575907841627381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 670804432767877122169841 503103324575907841627381)
                  ·
                    refine ⟨47165936678991360152567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 503103324575907841627381 47165936678991360152567)
                    ·
                      rfl

theorem cell23_275566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_275566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275566 prefixEnd_275566 := by exact prefixLift 275566
  have htrace : WordTrace (prefixWord ++ tailWord_275566) baseStart_275566 baseEnd_275566 := by
    simpa [prefixWord, tailWord_275566, baseEnd_275566] using wordTrace_append hprefix tailTrace_275566
  have hstable : (prefixWord ++ tailWord_275566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275566).length < 2 ^ (prefixWord ++ tailWord_275566).sum := by decide
  have hdescent : baseEnd_275566 < baseStart_275566 := by decide
  rcases family_descends (prefixWord ++ tailWord_275566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275623 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_275623 : Nat := 118140960795 + 275623 * 2 ^ 59
def prefixEnd_275623 : Nat := 4983230072969 + 3 ^ 40 * 275623 * 2
def baseEnd_275623 : Nat := 141527078434280357444939

theorem tailTrace_275623 : CollatzResearch.WordTrace tailWord_275623 prefixEnd_275623 141527078434280357444939 := by
  unfold tailWord_275623
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052796680472418505863523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6701864453648279003909015 10052796680472418505863523)
  ·
    refine ⟨15079195020708627758795285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10052796680472418505863523 15079195020708627758795285)
    ·
      refine ⟨706837266595716926193529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15079195020708627758795285 706837266595716926193529)
      ·
        refine ⟨530127949946787694645147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706837266595716926193529 530127949946787694645147)
        ·
          refine ⟨795191924920181541967721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530127949946787694645147 795191924920181541967721)
          ·
            refine ⟨596393943690136156475791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795191924920181541967721 596393943690136156475791)
            ·
              refine ⟨894590915535204234713687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596393943690136156475791 894590915535204234713687)
              ·
                refine ⟨1341886373302806352070531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894590915535204234713687 1341886373302806352070531)
                ·
                  refine ⟨2012829559954209528105797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341886373302806352070531 2012829559954209528105797)
                  ·
                    refine ⟨377405542491414286519837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012829559954209528105797 377405542491414286519837)
                    ·
                      refine ⟨141527078434280357444939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377405542491414286519837 141527078434280357444939)
                      ·
                        rfl

theorem cell23_275623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_275623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275623 prefixEnd_275623 := by exact prefixLift 275623
  have htrace : WordTrace (prefixWord ++ tailWord_275623) baseStart_275623 baseEnd_275623 := by
    simpa [prefixWord, tailWord_275623, baseEnd_275623] using wordTrace_append hprefix tailTrace_275623
  have hstable : (prefixWord ++ tailWord_275623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275623).length < 2 ^ (prefixWord ++ tailWord_275623).sum := by decide
  have hdescent : baseEnd_275623 < baseStart_275623 := by decide
  rcases family_descends (prefixWord ++ tailWord_275623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275646 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_275646 : Nat := 118140960795 + 275646 * 2 ^ 59
def prefixEnd_275646 : Nat := 4983230072969 + 3 ^ 40 * 275646 * 2
def baseEnd_275646 : Nat := 141538888489333767457333

theorem tailTrace_275646 : CollatzResearch.WordTrace tailWord_275646 prefixEnd_275646 141538888489333767457333 := by
  unfold tailWord_275646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256704444923636679243849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6702423706259395622633861 1256704444923636679243849)
  ·
    refine ⟨942528333692727509432887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1256704444923636679243849 942528333692727509432887)
    ·
      refine ⟨1413792500539091264149331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942528333692727509432887 1413792500539091264149331)
      ·
        refine ⟨2120688750808636896223997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413792500539091264149331 2120688750808636896223997)
        ·
          refine ⟨795258281553238836083999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2120688750808636896223997 795258281553238836083999)
          ·
            refine ⟨1192887422329858254125999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795258281553238836083999 1192887422329858254125999)
            ·
              refine ⟨1789331133494787381188999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192887422329858254125999 1789331133494787381188999)
              ·
                refine ⟨2683996700242181071783499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1789331133494787381188999 2683996700242181071783499)
                ·
                  refine ⟨4025995050363271607675249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683996700242181071783499 4025995050363271607675249)
                  ·
                    refine ⟨3019496287772453705756437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025995050363271607675249 3019496287772453705756437)
                    ·
                      refine ⟨141538888489333767457333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3019496287772453705756437 141538888489333767457333)
                      ·
                        rfl

theorem cell23_275646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_275646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275646 prefixEnd_275646 := by exact prefixLift 275646
  have htrace : WordTrace (prefixWord ++ tailWord_275646) baseStart_275646 baseEnd_275646 := by
    simpa [prefixWord, tailWord_275646, baseEnd_275646] using wordTrace_append hprefix tailTrace_275646
  have hstable : (prefixWord ++ tailWord_275646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275646).length < 2 ^ (prefixWord ++ tailWord_275646).sum := by decide
  have hdescent : baseEnd_275646 < baseStart_275646 := by decide
  rcases family_descends (prefixWord ++ tailWord_275646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275659 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_275659 : Nat := 118140960795 + 275659 * 2 ^ 59
def prefixEnd_275659 : Nat := 4983230072969 + 3 ^ 40 * 275659 * 2
def baseEnd_275659 : Nat := 141545563737842216594773

theorem tailTrace_275659 : CollatzResearch.WordTrace tailWord_275659 prefixEnd_275659 141545563737842216594773 := by
  unfold tailWord_275659
  simp only [CollatzResearch.WordTrace]
  refine ⟨10054109708341996654174031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6702739805561331102782687 10054109708341996654174031)
  ·
    refine ⟨15081164562512994981261047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10054109708341996654174031 15081164562512994981261047)
    ·
      refine ⟨22621746843769492471891571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15081164562512994981261047 22621746843769492471891571)
      ·
        refine ⟨33932620265654238707837357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22621746843769492471891571 33932620265654238707837357)
        ·
          refine ⟨12724732599620339515439009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33932620265654238707837357 12724732599620339515439009)
          ·
            refine ⟨9543549449715254636579257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12724732599620339515439009 9543549449715254636579257)
            ·
              refine ⟨7157662087286440977434443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9543549449715254636579257 7157662087286440977434443)
              ·
                refine ⟨10736493130929661466151665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157662087286440977434443 10736493130929661466151665)
                ·
                  refine ⟨8052369848197246099613749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10736493130929661466151665 8052369848197246099613749)
                  ·
                    refine ⟨754909673268491821838789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8052369848197246099613749 754909673268491821838789)
                    ·
                      refine ⟨141545563737842216594773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 754909673268491821838789 141545563737842216594773)
                      ·
                        rfl

theorem cell23_275659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_275659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275659 prefixEnd_275659 := by exact prefixLift 275659
  have htrace : WordTrace (prefixWord ++ tailWord_275659) baseStart_275659 baseEnd_275659 := by
    simpa [prefixWord, tailWord_275659, baseEnd_275659] using wordTrace_append hprefix tailTrace_275659
  have hstable : (prefixWord ++ tailWord_275659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275659).length < 2 ^ (prefixWord ++ tailWord_275659).sum := by decide
  have hdescent : baseEnd_275659 < baseStart_275659 := by decide
  rcases family_descends (prefixWord ++ tailWord_275659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275689 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_275689 : Nat := 118140960795 + 275689 * 2 ^ 59
def prefixEnd_275689 : Nat := 4983230072969 + 3 ^ 40 * 275689 * 2
def baseEnd_275689 : Nat := 141560968157477099219635

theorem tailTrace_275689 : CollatzResearch.WordTrace tailWord_275689 prefixEnd_275689 141560968157477099219635 := by
  unfold tailWord_275689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055203898233311777766121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6703469265488874518510747 10055203898233311777766121)
  ·
    refine ⟨7541402923674983833324591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10055203898233311777766121 7541402923674983833324591)
    ·
      refine ⟨11312104385512475749986887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541402923674983833324591 11312104385512475749986887)
      ·
        refine ⟨16968156578268713624980331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11312104385512475749986887 16968156578268713624980331)
        ·
          refine ⟨25452234867403070437470497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16968156578268713624980331 25452234867403070437470497)
          ·
            refine ⟨19089176150552302828102873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25452234867403070437470497 19089176150552302828102873)
            ·
              refine ⟨14316882112914227121077155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19089176150552302828102873 14316882112914227121077155)
              ·
                refine ⟨21475323169371340681615733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14316882112914227121077155 21475323169371340681615733)
                ·
                  refine ⟨2013311547128563188901475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21475323169371340681615733 2013311547128563188901475)
                  ·
                    refine ⟨3019967320692844783352213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2013311547128563188901475 3019967320692844783352213)
                    ·
                      refine ⟨141560968157477099219635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3019967320692844783352213 141560968157477099219635)
                      ·
                        rfl

theorem cell23_275689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_275689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275689 prefixEnd_275689 := by exact prefixLift 275689
  have htrace : WordTrace (prefixWord ++ tailWord_275689) baseStart_275689 baseEnd_275689 := by
    simpa [prefixWord, tailWord_275689, baseEnd_275689] using wordTrace_append hprefix tailTrace_275689
  have hstable : (prefixWord ++ tailWord_275689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275689).length < 2 ^ (prefixWord ++ tailWord_275689).sum := by decide
  have hdescent : baseEnd_275689 < baseStart_275689 := by decide
  rcases family_descends (prefixWord ++ tailWord_275689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275696 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_275696 : Nat := 118140960795 + 275696 * 2 ^ 59
def prefixEnd_275696 : Nat := 4983230072969 + 3 ^ 40 * 275696 * 2
def baseEnd_275696 : Nat := 141564562522058571832103

theorem tailTrace_275696 : CollatzResearch.WordTrace tailWord_275696 prefixEnd_275696 141564562522058571832103 := by
  unfold tailWord_275696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5027729604603975986635471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6703639472805301315513961 5027729604603975986635471)
  ·
    refine ⟨7541594406905963979953207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5027729604603975986635471 7541594406905963979953207)
    ·
      refine ⟨11312391610358945969929811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541594406905963979953207 11312391610358945969929811)
      ·
        refine ⟨16968587415538418954894717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11312391610358945969929811 16968587415538418954894717)
        ·
          refine ⟨6363220280826907108085519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16968587415538418954894717 6363220280826907108085519)
          ·
            refine ⟨9544830421240360662128279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363220280826907108085519 9544830421240360662128279)
            ·
              refine ⟨14317245631860540993192419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9544830421240360662128279 14317245631860540993192419)
              ·
                refine ⟨21475868447790811489788629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14317245631860540993192419 21475868447790811489788629)
                ·
                  refine ⟨503340666745097144291921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21475868447790811489788629 503340666745097144291921)
                  ·
                    refine ⟨377505500058822858218941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 503340666745097144291921 377505500058822858218941)
                    ·
                      refine ⟨141564562522058571832103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377505500058822858218941 141564562522058571832103)
                      ·
                        rfl

theorem cell23_275696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_275696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275696 prefixEnd_275696 := by exact prefixLift 275696
  have htrace : WordTrace (prefixWord ++ tailWord_275696) baseStart_275696 baseEnd_275696 := by
    simpa [prefixWord, tailWord_275696, baseEnd_275696] using wordTrace_append hprefix tailTrace_275696
  have hstable : (prefixWord ++ tailWord_275696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275696).length < 2 ^ (prefixWord ++ tailWord_275696).sum := by decide
  have hdescent : baseEnd_275696 < baseStart_275696 := by decide
  rcases family_descends (prefixWord ++ tailWord_275696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275699 : List Nat := [1, 1, 1, 2, 2, 5, 11]
def baseStart_275699 : Nat := 118140960795 + 275699 * 2 ^ 59
def prefixEnd_275699 : Nat := 4983230072969 + 3 ^ 40 * 275699 * 2
def baseEnd_275699 : Nat := 1747729666222494569069

theorem tailTrace_275699 : CollatzResearch.WordTrace tailWord_275699 prefixEnd_275699 1747729666222494569069 := by
  unfold tailWord_275699
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055568628197083485630151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6703712418798055657086767 10055568628197083485630151)
  ·
    refine ⟨15083352942295625228445227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055568628197083485630151 15083352942295625228445227)
    ·
      refine ⟨22625029413443437842667841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15083352942295625228445227 22625029413443437842667841)
      ·
        refine ⟨16968772060082578382000881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22625029413443437842667841 16968772060082578382000881)
        ·
          refine ⟨12726579045061933786500661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16968772060082578382000881 12726579045061933786500661)
          ·
            refine ⟨1193116785474556292484437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12726579045061933786500661 1193116785474556292484437)
            ·
              refine ⟨1747729666222494569069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1193116785474556292484437 1747729666222494569069)
              ·
                rfl

theorem cell23_275699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 11].length) (baseStart_275699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275699 prefixEnd_275699 := by exact prefixLift 275699
  have htrace : WordTrace (prefixWord ++ tailWord_275699) baseStart_275699 baseEnd_275699 := by
    simpa [prefixWord, tailWord_275699, baseEnd_275699] using wordTrace_append hprefix tailTrace_275699
  have hstable : (prefixWord ++ tailWord_275699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275699).length < 2 ^ (prefixWord ++ tailWord_275699).sum := by decide
  have hdescent : baseEnd_275699 < baseStart_275699 := by decide
  rcases family_descends (prefixWord ++ tailWord_275699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275716 : List Nat := [2, 3, 2, 2, 2, 1, 1, 10]
def baseStart_275716 : Nat := 118140960795 + 275716 * 2 ^ 59
def prefixEnd_275716 : Nat := 4983230072969 + 3 ^ 40 * 275716 * 2
def baseEnd_275716 : Nat := 5243512301301796058593

theorem tailTrace_275716 : CollatzResearch.WordTrace tailWord_275716 prefixEnd_275716 5243512301301796058593 := by
  unfold tailWord_275716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028094334567747694499501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6704125779423663592666001 5028094334567747694499501)
  ·
    refine ⟨1885535375462905385437313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5028094334567747694499501 1885535375462905385437313)
    ·
      refine ⟨1414151531597179039077985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1885535375462905385437313 1414151531597179039077985)
      ·
        refine ⟨1060613648697884279308489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414151531597179039077985 1060613648697884279308489)
        ·
          refine ⟨795460236523413209481367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060613648697884279308489 795460236523413209481367)
          ·
            refine ⟨1193190354785119814222051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795460236523413209481367 1193190354785119814222051)
            ·
              refine ⟨1789785532177679721333077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193190354785119814222051 1789785532177679721333077)
              ·
                refine ⟨5243512301301796058593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1789785532177679721333077 5243512301301796058593)
                ·
                  rfl

theorem cell23_275716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 10].length) (baseStart_275716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275716 prefixEnd_275716 := by exact prefixLift 275716
  have htrace : WordTrace (prefixWord ++ tailWord_275716) baseStart_275716 baseEnd_275716 := by
    simpa [prefixWord, tailWord_275716, baseEnd_275716] using wordTrace_append hprefix tailTrace_275716
  have hstable : (prefixWord ++ tailWord_275716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275716).length < 2 ^ (prefixWord ++ tailWord_275716).sum := by decide
  have hdescent : baseEnd_275716 < baseStart_275716 := by decide
  rcases family_descends (prefixWord ++ tailWord_275716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275720 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_275720 : Nat := 118140960795 + 275720 * 2 ^ 59
def prefixEnd_275720 : Nat := 4983230072969 + 3 ^ 40 * 275720 * 2
def baseEnd_275720 : Nat := 47192295352588825977331

theorem tailTrace_275720 : CollatzResearch.WordTrace tailWord_275720 prefixEnd_275720 47192295352588825977331 := by
  unfold tailWord_275720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028167280560502036072307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6704223040747336048096409 5028167280560502036072307)
  ·
    refine ⟨7542250920840753054108461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028167280560502036072307 7542250920840753054108461)
    ·
      refine ⟨2828344095315282395290673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7542250920840753054108461 2828344095315282395290673)
      ·
        refine ⟨2121258071486461796468005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2828344095315282395290673 2121258071486461796468005)
        ·
          refine ⟨397735888403711586837751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2121258071486461796468005 397735888403711586837751)
          ·
            refine ⟨596603832605567380256627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397735888403711586837751 596603832605567380256627)
            ·
              refine ⟨894905748908351070384941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596603832605567380256627 894905748908351070384941)
              ·
                refine ⟨335589655840631651394353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 894905748908351070384941 335589655840631651394353)
                ·
                  refine ⟨251692241880473738545765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335589655840631651394353 251692241880473738545765)
                  ·
                    refine ⟨47192295352588825977331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251692241880473738545765 47192295352588825977331)
                    ·
                      rfl

theorem cell23_275720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_275720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275720 prefixEnd_275720 := by exact prefixLift 275720
  have htrace : WordTrace (prefixWord ++ tailWord_275720) baseStart_275720 baseEnd_275720 := by
    simpa [prefixWord, tailWord_275720, baseEnd_275720] using wordTrace_append hprefix tailTrace_275720
  have hstable : (prefixWord ++ tailWord_275720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275720).length < 2 ^ (prefixWord ++ tailWord_275720).sum := by decide
  have hdescent : baseEnd_275720 < baseStart_275720 := by decide
  rcases family_descends (prefixWord ++ tailWord_275720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275760 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3]
def baseStart_275760 : Nat := 118140960795 + 275760 * 2 ^ 59
def prefixEnd_275760 : Nat := 4983230072969 + 3 ^ 40 * 275760 * 2
def baseEnd_275760 : Nat := 141597425283946321431809

theorem tailTrace_275760 : CollatzResearch.WordTrace tailWord_275760 prefixEnd_275760 141597425283946321431809 := by
  unfold tailWord_275760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028896740488045451800367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6705195653984060602400489 5028896740488045451800367)
  ·
    refine ⟨7543345110732068177700551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028896740488045451800367 7543345110732068177700551)
    ·
      refine ⟨11315017666098102266550827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543345110732068177700551 11315017666098102266550827)
      ·
        refine ⟨16972526499147153399826241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11315017666098102266550827 16972526499147153399826241)
        ·
          refine ⟨12729394874360365049869681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16972526499147153399826241 12729394874360365049869681)
          ·
            refine ⟨9547046155770273787402261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12729394874360365049869681 9547046155770273787402261)
            ·
              refine ⟨447517788551731583784481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9547046155770273787402261 447517788551731583784481)
              ·
                refine ⟨335638341413798687838361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447517788551731583784481 335638341413798687838361)
                ·
                  refine ⟨251728756060349015878771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335638341413798687838361 251728756060349015878771)
                  ·
                    refine ⟨377593134090523523818157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251728756060349015878771 377593134090523523818157)
                    ·
                      refine ⟨141597425283946321431809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377593134090523523818157 141597425283946321431809)
                      ·
                        rfl

theorem cell23_275760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_275760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275760 prefixEnd_275760 := by exact prefixLift 275760
  have htrace : WordTrace (prefixWord ++ tailWord_275760) baseStart_275760 baseEnd_275760 := by
    simpa [prefixWord, tailWord_275760, baseEnd_275760] using wordTrace_append hprefix tailTrace_275760
  have hstable : (prefixWord ++ tailWord_275760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275760).length < 2 ^ (prefixWord ++ tailWord_275760).sum := by decide
  have hdescent : baseEnd_275760 < baseStart_275760 := by decide
  rcases family_descends (prefixWord ++ tailWord_275760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275761 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 1, 2, 2]
def baseStart_275761 : Nat := 118140960795 + 275761 * 2 ^ 59
def prefixEnd_275761 : Nat := 4983230072969 + 3 ^ 40 * 275761 * 2
def baseEnd_275761 : Nat := 141597938764600817519305

theorem tailTrace_275761 : CollatzResearch.WordTrace tailWord_275761 prefixEnd_275761 141597938764600817519305 := by
  unfold tailWord_275761
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057829953972468074387137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6705219969314978716258091 10057829953972468074387137)
  ·
    refine ⟨7543372465479351055790353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10057829953972468074387137 7543372465479351055790353)
    ·
      refine ⟨5657529349109513291842765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7543372465479351055790353 5657529349109513291842765)
      ·
        refine ⟨2121573505916067484441037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5657529349109513291842765 2121573505916067484441037)
        ·
          refine ⟨795590064718525306665389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2121573505916067484441037 795590064718525306665389)
          ·
            refine ⟨298346274269446989999521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 795590064718525306665389 298346274269446989999521)
            ·
              refine ⟨223759705702085242499641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298346274269446989999521 223759705702085242499641)
              ·
                refine ⟨167819779276563931874731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223759705702085242499641 167819779276563931874731)
                ·
                  refine ⟨251729668914845897812097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167819779276563931874731 251729668914845897812097)
                  ·
                    refine ⟨188797251686134423359073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251729668914845897812097 188797251686134423359073)
                    ·
                      refine ⟨141597938764600817519305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188797251686134423359073 141597938764600817519305)
                      ·
                        rfl

theorem cell23_275761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_275761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275761 prefixEnd_275761 := by exact prefixLift 275761
  have htrace : WordTrace (prefixWord ++ tailWord_275761) baseStart_275761 baseEnd_275761 := by
    simpa [prefixWord, tailWord_275761, baseEnd_275761] using wordTrace_append hprefix tailTrace_275761
  have hstable : (prefixWord ++ tailWord_275761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275761).length < 2 ^ (prefixWord ++ tailWord_275761).sum := by decide
  have hdescent : baseEnd_275761 < baseStart_275761 := by decide
  rcases family_descends (prefixWord ++ tailWord_275761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275776 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_275776 : Nat := 118140960795 + 275776 * 2 ^ 59
def prefixEnd_275776 : Nat := 4983230072969 + 3 ^ 40 * 275776 * 2
def baseEnd_275776 : Nat := 47201880324806086277245

theorem tailTrace_275776 : CollatzResearch.WordTrace tailWord_275776 prefixEnd_275776 47201880324806086277245 := by
  unfold tailWord_275776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029188524459062818091591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6705584699278750424122121 5029188524459062818091591)
  ·
    refine ⟨7543782786688594227137387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029188524459062818091591 7543782786688594227137387)
    ·
      refine ⟨11315674180032891340706081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543782786688594227137387 11315674180032891340706081)
      ·
        refine ⟨8486755635024668505529561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11315674180032891340706081 8486755635024668505529561)
        ·
          refine ⟨6365066726268501379147171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8486755635024668505529561 6365066726268501379147171)
          ·
            refine ⟨9547600089402752068720757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6365066726268501379147171 9547600089402752068720757)
            ·
              refine ⟨895087508381508006442571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9547600089402752068720757 895087508381508006442571)
              ·
                refine ⟨1342631262572262009663857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895087508381508006442571 1342631262572262009663857)
                ·
                  refine ⟨1006973446929196507247893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342631262572262009663857 1006973446929196507247893)
                  ·
                    refine ⟨47201880324806086277245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1006973446929196507247893 47201880324806086277245)
                    ·
                      rfl

theorem cell23_275776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_275776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275776 prefixEnd_275776 := by exact prefixLift 275776
  have htrace : WordTrace (prefixWord ++ tailWord_275776) baseStart_275776 baseEnd_275776 := by
    simpa [prefixWord, tailWord_275776, baseEnd_275776] using wordTrace_append hprefix tailTrace_275776
  have hstable : (prefixWord ++ tailWord_275776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275776).length < 2 ^ (prefixWord ++ tailWord_275776).sum := by decide
  have hdescent : baseEnd_275776 < baseStart_275776 := by decide
  rcases family_descends (prefixWord ++ tailWord_275776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275777 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_275777 : Nat := 118140960795 + 275777 * 2 ^ 59
def prefixEnd_275777 : Nat := 4983230072969 + 3 ^ 40 * 275777 * 2
def baseEnd_275777 : Nat := 141606154455072754919231

theorem tailTrace_275777 : CollatzResearch.WordTrace tailWord_275777 prefixEnd_275777 141606154455072754919231 := by
  unfold tailWord_275777
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058413521914502806969585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6705609014609668537979723 10058413521914502806969585)
  ·
    refine ⟨7543810141435877105227189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058413521914502806969585 7543810141435877105227189)
    ·
      refine ⟨707232200759613478615049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7543810141435877105227189 707232200759613478615049)
      ·
        refine ⟨530424150569710108961287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 707232200759613478615049 530424150569710108961287)
        ·
          refine ⟨795636225854565163441931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530424150569710108961287 795636225854565163441931)
          ·
            refine ⟨1193454338781847745162897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795636225854565163441931 1193454338781847745162897)
            ·
              refine ⟨895090754086385808872173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193454338781847745162897 895090754086385808872173)
              ·
                refine ⟨335659032782394678327065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 895090754086385808872173 335659032782394678327065)
                ·
                  refine ⟨251744274586796008745299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335659032782394678327065 251744274586796008745299)
                  ·
                    refine ⟨377616411880194013117949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251744274586796008745299 377616411880194013117949)
                    ·
                      refine ⟨141606154455072754919231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377616411880194013117949 141606154455072754919231)
                      ·
                        rfl

theorem cell23_275777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_275777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275777 prefixEnd_275777 := by exact prefixLift 275777
  have htrace : WordTrace (prefixWord ++ tailWord_275777) baseStart_275777 baseEnd_275777 := by
    simpa [prefixWord, tailWord_275777, baseEnd_275777] using wordTrace_append hprefix tailTrace_275777
  have hstable : (prefixWord ++ tailWord_275777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275777).length < 2 ^ (prefixWord ++ tailWord_275777).sum := by decide
  have hdescent : baseEnd_275777 < baseStart_275777 := by decide
  rcases family_descends (prefixWord ++ tailWord_275777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275786 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_275786 : Nat := 118140960795 + 275786 * 2 ^ 59
def prefixEnd_275786 : Nat := 4983230072969 + 3 ^ 40 * 275786 * 2
def baseEnd_275786 : Nat := 141610775780963219706689

theorem tailTrace_275786 : CollatzResearch.WordTrace tailWord_275786 prefixEnd_275786 141610775780963219706689 := by
  unfold tailWord_275786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514685444720474336011803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6705827852587931562698141 2514685444720474336011803)
  ·
    refine ⟨3772028167080711504017705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2514685444720474336011803 3772028167080711504017705)
    ·
      refine ⟨2829021125310533628013279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3772028167080711504017705 2829021125310533628013279)
      ·
        refine ⟨4243531687965800442019919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829021125310533628013279 4243531687965800442019919)
        ·
          refine ⟨6365297531948700663029879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243531687965800442019919 6365297531948700663029879)
          ·
            refine ⟨9547946297923050994544819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6365297531948700663029879 9547946297923050994544819)
            ·
              refine ⟨14321919446884576491817229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9547946297923050994544819 14321919446884576491817229)
              ·
                refine ⟨5370719792581716184431461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14321919446884576491817229 5370719792581716184431461)
                ·
                  refine ⟨1007009961109071784580899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5370719792581716184431461 1007009961109071784580899)
                  ·
                    refine ⟨1510514941663607676871349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1007009961109071784580899 1510514941663607676871349)
                    ·
                      refine ⟨141610775780963219706689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1510514941663607676871349 141610775780963219706689)
                      ·
                        rfl

theorem cell23_275786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_275786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275786 prefixEnd_275786 := by exact prefixLift 275786
  have htrace : WordTrace (prefixWord ++ tailWord_275786) baseStart_275786 baseEnd_275786 := by
    simpa [prefixWord, tailWord_275786, baseEnd_275786] using wordTrace_append hprefix tailTrace_275786
  have hstable : (prefixWord ++ tailWord_275786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275786).length < 2 ^ (prefixWord ++ tailWord_275786).sum := by decide
  have hdescent : baseEnd_275786 < baseStart_275786 := by decide
  rcases family_descends (prefixWord ++ tailWord_275786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275800 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_275800 : Nat := 118140960795 + 275800 * 2 ^ 59
def prefixEnd_275800 : Nat := 4983230072969 + 3 ^ 40 * 275800 * 2
def baseEnd_275800 : Nat := 141617964510126164931625

theorem tailTrace_275800 : CollatzResearch.WordTrace tailWord_275800 prefixEnd_275800 141617964510126164931625 := by
  unfold tailWord_275800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029626200415588867528427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6706168267220785156704569 5029626200415588867528427)
  ·
    refine ⟨7544439300623383301292641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029626200415588867528427 7544439300623383301292641)
    ·
      refine ⟨5658329475467537475969481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7544439300623383301292641 5658329475467537475969481)
      ·
        refine ⟨4243747106600653106977111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5658329475467537475969481 4243747106600653106977111)
        ·
          refine ⟨6365620659900979660465667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243747106600653106977111 6365620659900979660465667)
          ·
            refine ⟨9548430989851469490698501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6365620659900979660465667 9548430989851469490698501)
            ·
              refine ⟨1790330810597150529505969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9548430989851469490698501 1790330810597150529505969)
              ·
                refine ⟨1342748107947862897129477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790330810597150529505969 1342748107947862897129477)
                ·
                  refine ⟨251765270240224293211777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1342748107947862897129477 251765270240224293211777)
                  ·
                    refine ⟨188823952680168219908833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251765270240224293211777 188823952680168219908833)
                    ·
                      refine ⟨141617964510126164931625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188823952680168219908833 141617964510126164931625)
                      ·
                        rfl

theorem cell23_275800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_275800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275800 prefixEnd_275800 := by exact prefixLift 275800
  have htrace : WordTrace (prefixWord ++ tailWord_275800) baseStart_275800 baseEnd_275800 := by
    simpa [prefixWord, tailWord_275800, baseEnd_275800] using wordTrace_append hprefix tailTrace_275800
  have hstable : (prefixWord ++ tailWord_275800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275800).length < 2 ^ (prefixWord ++ tailWord_275800).sum := by decide
  have hdescent : baseEnd_275800 < baseStart_275800 := by decide
  rcases family_descends (prefixWord ++ tailWord_275800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275823 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 5]
def baseStart_275823 : Nat := 118140960795 + 275823 * 2 ^ 59
def prefixEnd_275823 : Nat := 4983230072969 + 3 ^ 40 * 275823 * 2
def baseEnd_275823 : Nat := 15736641618353286104891

theorem tailTrace_275823 : CollatzResearch.WordTrace tailWord_275823 prefixEnd_275823 15736641618353286104891 := by
  unfold tailWord_275823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060091279747852663144123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6706727519831901775429415 10060091279747852663144123)
  ·
    refine ⟨15090136919621778994716185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060091279747852663144123 15090136919621778994716185)
    ·
      refine ⟨11317602689716334246037139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15090136919621778994716185 11317602689716334246037139)
      ·
        refine ⟨16976404034574501369055709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11317602689716334246037139 16976404034574501369055709)
        ·
          refine ⟨6366151512965438013395891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16976404034574501369055709 6366151512965438013395891)
          ·
            refine ⟨9549227269448157020093837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366151512965438013395891 9549227269448157020093837)
            ·
              refine ⟨3580960226043058882535189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9549227269448157020093837 3580960226043058882535189)
              ·
                refine ⟨167857510595768385118837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3580960226043058882535189 167857510595768385118837)
                ·
                  refine ⟨15736641618353286104891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167857510595768385118837 15736641618353286104891)
                  ·
                    rfl

theorem cell23_275823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 5].length) (baseStart_275823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275823 prefixEnd_275823 := by exact prefixLift 275823
  have htrace : WordTrace (prefixWord ++ tailWord_275823) baseStart_275823 baseEnd_275823 := by
    simpa [prefixWord, tailWord_275823, baseEnd_275823] using wordTrace_append hprefix tailTrace_275823
  have hstable : (prefixWord ++ tailWord_275823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275823).length < 2 ^ (prefixWord ++ tailWord_275823).sum := by decide
  have hdescent : baseEnd_275823 < baseStart_275823 := by decide
  rcases family_descends (prefixWord ++ tailWord_275823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275833 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_275833 : Nat := 118140960795 + 275833 * 2 ^ 59
def prefixEnd_275833 : Nat := 4983230072969 + 3 ^ 40 * 275833 * 2
def baseEnd_275833 : Nat := 141634909371724535818973

theorem tailTrace_275833 : CollatzResearch.WordTrace tailWord_275833 prefixEnd_275833 141634909371724535818973 := by
  unfold tailWord_275833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060456009711624371008153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6706970673141082914005435 10060456009711624371008153)
  ·
    refine ⟨7545342007283718278256115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10060456009711624371008153 7545342007283718278256115)
    ·
      refine ⟨11318013010925577417384173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7545342007283718278256115 11318013010925577417384173)
      ·
        refine ⟨4244254879097091531519065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11318013010925577417384173 4244254879097091531519065)
        ·
          refine ⟨3183191159322818648639299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4244254879097091531519065 3183191159322818648639299)
          ·
            refine ⟨4774786738984227972958949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183191159322818648639299 4774786738984227972958949)
            ·
              refine ⟨895272513559542744929803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4774786738984227972958949 895272513559542744929803)
              ·
                refine ⟨1342908770339314117394705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895272513559542744929803 1342908770339314117394705)
                ·
                  refine ⟨1007181577754485588046029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342908770339314117394705 1007181577754485588046029)
                  ·
                    refine ⟨377693091657932095517261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1007181577754485588046029 377693091657932095517261)
                    ·
                      refine ⟨141634909371724535818973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377693091657932095517261 141634909371724535818973)
                      ·
                        rfl

theorem cell23_275833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_275833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275833 prefixEnd_275833 := by exact prefixLift 275833
  have htrace : WordTrace (prefixWord ++ tailWord_275833) baseStart_275833 baseEnd_275833 := by
    simpa [prefixWord, tailWord_275833, baseEnd_275833] using wordTrace_append hprefix tailTrace_275833
  have hstable : (prefixWord ++ tailWord_275833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275833).length < 2 ^ (prefixWord ++ tailWord_275833).sum := by decide
  have hdescent : baseEnd_275833 < baseStart_275833 := by decide
  rcases family_descends (prefixWord ++ tailWord_275833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275836 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_275836 : Nat := 118140960795 + 275836 * 2 ^ 59
def prefixEnd_275836 : Nat := 4983230072969 + 3 ^ 40 * 275836 * 2
def baseEnd_275836 : Nat := 47212149937896008027153

theorem tailTrace_275836 : CollatzResearch.WordTrace tailWord_275836 prefixEnd_275836 47212149937896008027153 := by
  unfold tailWord_275836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030282714350377941683681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6707043619133837255578241 5030282714350377941683681)
  ·
    refine ⟨3772712035762783456262761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5030282714350377941683681 3772712035762783456262761)
    ·
      refine ⟨2829534026822087592197071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3772712035762783456262761 2829534026822087592197071)
      ·
        refine ⟨4244301040233131388295607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829534026822087592197071 4244301040233131388295607)
        ·
          refine ⟨6366451560349697082443411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244301040233131388295607 6366451560349697082443411)
          ·
            refine ⟨9549677340524545623665117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366451560349697082443411 9549677340524545623665117)
            ·
              refine ⟨3581129002696704608874419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9549677340524545623665117 3581129002696704608874419)
              ·
                refine ⟨5371693504045056913311629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581129002696704608874419 5371693504045056913311629)
                ·
                  refine ⟨2014385064016896342491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5371693504045056913311629 2014385064016896342491861)
                  ·
                    refine ⟨47212149937896008027153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2014385064016896342491861 47212149937896008027153)
                    ·
                      rfl

theorem cell23_275836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_275836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275836 prefixEnd_275836 := by exact prefixLift 275836
  have htrace : WordTrace (prefixWord ++ tailWord_275836) baseStart_275836 baseEnd_275836 := by
    simpa [prefixWord, tailWord_275836, baseEnd_275836] using wordTrace_append hprefix tailTrace_275836
  have hstable : (prefixWord ++ tailWord_275836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275836).length < 2 ^ (prefixWord ++ tailWord_275836).sum := by decide
  have hdescent : baseEnd_275836 < baseStart_275836 := by decide
  rcases family_descends (prefixWord ++ tailWord_275836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275930 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_275930 : Nat := 118140960795 + 275930 * 2 ^ 59
def prefixEnd_275930 : Nat := 4983230072969 + 3 ^ 40 * 275930 * 2
def baseEnd_275930 : Nat := 15742746332801184034003

theorem tailTrace_275930 : CollatzResearch.WordTrace tailWord_275930 prefixEnd_275930 15742746332801184034003 := by
  unfold tailWord_275930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515998472590052484322311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6709329260240139958192829 2515998472590052484322311)
  ·
    refine ⟨3773997708885078726483467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515998472590052484322311 3773997708885078726483467)
    ·
      refine ⟨5660996563327618089725201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773997708885078726483467 5660996563327618089725201)
      ·
        refine ⟨4245747422495713567293901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5660996563327618089725201 4245747422495713567293901)
        ·
          refine ⟨1592155283435892587735213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4245747422495713567293901 1592155283435892587735213)
          ·
            refine ⟨597058231288459720400705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1592155283435892587735213 597058231288459720400705)
            ·
              refine ⟨447793673466344790300529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597058231288459720400705 447793673466344790300529)
              ·
                refine ⟨335845255099758592725397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447793673466344790300529 335845255099758592725397)
                ·
                  refine ⟨15742746332801184034003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335845255099758592725397 15742746332801184034003)
                  ·
                    rfl

theorem cell23_275930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_275930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275930 prefixEnd_275930 := by exact prefixLift 275930
  have htrace : WordTrace (prefixWord ++ tailWord_275930) baseStart_275930 baseEnd_275930 := by
    simpa [prefixWord, tailWord_275930, baseEnd_275930] using wordTrace_append hprefix tailTrace_275930
  have hstable : (prefixWord ++ tailWord_275930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275930).length < 2 ^ (prefixWord ++ tailWord_275930).sum := by decide
  have hdescent : baseEnd_275930 < baseStart_275930 := by decide
  rcases family_descends (prefixWord ++ tailWord_275930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275940 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_275940 : Nat := 118140960795 + 275940 * 2 ^ 59
def prefixEnd_275940 : Nat := 4983230072969 + 3 ^ 40 * 275940 * 2
def baseEnd_275940 : Nat := 141689851801755617180981

theorem tailTrace_275940 : CollatzResearch.WordTrace tailWord_275940 prefixEnd_275940 141689851801755617180981 := by
  unfold tailWord_275940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032179310161990822576637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6709572413549321096768849 5032179310161990822576637)
  ·
    refine ⟨1887067241310746558466239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5032179310161990822576637 1887067241310746558466239)
    ·
      refine ⟨2830600861966119837699359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887067241310746558466239 2830600861966119837699359)
      ·
        refine ⟨4245901292949179756549039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830600861966119837699359 4245901292949179756549039)
        ·
          refine ⟨6368851939423769634823559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245901292949179756549039 6368851939423769634823559)
          ·
            refine ⟨9553277909135654452235339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368851939423769634823559 9553277909135654452235339)
            ·
              refine ⟨14329916863703481678353009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9553277909135654452235339 14329916863703481678353009)
              ·
                refine ⟨10747437647777611258764757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14329916863703481678353009 10747437647777611258764757)
                ·
                  refine ⟨251893069869787763877299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10747437647777611258764757 251893069869787763877299)
                  ·
                    refine ⟨377839604804681645815949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251893069869787763877299 377839604804681645815949)
                    ·
                      refine ⟨141689851801755617180981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377839604804681645815949 141689851801755617180981)
                      ·
                        rfl

theorem cell23_275940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_275940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275940 prefixEnd_275940 := by exact prefixLift 275940
  have htrace : WordTrace (prefixWord ++ tailWord_275940) baseStart_275940 baseEnd_275940 := by
    simpa [prefixWord, tailWord_275940, baseEnd_275940] using wordTrace_append hprefix tailTrace_275940
  have hstable : (prefixWord ++ tailWord_275940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275940).length < 2 ^ (prefixWord ++ tailWord_275940).sum := by decide
  have hdescent : baseEnd_275940 < baseStart_275940 := by decide
  rcases family_descends (prefixWord ++ tailWord_275940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275981 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 6]
def baseStart_275981 : Nat := 118140960795 + 275981 * 2 ^ 59
def prefixEnd_275981 : Nat := 4983230072969 + 3 ^ 40 * 275981 * 2
def baseEnd_275981 : Nat := 15745656056509995196477

theorem tailTrace_275981 : CollatzResearch.WordTrace tailWord_275981 prefixEnd_275981 15745656056509995196477 := by
  unfold tailWord_275981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10065854013175445647395797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6710569342116963764930531 10065854013175445647395797)
  ·
    refine ⟨235918453433799507360839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10065854013175445647395797 235918453433799507360839)
    ·
      refine ⟨353877680150699261041259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235918453433799507360839 353877680150699261041259)
      ·
        refine ⟨530816520226048891561889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353877680150699261041259 530816520226048891561889)
        ·
          refine ⟨398112390169536668671417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530816520226048891561889 398112390169536668671417)
          ·
            refine ⟨298584292627152501503563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398112390169536668671417 298584292627152501503563)
            ·
              refine ⟨447876438940728752255345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298584292627152501503563 447876438940728752255345)
              ·
                refine ⟨335907329205546564191509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447876438940728752255345 335907329205546564191509)
                ·
                  refine ⟨15745656056509995196477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335907329205546564191509 15745656056509995196477)
                  ·
                    rfl

theorem cell23_275981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_275981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275981 prefixEnd_275981 := by exact prefixLift 275981
  have htrace : WordTrace (prefixWord ++ tailWord_275981) baseStart_275981 baseEnd_275981 := by
    simpa [prefixWord, tailWord_275981, baseEnd_275981] using wordTrace_append hprefix tailTrace_275981
  have hstable : (prefixWord ++ tailWord_275981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275981).length < 2 ^ (prefixWord ++ tailWord_275981).sum := by decide
  have hdescent : baseEnd_275981 < baseStart_275981 := by decide
  rcases family_descends (prefixWord ++ tailWord_275981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275983 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_275983 : Nat := 118140960795 + 275983 * 2 ^ 59
def prefixEnd_275983 : Nat := 4983230072969 + 3 ^ 40 * 275983 * 2
def baseEnd_275983 : Nat := 141711931469898948943283

theorem tailTrace_275983 : CollatzResearch.WordTrace tailWord_275983 prefixEnd_275983 141711931469898948943283 := by
  unfold tailWord_275983
  simp only [CollatzResearch.WordTrace]
  refine ⟨10065926959168199988968603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6710617972778799992645735 10065926959168199988968603)
  ·
    refine ⟨15098890438752299983452905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10065926959168199988968603 15098890438752299983452905)
    ·
      refine ⟨11324167829064224987589679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15098890438752299983452905 11324167829064224987589679)
      ·
        refine ⟨16986251743596337481384519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11324167829064224987589679 16986251743596337481384519)
        ·
          refine ⟨25479377615394506222076779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16986251743596337481384519 25479377615394506222076779)
          ·
            refine ⟨38219066423091759333115169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25479377615394506222076779 38219066423091759333115169)
            ·
              refine ⟨28664299817318819499836377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38219066423091759333115169 28664299817318819499836377)
              ·
                refine ⟨21498224862989114624877283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28664299817318819499836377 21498224862989114624877283)
                ·
                  refine ⟨32247337294483671937315925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21498224862989114624877283 32247337294483671937315925)
                  ·
                    refine ⟨377898483919730530515421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32247337294483671937315925 377898483919730530515421)
                    ·
                      refine ⟨141711931469898948943283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377898483919730530515421 141711931469898948943283)
                      ·
                        rfl

theorem cell23_275983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_275983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275983 prefixEnd_275983 := by exact prefixLift 275983
  have htrace : WordTrace (prefixWord ++ tailWord_275983) baseStart_275983 baseEnd_275983 := by
    simpa [prefixWord, tailWord_275983, baseEnd_275983] using wordTrace_append hprefix tailTrace_275983
  have hstable : (prefixWord ++ tailWord_275983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275983).length < 2 ^ (prefixWord ++ tailWord_275983).sum := by decide
  have hdescent : baseEnd_275983 < baseStart_275983 := by decide
  rcases family_descends (prefixWord ++ tailWord_275983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275998 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_275998 : Nat := 118140960795 + 275998 * 2 ^ 59
def prefixEnd_275998 : Nat := 4983230072969 + 3 ^ 40 * 275998 * 2
def baseEnd_275998 : Nat := 15746625964412932250635

theorem tailTrace_275998 : CollatzResearch.WordTrace tailWord_275998 prefixEnd_275998 15746625964412932250635 := by
  unfold tailWord_275998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258309256764232193845581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6710982702742571700509765 1258309256764232193845581)
  ·
    refine ⟨471865971286587072692093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1258309256764232193845581 471865971286587072692093)
    ·
      refine ⟨176949739232470152259535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 471865971286587072692093 176949739232470152259535)
      ·
        refine ⟨265424608848705228389303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176949739232470152259535 265424608848705228389303)
        ·
          refine ⟨398136913273057842583955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265424608848705228389303 398136913273057842583955)
          ·
            refine ⟨597205369909586763875933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398136913273057842583955 597205369909586763875933)
            ·
              refine ⟨223952013716095036453475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597205369909586763875933 223952013716095036453475)
              ·
                refine ⟨335928020574142554680213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223952013716095036453475 335928020574142554680213)
                ·
                  refine ⟨15746625964412932250635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335928020574142554680213 15746625964412932250635)
                  ·
                    rfl

theorem cell23_275998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_275998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_275998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_275998 prefixEnd_275998 := by exact prefixLift 275998
  have htrace : WordTrace (prefixWord ++ tailWord_275998) baseStart_275998 baseEnd_275998 := by
    simpa [prefixWord, tailWord_275998, baseEnd_275998] using wordTrace_append hprefix tailTrace_275998
  have hstable : (prefixWord ++ tailWord_275998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275998).length < 2 ^ (prefixWord ++ tailWord_275998).sum := by decide
  have hdescent : baseEnd_275998 < baseStart_275998 := by decide
  rcases family_descends (prefixWord ++ tailWord_275998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276000 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_276000 : Nat := 118140960795 + 276000 * 2 ^ 59
def prefixEnd_276000 : Nat := 4983230072969 + 3 ^ 40 * 276000 * 2
def baseEnd_276000 : Nat := 141720660641025382430705

theorem tailTrace_276000 : CollatzResearch.WordTrace tailWord_276000 prefixEnd_276000 141720660641025382430705 := by
  unfold tailWord_276000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033273500053305946168727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6711031333404407928224969 5033273500053305946168727)
  ·
    refine ⟨7549910250079958919253091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5033273500053305946168727 7549910250079958919253091)
    ·
      refine ⟨11324865375119938378879637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7549910250079958919253091 11324865375119938378879637)
      ·
        refine ⟨530853064458747111509983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11324865375119938378879637 530853064458747111509983)
        ·
          refine ⟨796279596688120667264975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530853064458747111509983 796279596688120667264975)
          ·
            refine ⟨1194419395032181000897463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796279596688120667264975 1194419395032181000897463)
            ·
              refine ⟨1791629092548271501346195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194419395032181000897463 1791629092548271501346195)
              ·
                refine ⟨2687443638822407252019293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791629092548271501346195 2687443638822407252019293)
                ·
                  refine ⟨1007791364558402719507235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2687443638822407252019293 1007791364558402719507235)
                  ·
                    refine ⟨1511687046837604079260853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1007791364558402719507235 1511687046837604079260853)
                    ·
                      refine ⟨141720660641025382430705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1511687046837604079260853 141720660641025382430705)
                      ·
                        rfl

theorem cell23_276000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_276000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276000 prefixEnd_276000 := by exact prefixLift 276000
  have htrace : WordTrace (prefixWord ++ tailWord_276000) baseStart_276000 baseEnd_276000 := by
    simpa [prefixWord, tailWord_276000, baseEnd_276000] using wordTrace_append hprefix tailTrace_276000
  have hstable : (prefixWord ++ tailWord_276000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276000).length < 2 ^ (prefixWord ++ tailWord_276000).sum := by decide
  have hdescent : baseEnd_276000 < baseStart_276000 := by decide
  rcases family_descends (prefixWord ++ tailWord_276000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276010 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_276010 : Nat := 118140960795 + 276010 * 2 ^ 59
def prefixEnd_276010 : Nat := 4983230072969 + 3 ^ 40 * 276010 * 2
def baseEnd_276010 : Nat := 141725795447570343305659

theorem tailTrace_276010 : CollatzResearch.WordTrace tailWord_276010 prefixEnd_276010 141725795447570343305659 := by
  unfold tailWord_276010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516727932517595900050371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6711274486713589066800989 2516727932517595900050371)
  ·
    refine ⟨3775091898776393850075557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2516727932517595900050371 3775091898776393850075557)
    ·
      refine ⟨707829731020573846889167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3775091898776393850075557 707829731020573846889167)
      ·
        refine ⟨1061744596530860770333751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707829731020573846889167 1061744596530860770333751)
        ·
          refine ⟨1592616894796291155500627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061744596530860770333751 1592616894796291155500627)
          ·
            refine ⟨2388925342194436733250941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592616894796291155500627 2388925342194436733250941)
            ·
              refine ⟨895847003322913774969103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2388925342194436733250941 895847003322913774969103)
              ·
                refine ⟨1343770504984370662453655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895847003322913774969103 1343770504984370662453655)
                ·
                  refine ⟨2015655757476555993680483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343770504984370662453655 2015655757476555993680483)
                  ·
                    refine ⟨3023483636214833990520725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015655757476555993680483 3023483636214833990520725)
                    ·
                      refine ⟨141725795447570343305659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3023483636214833990520725 141725795447570343305659)
                      ·
                        rfl

theorem cell23_276010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_276010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276010 prefixEnd_276010 := by exact prefixLift 276010
  have htrace : WordTrace (prefixWord ++ tailWord_276010) baseStart_276010 baseEnd_276010 := by
    simpa [prefixWord, tailWord_276010, baseEnd_276010] using wordTrace_append hprefix tailTrace_276010
  have hstable : (prefixWord ++ tailWord_276010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276010).length < 2 ^ (prefixWord ++ tailWord_276010).sum := by decide
  have hdescent : baseEnd_276010 < baseStart_276010 := by decide
  rcases family_descends (prefixWord ++ tailWord_276010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276014 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_276014 : Nat := 118140960795 + 276014 * 2 ^ 59
def prefixEnd_276014 : Nat := 4983230072969 + 3 ^ 40 * 276014 * 2
def baseEnd_276014 : Nat := 141727849370188327655641

theorem tailTrace_276014 : CollatzResearch.WordTrace tailWord_276014 prefixEnd_276014 141727849370188327655641 := by
  unfold tailWord_276014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258382202756986535418387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6711371748037261522231397 1258382202756986535418387)
  ·
    refine ⟨1887573304135479803127581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258382202756986535418387 1887573304135479803127581)
    ·
      refine ⟨707839989050804926172843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1887573304135479803127581 707839989050804926172843)
      ·
        refine ⟨1061759983576207389259265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707839989050804926172843 1061759983576207389259265)
        ·
          refine ⟨796319987682155541944449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061759983576207389259265 796319987682155541944449)
          ·
            refine ⟨597239990761616656458337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796319987682155541944449 597239990761616656458337)
            ·
              refine ⟨447929993071212492343753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597239990761616656458337 447929993071212492343753)
              ·
                refine ⟨335947494803409369257815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447929993071212492343753 335947494803409369257815)
                ·
                  refine ⟨503921242205114053886723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 335947494803409369257815 503921242205114053886723)
                  ·
                    refine ⟨755881863307671080830085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 503921242205114053886723 755881863307671080830085)
                    ·
                      refine ⟨141727849370188327655641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 755881863307671080830085 141727849370188327655641)
                      ·
                        rfl

theorem cell23_276014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_276014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276014 prefixEnd_276014 := by exact prefixLift 276014
  have htrace : WordTrace (prefixWord ++ tailWord_276014) baseStart_276014 baseEnd_276014 := by
    simpa [prefixWord, tailWord_276014, baseEnd_276014] using wordTrace_append hprefix tailTrace_276014
  have hstable : (prefixWord ++ tailWord_276014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276014).length < 2 ^ (prefixWord ++ tailWord_276014).sum := by decide
  have hdescent : baseEnd_276014 < baseStart_276014 := by decide
  rcases family_descends (prefixWord ++ tailWord_276014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276031 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 1, 2, 2]
def baseStart_276031 : Nat := 118140960795 + 276031 * 2 ^ 59
def prefixEnd_276031 : Nat := 4983230072969 + 3 ^ 40 * 276031 * 2
def baseEnd_276031 : Nat := 141736578541314761143063

theorem tailTrace_276031 : CollatzResearch.WordTrace tailWord_276031 prefixEnd_276031 141736578541314761143063 := by
  unfold tailWord_276031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10067677662994304186715947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6711785108662869457810631 10067677662994304186715947)
  ·
    refine ⟨15101516494491456280073921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10067677662994304186715947 15101516494491456280073921)
    ·
      refine ⟨11326137370868592210055441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15101516494491456280073921 11326137370868592210055441)
      ·
        refine ⟨8494603028151444157541581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11326137370868592210055441 8494603028151444157541581)
        ·
          refine ⟨3185476135556791559078093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8494603028151444157541581 3185476135556791559078093)
          ·
            refine ⟨1194553550833796834654285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3185476135556791559078093 1194553550833796834654285)
            ·
              refine ⟨447957581562673812995357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1194553550833796834654285 447957581562673812995357)
              ·
                refine ⟨167984093086002679873259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 447957581562673812995357 167984093086002679873259)
                ·
                  refine ⟨251976139629004019809889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167984093086002679873259 251976139629004019809889)
                  ·
                    refine ⟨188982104721753014857417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251976139629004019809889 188982104721753014857417)
                    ·
                      refine ⟨141736578541314761143063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 188982104721753014857417 141736578541314761143063)
                      ·
                        rfl

theorem cell23_276031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_276031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276031 prefixEnd_276031 := by exact prefixLift 276031
  have htrace : WordTrace (prefixWord ++ tailWord_276031) baseStart_276031 baseEnd_276031 := by
    simpa [prefixWord, tailWord_276031, baseEnd_276031] using wordTrace_append hprefix tailTrace_276031
  have hstable : (prefixWord ++ tailWord_276031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276031).length < 2 ^ (prefixWord ++ tailWord_276031).sum := by decide
  have hdescent : baseEnd_276031 < baseStart_276031 := by decide
  rcases family_descends (prefixWord ++ tailWord_276031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276043 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_276043 : Nat := 118140960795 + 276043 * 2 ^ 59
def prefixEnd_276043 : Nat := 4983230072969 + 3 ^ 40 * 276043 * 2
def baseEnd_276043 : Nat := 141742740309168714193007

theorem tailTrace_276043 : CollatzResearch.WordTrace tailWord_276043 prefixEnd_276043 141742740309168714193007 := by
  unfold tailWord_276043
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068115338950830236152783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6712076892633886824101855 10068115338950830236152783)
  ·
    refine ⟨15102173008426245354229175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068115338950830236152783 15102173008426245354229175)
    ·
      refine ⟨22653259512639368031343763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15102173008426245354229175 22653259512639368031343763)
      ·
        refine ⟨33979889268959052047015645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22653259512639368031343763 33979889268959052047015645)
        ·
          refine ⟨12742458475859644517630867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33979889268959052047015645 12742458475859644517630867)
          ·
            refine ⟨19113687713789466776446301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12742458475859644517630867 19113687713789466776446301)
            ·
              refine ⟨7167632892671050041167363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19113687713789466776446301 7167632892671050041167363)
              ·
                refine ⟨10751449339006575061751045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167632892671050041167363 10751449339006575061751045)
                ·
                  refine ⟨2015896751063732824078321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10751449339006575061751045 2015896751063732824078321)
                  ·
                    refine ⟨1511922563297799618058741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015896751063732824078321 1511922563297799618058741)
                    ·
                      refine ⟨141742740309168714193007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1511922563297799618058741 141742740309168714193007)
                      ·
                        rfl

theorem cell23_276043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_276043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276043 prefixEnd_276043 := by exact prefixLift 276043
  have htrace : WordTrace (prefixWord ++ tailWord_276043) baseStart_276043 baseEnd_276043 := by
    simpa [prefixWord, tailWord_276043, baseEnd_276043] using wordTrace_append hprefix tailTrace_276043
  have hstable : (prefixWord ++ tailWord_276043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276043).length < 2 ^ (prefixWord ++ tailWord_276043).sum := by decide
  have hdescent : baseEnd_276043 < baseStart_276043 := by decide
  rcases family_descends (prefixWord ++ tailWord_276043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276047 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 3]
def baseStart_276047 : Nat := 118140960795 + 276047 * 2 ^ 59
def prefixEnd_276047 : Nat := 4983230072969 + 3 ^ 40 * 276047 * 2
def baseEnd_276047 : Nat := 141744794231786698542989

theorem tailTrace_276047 : CollatzResearch.WordTrace tailWord_276047 prefixEnd_276047 141744794231786698542989 := by
  unfold tailWord_276047
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068261230936338919298395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6712174153957559279532263 10068261230936338919298395)
  ·
    refine ⟨15102391846404508378947593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10068261230936338919298395 15102391846404508378947593)
    ·
      refine ⟨11326793884803381284210695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15102391846404508378947593 11326793884803381284210695)
      ·
        refine ⟨16990190827205071926316043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11326793884803381284210695 16990190827205071926316043)
        ·
          refine ⟨25485286240807607889474065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16990190827205071926316043 25485286240807607889474065)
          ·
            refine ⟨19113964680605705917105549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25485286240807607889474065 19113964680605705917105549)
            ·
              refine ⟨7167736755227139718914581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19113964680605705917105549 7167736755227139718914581)
              ·
                refine ⟨335987660401272174324121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7167736755227139718914581 335987660401272174324121)
                ·
                  refine ⟨251990745300954130743091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335987660401272174324121 251990745300954130743091)
                  ·
                    refine ⟨377986117951431196114637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251990745300954130743091 377986117951431196114637)
                    ·
                      refine ⟨141744794231786698542989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 377986117951431196114637 141744794231786698542989)
                      ·
                        rfl

theorem cell23_276047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_276047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276047 prefixEnd_276047 := by exact prefixLift 276047
  have htrace : WordTrace (prefixWord ++ tailWord_276047) baseStart_276047 baseEnd_276047 := by
    simpa [prefixWord, tailWord_276047, baseEnd_276047] using wordTrace_append hprefix tailTrace_276047
  have hstable : (prefixWord ++ tailWord_276047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276047).length < 2 ^ (prefixWord ++ tailWord_276047).sum := by decide
  have hdescent : baseEnd_276047 < baseStart_276047 := by decide
  rcases family_descends (prefixWord ++ tailWord_276047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276074 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_276074 : Nat := 118140960795 + 276074 * 2 ^ 59
def prefixEnd_276074 : Nat := 4983230072969 + 3 ^ 40 * 276074 * 2
def baseEnd_276074 : Nat := 141758658209458092905365

theorem tailTrace_276074 : CollatzResearch.WordTrace tailWord_276074 prefixEnd_276074 141758658209458092905365 := by
  unfold tailWord_276074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517311500459630632632819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6712830667892348353687517 2517311500459630632632819)
  ·
    refine ⟨3775967250689445948949229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517311500459630632632819 3775967250689445948949229)
    ·
      refine ⟨1415987719008542230855961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3775967250689445948949229 1415987719008542230855961)
      ·
        refine ⟨1061990789256406673141971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1415987719008542230855961 1061990789256406673141971)
        ·
          refine ⟨1592986183884610009712957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061990789256406673141971 1592986183884610009712957)
          ·
            refine ⟨597369818956728753642359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1592986183884610009712957 597369818956728753642359)
            ·
              refine ⟨896054728435093130463539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597369818956728753642359 896054728435093130463539)
              ·
                refine ⟨1344082092652639695695309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896054728435093130463539 1344082092652639695695309)
                ·
                  refine ⟨504030784744739885885741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1344082092652639695695309 504030784744739885885741)
                  ·
                    refine ⟨189011544279277457207153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504030784744739885885741 189011544279277457207153)
                    ·
                      refine ⟨141758658209458092905365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189011544279277457207153 141758658209458092905365)
                      ·
                        rfl

theorem cell23_276074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_276074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276074 prefixEnd_276074 := by exact prefixLift 276074
  have htrace : WordTrace (prefixWord ++ tailWord_276074) baseStart_276074 baseEnd_276074 := by
    simpa [prefixWord, tailWord_276074, baseEnd_276074] using wordTrace_append hprefix tailTrace_276074
  have hstable : (prefixWord ++ tailWord_276074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276074).length < 2 ^ (prefixWord ++ tailWord_276074).sum := by decide
  have hdescent : baseEnd_276074 < baseStart_276074 := by decide
  rcases family_descends (prefixWord ++ tailWord_276074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276083 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_276083 : Nat := 118140960795 + 276083 * 2 ^ 59
def prefixEnd_276083 : Nat := 4983230072969 + 3 ^ 40 * 276083 * 2
def baseEnd_276083 : Nat := 141763279535348557692823

theorem tailTrace_276083 : CollatzResearch.WordTrace tailWord_276083 prefixEnd_276083 141763279535348557692823 := by
  unfold tailWord_276083
  simp only [CollatzResearch.WordTrace]
  refine ⟨10069574258805917067608903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6713049505870611378405935 10069574258805917067608903)
  ·
    refine ⟨15104361388208875601413355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10069574258805917067608903 15104361388208875601413355)
    ·
      refine ⟨22656542082313313402120033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15104361388208875601413355 22656542082313313402120033)
      ·
        refine ⟨16992406561734985051590025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22656542082313313402120033 16992406561734985051590025)
        ·
          refine ⟨12744304921301238788692519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16992406561734985051590025 12744304921301238788692519)
          ·
            refine ⟨19116457381951858183038779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12744304921301238788692519 19116457381951858183038779)
            ·
              refine ⟨28674686072927787274558169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19116457381951858183038779 28674686072927787274558169)
              ·
                refine ⟨21506014554695840455918627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28674686072927787274558169 21506014554695840455918627)
                ·
                  refine ⟨32259021832043760683877941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21506014554695840455918627 32259021832043760683877941)
                  ·
                    refine ⟨3024283296754102564113557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32259021832043760683877941 3024283296754102564113557)
                    ·
                      refine ⟨141763279535348557692823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3024283296754102564113557 141763279535348557692823)
                      ·
                        rfl

theorem cell23_276083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_276083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276083 prefixEnd_276083 := by exact prefixLift 276083
  have htrace : WordTrace (prefixWord ++ tailWord_276083) baseStart_276083 baseEnd_276083 := by
    simpa [prefixWord, tailWord_276083, baseEnd_276083] using wordTrace_append hprefix tailTrace_276083
  have hstable : (prefixWord ++ tailWord_276083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276083).length < 2 ^ (prefixWord ++ tailWord_276083).sum := by decide
  have hdescent : baseEnd_276083 < baseStart_276083 := by decide
  rcases family_descends (prefixWord ++ tailWord_276083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276142 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_276142 : Nat := 118140960795 + 276142 * 2 ^ 59
def prefixEnd_276142 : Nat := 4983230072969 + 3 ^ 40 * 276142 * 2
def baseEnd_276142 : Nat := 141793574893963826855053

theorem tailTrace_276142 : CollatzResearch.WordTrace tailWord_276142 prefixEnd_276142 141793574893963826855053 := by
  unfold tailWord_276142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258965770699021268000835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6714484110394780096004453 1258965770699021268000835)
  ·
    refine ⟨1888448656048531902001253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258965770699021268000835 1888448656048531902001253)
    ·
      refine ⟨354084123009099731625235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1888448656048531902001253 354084123009099731625235)
      ·
        refine ⟨531126184513649597437853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354084123009099731625235 531126184513649597437853)
        ·
          refine ⟨199172319192618599039195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531126184513649597437853 199172319192618599039195)
          ·
            refine ⟨298758478788927898558793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199172319192618599039195 298758478788927898558793)
            ·
              refine ⟨224068859091695923919095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298758478788927898558793 224068859091695923919095)
              ·
                refine ⟨336103288637543885878643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224068859091695923919095 336103288637543885878643)
                ·
                  refine ⟨504154932956315828817965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336103288637543885878643 504154932956315828817965)
                  ·
                    refine ⟨189058099858618435806737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504154932956315828817965 189058099858618435806737)
                    ·
                      refine ⟨141793574893963826855053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189058099858618435806737 141793574893963826855053)
                      ·
                        rfl

theorem cell23_276142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_276142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276142 prefixEnd_276142 := by exact prefixLift 276142
  have htrace : WordTrace (prefixWord ++ tailWord_276142) baseStart_276142 baseEnd_276142 := by
    simpa [prefixWord, tailWord_276142, baseEnd_276142] using wordTrace_append hprefix tailTrace_276142
  have hstable : (prefixWord ++ tailWord_276142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276142).length < 2 ^ (prefixWord ++ tailWord_276142).sum := by decide
  have hdescent : baseEnd_276142 < baseStart_276142 := by decide
  rcases family_descends (prefixWord ++ tailWord_276142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276197 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_276197 : Nat := 118140960795 + 276197 * 2 ^ 59
def prefixEnd_276197 : Nat := 4983230072969 + 3 ^ 40 * 276197 * 2
def baseEnd_276197 : Nat := 141821816329961111667299

theorem tailTrace_276197 : CollatzResearch.WordTrace tailWord_276197 prefixEnd_276197 141821816329961111667299 := by
  unfold tailWord_276197
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073732180392914537258845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6715821453595276358172563 10073732180392914537258845)
  ·
    refine ⟨3777649567647342951472067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10073732180392914537258845 3777649567647342951472067)
    ·
      refine ⟨5666474351471014427208101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3777649567647342951472067 5666474351471014427208101)
      ·
        refine ⟨1062463940900815205101519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5666474351471014427208101 1062463940900815205101519)
        ·
          refine ⟨1593695911351222807652279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062463940900815205101519 1593695911351222807652279)
          ·
            refine ⟨2390543867026834211478419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593695911351222807652279 2390543867026834211478419)
            ·
              refine ⟨3585815800540251317217629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2390543867026834211478419 3585815800540251317217629)
              ·
                refine ⟨1344680925202594243956611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3585815800540251317217629 1344680925202594243956611)
                ·
                  refine ⟨2017021387803891365934917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344680925202594243956611 2017021387803891365934917)
                  ·
                    refine ⟨378191510213229631112797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2017021387803891365934917 378191510213229631112797)
                    ·
                      refine ⟨141821816329961111667299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 378191510213229631112797 141821816329961111667299)
                      ·
                        rfl

theorem cell23_276197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_276197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276197 prefixEnd_276197 := by exact prefixLift 276197
  have htrace : WordTrace (prefixWord ++ tailWord_276197) baseStart_276197 baseEnd_276197 := by
    simpa [prefixWord, tailWord_276197, baseEnd_276197] using wordTrace_append hprefix tailTrace_276197
  have hstable : (prefixWord ++ tailWord_276197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276197).length < 2 ^ (prefixWord ++ tailWord_276197).sum := by decide
  have hdescent : baseEnd_276197 < baseStart_276197 := by decide
  rcases family_descends (prefixWord ++ tailWord_276197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276214 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_276214 : Nat := 118140960795 + 276214 * 2 ^ 59
def prefixEnd_276214 : Nat := 4983230072969 + 3 ^ 40 * 276214 * 2
def baseEnd_276214 : Nat := 141830545501087545154721

theorem tailTrace_276214 : CollatzResearch.WordTrace tailWord_276214 prefixEnd_276214 141830545501087545154721 := by
  unfold tailWord_276214
  simp only [CollatzResearch.WordTrace]
  refine ⟨629647013833207902539231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6716234814220884293751797 629647013833207902539231)
  ·
    refine ⟨944470520749811853808847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 629647013833207902539231 944470520749811853808847)
    ·
      refine ⟨1416705781124717780713271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944470520749811853808847 1416705781124717780713271)
      ·
        refine ⟨2125058671687076671069907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416705781124717780713271 2125058671687076671069907)
        ·
          refine ⟨3187588007530615006604861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125058671687076671069907 3187588007530615006604861)
          ·
            refine ⟨1195345502823980627476823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3187588007530615006604861 1195345502823980627476823)
            ·
              refine ⟨1793018254235970941215235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195345502823980627476823 1793018254235970941215235)
              ·
                refine ⟨2689527381353956411822853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793018254235970941215235 2689527381353956411822853)
                ·
                  refine ⟨504286384003866827216785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2689527381353956411822853 504286384003866827216785)
                  ·
                    refine ⟨378214788002900120412589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504286384003866827216785 378214788002900120412589)
                    ·
                      refine ⟨141830545501087545154721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 378214788002900120412589 141830545501087545154721)
                      ·
                        rfl

theorem cell23_276214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_276214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276214 prefixEnd_276214 := by exact prefixLift 276214
  have htrace : WordTrace (prefixWord ++ tailWord_276214) baseStart_276214 baseEnd_276214 := by
    simpa [prefixWord, tailWord_276214, baseEnd_276214] using wordTrace_append hprefix tailTrace_276214
  have hstable : (prefixWord ++ tailWord_276214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276214).length < 2 ^ (prefixWord ++ tailWord_276214).sum := by decide
  have hdescent : baseEnd_276214 < baseStart_276214 := by decide
  rcases family_descends (prefixWord ++ tailWord_276214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276234 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_276234 : Nat := 118140960795 + 276234 * 2 ^ 59
def prefixEnd_276234 : Nat := 4983230072969 + 3 ^ 40 * 276234 * 2
def baseEnd_276234 : Nat := 15760090568241940767181

theorem tailTrace_276234 : CollatzResearch.WordTrace tailWord_276234 prefixEnd_276234 15760090568241940767181 := by
  unfold tailWord_276234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518770420314717464088939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6716721120839246570903837 2518770420314717464088939)
  ·
    refine ⟨3778155630472076196133409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518770420314717464088939 3778155630472076196133409)
    ·
      refine ⟨2833616722854057147100057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3778155630472076196133409 2833616722854057147100057)
      ·
        refine ⟨2125212542140542860325043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2833616722854057147100057 2125212542140542860325043)
        ·
          refine ⟨3187818813210814290487565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125212542140542860325043 3187818813210814290487565)
          ·
            refine ⟨1195432054954055358932837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3187818813210814290487565 1195432054954055358932837)
            ·
              refine ⟨224143510303885379799907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1195432054954055358932837 224143510303885379799907)
              ·
                refine ⟨336215265455828069699861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224143510303885379799907 336215265455828069699861)
                ·
                  refine ⟨15760090568241940767181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 336215265455828069699861 15760090568241940767181)
                  ·
                    rfl

theorem cell23_276234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_276234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276234 prefixEnd_276234 := by exact prefixLift 276234
  have htrace : WordTrace (prefixWord ++ tailWord_276234) baseStart_276234 baseEnd_276234 := by
    simpa [prefixWord, tailWord_276234, baseEnd_276234] using wordTrace_append hprefix tailTrace_276234
  have hstable : (prefixWord ++ tailWord_276234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276234).length < 2 ^ (prefixWord ++ tailWord_276234).sum := by decide
  have hdescent : baseEnd_276234 < baseStart_276234 := by decide
  rcases family_descends (prefixWord ++ tailWord_276234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276301 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_276301 : Nat := 118140960795 + 276301 * 2 ^ 59
def prefixEnd_276301 : Nat := 4983230072969 + 3 ^ 40 * 276301 * 2
def baseEnd_276301 : Nat := 141875218318028704766821

theorem tailTrace_276301 : CollatzResearch.WordTrace tailWord_276301 prefixEnd_276301 141875218318028704766821 := by
  unfold tailWord_276301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10077525372016140299044757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6718350248010760199363171 10077525372016140299044757)
  ·
    refine ⟨472384001813256576517723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10077525372016140299044757 472384001813256576517723)
    ·
      refine ⟨708576002719884864776585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472384001813256576517723 708576002719884864776585)
      ·
        refine ⟨531432002039913648582439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708576002719884864776585 531432002039913648582439)
        ·
          refine ⟨797148003059870472873659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531432002039913648582439 797148003059870472873659)
          ·
            refine ⟨1195722004589805709310489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797148003059870472873659 1195722004589805709310489)
            ·
              refine ⟨896791503442354281982867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195722004589805709310489 896791503442354281982867)
              ·
                refine ⟨1345187255163531422974301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896791503442354281982867 1345187255163531422974301)
                ·
                  refine ⟨504445220686324283615363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1345187255163531422974301 504445220686324283615363)
                  ·
                    refine ⟨756667831029486425423045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504445220686324283615363 756667831029486425423045)
                    ·
                      refine ⟨141875218318028704766821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 756667831029486425423045 141875218318028704766821)
                      ·
                        rfl

theorem cell23_276301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_276301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276301 prefixEnd_276301 := by exact prefixLift 276301
  have htrace : WordTrace (prefixWord ++ tailWord_276301) baseStart_276301 baseEnd_276301 := by
    simpa [prefixWord, tailWord_276301, baseEnd_276301] using wordTrace_append hprefix tailTrace_276301
  have hstable : (prefixWord ++ tailWord_276301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276301).length < 2 ^ (prefixWord ++ tailWord_276301).sum := by decide
  have hdescent : baseEnd_276301 < baseStart_276301 := by decide
  rcases family_descends (prefixWord ++ tailWord_276301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276304 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_276304 : Nat := 118140960795 + 276304 * 2 ^ 59
def prefixEnd_276304 : Nat := 4983230072969 + 3 ^ 40 * 276304 * 2
def baseEnd_276304 : Nat := 141876758759992193029307

theorem tailTrace_276304 : CollatzResearch.WordTrace tailWord_276304 prefixEnd_276304 141876758759992193029307 := by
  unfold tailWord_276304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038817395502635905701983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6718423194003514540935977 5038817395502635905701983)
  ·
    refine ⟨7558226093253953858552975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5038817395502635905701983 7558226093253953858552975)
    ·
      refine ⟨11337339139880930787829463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7558226093253953858552975 11337339139880930787829463)
      ·
        refine ⟨17006008709821396181744195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11337339139880930787829463 17006008709821396181744195)
        ·
          refine ⟨25509013064732094272616293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17006008709821396181744195 25509013064732094272616293)
          ·
            refine ⟨4782939949637267676115555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25509013064732094272616293 4782939949637267676115555)
            ·
              refine ⟨7174409924455901514173333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4782939949637267676115555 7174409924455901514173333)
              ·
                refine ⟨336300465208870383476875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7174409924455901514173333 336300465208870383476875)
                ·
                  refine ⟨504450697813305575215313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336300465208870383476875 504450697813305575215313)
                  ·
                    refine ⟨378338023359979181411485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 504450697813305575215313 378338023359979181411485)
                    ·
                      refine ⟨141876758759992193029307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 378338023359979181411485 141876758759992193029307)
                      ·
                        rfl

theorem cell23_276304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_276304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276304 prefixEnd_276304 := by exact prefixLift 276304
  have htrace : WordTrace (prefixWord ++ tailWord_276304) baseStart_276304 baseEnd_276304 := by
    simpa [prefixWord, tailWord_276304, baseEnd_276304] using wordTrace_append hprefix tailTrace_276304
  have hstable : (prefixWord ++ tailWord_276304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276304).length < 2 ^ (prefixWord ++ tailWord_276304).sum := by decide
  have hdescent : baseEnd_276304 < baseStart_276304 := by decide
  rcases family_descends (prefixWord ++ tailWord_276304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276377 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_276377 : Nat := 118140960795 + 276377 * 2 ^ 59
def prefixEnd_276377 : Nat := 4983230072969 + 3 ^ 40 * 276377 * 2
def baseEnd_276377 : Nat := 141914242847770407416471

theorem tailTrace_276377 : CollatzResearch.WordTrace tailWord_276377 prefixEnd_276377 141914242847770407416471 := by
  unfold tailWord_276377
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080297319740805278811385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6720198213160536852540923 10080297319740805278811385)
  ·
    refine ⟨7560222989805603959108539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10080297319740805278811385 7560222989805603959108539)
    ·
      refine ⟨11340334484708405938662809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7560222989805603959108539 11340334484708405938662809)
      ·
        refine ⟨8505250863531304453997107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11340334484708405938662809 8505250863531304453997107)
        ·
          refine ⟨12757876295296956680995661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505250863531304453997107 12757876295296956680995661)
          ·
            refine ⟨4784203610736358755373373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12757876295296956680995661 4784203610736358755373373)
            ·
              refine ⟨1794076354026134533265015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4784203610736358755373373 1794076354026134533265015)
              ·
                refine ⟨2691114531039201799897523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794076354026134533265015 2691114531039201799897523)
                ·
                  refine ⟨4036671796558802699846285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691114531039201799897523 4036671796558802699846285)
                  ·
                    refine ⟨1513751923709551012442357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4036671796558802699846285 1513751923709551012442357)
                    ·
                      refine ⟨141914242847770407416471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1513751923709551012442357 141914242847770407416471)
                      ·
                        rfl

theorem cell23_276377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_276377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276377 prefixEnd_276377 := by exact prefixLift 276377
  have htrace : WordTrace (prefixWord ++ tailWord_276377) baseStart_276377 baseEnd_276377 := by
    simpa [prefixWord, tailWord_276377, baseEnd_276377] using wordTrace_append hprefix tailTrace_276377
  have hstable : (prefixWord ++ tailWord_276377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276377).length < 2 ^ (prefixWord ++ tailWord_276377).sum := by decide
  have hdescent : baseEnd_276377 < baseStart_276377 := by decide
  rcases family_descends (prefixWord ++ tailWord_276377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276378 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_276378 : Nat := 118140960795 + 276378 * 2 ^ 59
def prefixEnd_276378 : Nat := 4983230072969 + 3 ^ 40 * 276378 * 2
def baseEnd_276378 : Nat := 141914756328424903503967

theorem tailTrace_276378 : CollatzResearch.WordTrace tailWord_276378 prefixEnd_276378 141914756328424903503967 := by
  unfold tailWord_276378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520083448184295612399447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6720222528491454966398525 2520083448184295612399447)
  ·
    refine ⟨3780125172276443418599171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520083448184295612399447 3780125172276443418599171)
    ·
      refine ⟨5670187758414665127898757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3780125172276443418599171 5670187758414665127898757)
      ·
        refine ⟨1063160204702749711481017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5670187758414665127898757 1063160204702749711481017)
        ·
          refine ⟨797370153527062283610763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063160204702749711481017 797370153527062283610763)
          ·
            refine ⟨1196055230290593425416145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797370153527062283610763 1196055230290593425416145)
            ·
              refine ⟨897041422717945069062109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196055230290593425416145 897041422717945069062109)
              ·
                refine ⟨336390533519229400898291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897041422717945069062109 336390533519229400898291)
                ·
                  refine ⟨504585800278844101347437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336390533519229400898291 504585800278844101347437)
                  ·
                    refine ⟨189219675104566538005289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504585800278844101347437 189219675104566538005289)
                    ·
                      refine ⟨141914756328424903503967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189219675104566538005289 141914756328424903503967)
                      ·
                        rfl

theorem cell23_276378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_276378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276378 prefixEnd_276378 := by exact prefixLift 276378
  have htrace : WordTrace (prefixWord ++ tailWord_276378) baseStart_276378 baseEnd_276378 := by
    simpa [prefixWord, tailWord_276378, baseEnd_276378] using wordTrace_append hprefix tailTrace_276378
  have hstable : (prefixWord ++ tailWord_276378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276378).length < 2 ^ (prefixWord ++ tailWord_276378).sum := by decide
  have hdescent : baseEnd_276378 < baseStart_276378 := by decide
  rcases family_descends (prefixWord ++ tailWord_276378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276408 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_276408 : Nat := 118140960795 + 276408 * 2 ^ 59
def prefixEnd_276408 : Nat := 4983230072969 + 3 ^ 40 * 276408 * 2
def baseEnd_276408 : Nat := 141930160748059786128829

theorem tailTrace_276408 : CollatzResearch.WordTrace tailWord_276408 prefixEnd_276408 141930160748059786128829 := by
  unfold tailWord_276408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040713991314248786594939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6720951988418998382126585 5040713991314248786594939)
  ·
    refine ⟨7561070986971373179892409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5040713991314248786594939 7561070986971373179892409)
    ·
      refine ⟨5670803240228529884919307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7561070986971373179892409 5670803240228529884919307)
      ·
        refine ⟨8506204860342794827378961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670803240228529884919307 8506204860342794827378961)
        ·
          refine ⟨6379653645257096120534221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8506204860342794827378961 6379653645257096120534221)
          ·
            refine ⟨2392370116971411045200333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6379653645257096120534221 2392370116971411045200333)
            ·
              refine ⟨897138793864279141950125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2392370116971411045200333 897138793864279141950125)
              ·
                refine ⟨336427047699104678231297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897138793864279141950125 336427047699104678231297)
                ·
                  refine ⟨252320285774328508673473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336427047699104678231297 252320285774328508673473)
                  ·
                    refine ⟨189240214330746381505105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 252320285774328508673473 189240214330746381505105)
                    ·
                      refine ⟨141930160748059786128829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189240214330746381505105 141930160748059786128829)
                      ·
                        rfl

theorem cell23_276408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_276408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276408 prefixEnd_276408 := by exact prefixLift 276408
  have htrace : WordTrace (prefixWord ++ tailWord_276408) baseStart_276408 baseEnd_276408 := by
    simpa [prefixWord, tailWord_276408, baseEnd_276408] using wordTrace_append hprefix tailTrace_276408
  have hstable : (prefixWord ++ tailWord_276408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276408).length < 2 ^ (prefixWord ++ tailWord_276408).sum := by decide
  have hdescent : baseEnd_276408 < baseStart_276408 := by decide
  rcases family_descends (prefixWord ++ tailWord_276408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276412 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_276412 : Nat := 118140960795 + 276412 * 2 ^ 59
def prefixEnd_276412 : Nat := 4983230072969 + 3 ^ 40 * 276412 * 2
def baseEnd_276412 : Nat := 141932214670677770478811

theorem tailTrace_276412 : CollatzResearch.WordTrace tailWord_276412 prefixEnd_276412 141932214670677770478811 := by
  unfold tailWord_276412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040786937307003128167745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6721049249742670837556993 5040786937307003128167745)
  ·
    refine ⟨3780590202980252346125809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5040786937307003128167745 3780590202980252346125809)
    ·
      refine ⟨2835442652235189259594357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3780590202980252346125809 2835442652235189259594357)
      ·
        refine ⟨265822748647048993086971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2835442652235189259594357 265822748647048993086971)
        ·
          refine ⟨398734122970573489630457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265822748647048993086971 398734122970573489630457)
          ·
            refine ⟨299050592227930117222843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398734122970573489630457 299050592227930117222843)
            ·
              refine ⟨448575888341895175834265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299050592227930117222843 448575888341895175834265)
              ·
                refine ⟨336431916256421381875699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448575888341895175834265 336431916256421381875699)
                ·
                  refine ⟨504647874384632072813549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336431916256421381875699 504647874384632072813549)
                  ·
                    refine ⟨189242952894237027305081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504647874384632072813549 189242952894237027305081)
                    ·
                      refine ⟨141932214670677770478811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189242952894237027305081 141932214670677770478811)
                      ·
                        rfl

theorem cell23_276412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_276412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276412 prefixEnd_276412 := by exact prefixLift 276412
  have htrace : WordTrace (prefixWord ++ tailWord_276412) baseStart_276412 baseEnd_276412 := by
    simpa [prefixWord, tailWord_276412, baseEnd_276412] using wordTrace_append hprefix tailTrace_276412
  have hstable : (prefixWord ++ tailWord_276412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276412).length < 2 ^ (prefixWord ++ tailWord_276412).sum := by decide
  have hdescent : baseEnd_276412 < baseStart_276412 := by decide
  rcases family_descends (prefixWord ++ tailWord_276412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276451 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 5, 2]
def baseStart_276451 : Nat := 118140960795 + 276451 * 2 ^ 59
def prefixEnd_276451 : Nat := 4983230072969 + 3 ^ 40 * 276451 * 2
def baseEnd_276451 : Nat := 141952240416203117891131

theorem tailTrace_276451 : CollatzResearch.WordTrace tailWord_276451 prefixEnd_276451 141952240416203117891131 := by
  unfold tailWord_276451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10082996321472715917005207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6721997547648477278003471 10082996321472715917005207)
  ·
    refine ⟨15124494482209073875507811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10082996321472715917005207 15124494482209073875507811)
    ·
      refine ⟨22686741723313610813261717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15124494482209073875507811 22686741723313610813261717)
      ·
        refine ⟨1063441018280325506871643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22686741723313610813261717 1063441018280325506871643)
        ·
          refine ⟨1595161527420488260307465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063441018280325506871643 1595161527420488260307465)
          ·
            refine ⟨1196371145565366195230599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595161527420488260307465 1196371145565366195230599)
            ·
              refine ⟨1794556718348049292845899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196371145565366195230599 1794556718348049292845899)
              ·
                refine ⟨2691835077522073939268849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794556718348049292845899 2691835077522073939268849)
                ·
                  refine ⟨2018876308141555454451637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691835077522073939268849 2018876308141555454451637)
                  ·
                    refine ⟨189269653888270823854841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2018876308141555454451637 189269653888270823854841)
                    ·
                      refine ⟨141952240416203117891131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189269653888270823854841 141952240416203117891131)
                      ·
                        rfl

theorem cell23_276451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_276451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276451 prefixEnd_276451 := by exact prefixLift 276451
  have htrace : WordTrace (prefixWord ++ tailWord_276451) baseStart_276451 baseEnd_276451 := by
    simpa [prefixWord, tailWord_276451, baseEnd_276451] using wordTrace_append hprefix tailTrace_276451
  have hstable : (prefixWord ++ tailWord_276451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276451).length < 2 ^ (prefixWord ++ tailWord_276451).sum := by decide
  have hdescent : baseEnd_276451 < baseStart_276451 := by decide
  rcases family_descends (prefixWord ++ tailWord_276451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276464 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_276464 : Nat := 118140960795 + 276464 * 2 ^ 59
def prefixEnd_276464 : Nat := 4983230072969 + 3 ^ 40 * 276464 * 2
def baseEnd_276464 : Nat := 141958915664711567028571

theorem tailTrace_276464 : CollatzResearch.WordTrace tailWord_276464 prefixEnd_276464 141958915664711567028571 := by
  unfold tailWord_276464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041735235212809568614223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6722313646950412758152297 5041735235212809568614223)
  ·
    refine ⟨7562602852819214352921335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5041735235212809568614223 7562602852819214352921335)
    ·
      refine ⟨11343904279228821529382003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7562602852819214352921335 11343904279228821529382003)
      ·
        refine ⟨17015856418843232294073005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11343904279228821529382003 17015856418843232294073005)
        ·
          refine ⟨6380946157066212110277377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17015856418843232294073005 6380946157066212110277377)
          ·
            refine ⟨4785709617799659082708033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6380946157066212110277377 4785709617799659082708033)
            ·
              refine ⟨3589282213349744312031025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785709617799659082708033 3589282213349744312031025)
              ·
                refine ⟨2691961660012308234023269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589282213349744312031025 2691961660012308234023269)
                ·
                  refine ⟨504742811252307793879363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2691961660012308234023269 504742811252307793879363)
                  ·
                    refine ⟨757114216878461690819045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504742811252307793879363 757114216878461690819045)
                    ·
                      refine ⟨141958915664711567028571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 757114216878461690819045 141958915664711567028571)
                      ·
                        rfl

theorem cell23_276464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_276464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276464 prefixEnd_276464 := by exact prefixLift 276464
  have htrace : WordTrace (prefixWord ++ tailWord_276464) baseStart_276464 baseEnd_276464 := by
    simpa [prefixWord, tailWord_276464, baseEnd_276464] using wordTrace_append hprefix tailTrace_276464
  have hstable : (prefixWord ++ tailWord_276464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276464).length < 2 ^ (prefixWord ++ tailWord_276464).sum := by decide
  have hdescent : baseEnd_276464 < baseStart_276464 := by decide
  rcases family_descends (prefixWord ++ tailWord_276464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276478 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_276478 : Nat := 118140960795 + 276478 * 2 ^ 59
def prefixEnd_276478 : Nat := 4983230072969 + 3 ^ 40 * 276478 * 2
def baseEnd_276478 : Nat := 47322034797958170751169

theorem tailTrace_276478 : CollatzResearch.WordTrace tailWord_276478 prefixEnd_276478 47322034797958170751169 := by
  unfold tailWord_276478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260497636546862441029761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6722654061583266352158725 1260497636546862441029761)
  ·
    refine ⟨945373227410146830772321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1260497636546862441029761 945373227410146830772321)
    ·
      refine ⟨709029920557610123079241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945373227410146830772321 709029920557610123079241)
      ·
        refine ⟨531772440418207592309431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 709029920557610123079241 531772440418207592309431)
        ·
          refine ⟨797658660627311388464147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531772440418207592309431 797658660627311388464147)
          ·
            refine ⟨1196487990940967082696221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797658660627311388464147 1196487990940967082696221)
            ·
              refine ⟨448682996602862656011083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1196487990940967082696221 448682996602862656011083)
              ·
                refine ⟨673024494904293984016625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448682996602862656011083 673024494904293984016625)
                ·
                  refine ⟨504768371178220488012469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673024494904293984016625 504768371178220488012469)
                  ·
                    refine ⟨47322034797958170751169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 504768371178220488012469 47322034797958170751169)
                    ·
                      rfl

theorem cell23_276478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_276478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276478 prefixEnd_276478 := by exact prefixLift 276478
  have htrace : WordTrace (prefixWord ++ tailWord_276478) baseStart_276478 baseEnd_276478 := by
    simpa [prefixWord, tailWord_276478, baseEnd_276478] using wordTrace_append hprefix tailTrace_276478
  have hstable : (prefixWord ++ tailWord_276478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276478).length < 2 ^ (prefixWord ++ tailWord_276478).sum := by decide
  have hdescent : baseEnd_276478 < baseStart_276478 := by decide
  rcases family_descends (prefixWord ++ tailWord_276478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276481 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_276481 : Nat := 118140960795 + 276481 * 2 ^ 59
def prefixEnd_276481 : Nat := 4983230072969 + 3 ^ 40 * 276481 * 2
def baseEnd_276481 : Nat := 141967644835838000515993

theorem tailTrace_276481 : CollatzResearch.WordTrace tailWord_276481 prefixEnd_276481 141967644835838000515993 := by
  unfold tailWord_276481
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084090511364031040597297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6722727007576020693731531 10084090511364031040597297)
  ·
    refine ⟨7563067883523023280447973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10084090511364031040597297 7563067883523023280447973)
    ·
      refine ⟨1418075228160566865083995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7563067883523023280447973 1418075228160566865083995)
      ·
        refine ⟨2127112842240850297625993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418075228160566865083995 2127112842240850297625993)
        ·
          refine ⟨1595334631680637723219495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127112842240850297625993 1595334631680637723219495)
          ·
            refine ⟨2393001947520956584829243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595334631680637723219495 2393001947520956584829243)
            ·
              refine ⟨3589502921281434877243865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393001947520956584829243 3589502921281434877243865)
              ·
                refine ⟨2692127190961076157932899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589502921281434877243865 2692127190961076157932899)
                ·
                  refine ⟨4038190786441614236899349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692127190961076157932899 4038190786441614236899349)
                  ·
                    refine ⟨189290193114450667354657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4038190786441614236899349 189290193114450667354657)
                    ·
                      refine ⟨141967644835838000515993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189290193114450667354657 141967644835838000515993)
                      ·
                        rfl

theorem cell23_276481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_276481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276481 prefixEnd_276481 := by exact prefixLift 276481
  have htrace : WordTrace (prefixWord ++ tailWord_276481) baseStart_276481 baseEnd_276481 := by
    simpa [prefixWord, tailWord_276481, baseEnd_276481] using wordTrace_append hprefix tailTrace_276481
  have hstable : (prefixWord ++ tailWord_276481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276481).length < 2 ^ (prefixWord ++ tailWord_276481).sum := by decide
  have hdescent : baseEnd_276481 < baseStart_276481 := by decide
  rcases family_descends (prefixWord ++ tailWord_276481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276493 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_276493 : Nat := 118140960795 + 276493 * 2 ^ 59
def prefixEnd_276493 : Nat := 4983230072969 + 3 ^ 40 * 276493 * 2
def baseEnd_276493 : Nat := 141973806603691953565939

theorem tailTrace_276493 : CollatzResearch.WordTrace tailWord_276493 prefixEnd_276493 141973806603691953565939 := by
  unfold tailWord_276493
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084528187320557090034133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6723018791547038060022755 10084528187320557090034133)
  ·
    refine ⟨236356129390325556797675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10084528187320557090034133 236356129390325556797675)
    ·
      refine ⟨354534194085488335196513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236356129390325556797675 354534194085488335196513)
      ·
        refine ⟨265900645564116251397385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354534194085488335196513 265900645564116251397385)
        ·
          refine ⟨199425484173087188548039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265900645564116251397385 199425484173087188548039)
          ·
            refine ⟨299138226259630782822059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199425484173087188548039 299138226259630782822059)
            ·
              refine ⟨448707339389446174233089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299138226259630782822059 448707339389446174233089)
              ·
                refine ⟨336530504542084630674817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448707339389446174233089 336530504542084630674817)
                ·
                  refine ⟨252397878406563473006113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336530504542084630674817 252397878406563473006113)
                  ·
                    refine ⟨189298408804922604754585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 252397878406563473006113 189298408804922604754585)
                    ·
                      refine ⟨141973806603691953565939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189298408804922604754585 141973806603691953565939)
                      ·
                        rfl

theorem cell23_276493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_276493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276493 prefixEnd_276493 := by exact prefixLift 276493
  have htrace : WordTrace (prefixWord ++ tailWord_276493) baseStart_276493 baseEnd_276493 := by
    simpa [prefixWord, tailWord_276493, baseEnd_276493] using wordTrace_append hprefix tailTrace_276493
  have hstable : (prefixWord ++ tailWord_276493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276493).length < 2 ^ (prefixWord ++ tailWord_276493).sum := by decide
  have hdescent : baseEnd_276493 < baseStart_276493 := by decide
  rcases family_descends (prefixWord ++ tailWord_276493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276494 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_276494 : Nat := 118140960795 + 276494 * 2 ^ 59
def prefixEnd_276494 : Nat := 4983230072969 + 3 ^ 40 * 276494 * 2
def baseEnd_276494 : Nat := 141974320084346449653433

theorem tailTrace_276494 : CollatzResearch.WordTrace tailWord_276494 prefixEnd_276494 141974320084346449653433 := by
  unfold tailWord_276494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260570582539616782602567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6723043106877956173880357 1260570582539616782602567)
  ·
    refine ⟨1890855873809425173903851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260570582539616782602567 1890855873809425173903851)
    ·
      refine ⟨2836283810714137760855777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890855873809425173903851 2836283810714137760855777)
      ·
        refine ⟨2127212858035603320641833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836283810714137760855777 2127212858035603320641833)
        ·
          refine ⟨1595409643526702490481375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127212858035603320641833 1595409643526702490481375)
          ·
            refine ⟨2393114465290053735722063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595409643526702490481375 2393114465290053735722063)
            ·
              refine ⟨3589671697935080603583095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393114465290053735722063 3589671697935080603583095)
              ·
                refine ⟨5384507546902620905374643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589671697935080603583095 5384507546902620905374643)
                ·
                  refine ⟨8076761320353931358061965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5384507546902620905374643 8076761320353931358061965)
                  ·
                    refine ⟨3028785495132724259273237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8076761320353931358061965 3028785495132724259273237)
                    ·
                      refine ⟨141974320084346449653433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3028785495132724259273237 141974320084346449653433)
                      ·
                        rfl

theorem cell23_276494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_276494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276494 prefixEnd_276494 := by exact prefixLift 276494
  have htrace : WordTrace (prefixWord ++ tailWord_276494) baseStart_276494 baseEnd_276494 := by
    simpa [prefixWord, tailWord_276494, baseEnd_276494] using wordTrace_append hprefix tailTrace_276494
  have hstable : (prefixWord ++ tailWord_276494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276494).length < 2 ^ (prefixWord ++ tailWord_276494).sum := by decide
  have hdescent : baseEnd_276494 < baseStart_276494 := by decide
  rcases family_descends (prefixWord ++ tailWord_276494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276504 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 8]
def baseStart_276504 : Nat := 118140960795 + 276504 * 2 ^ 59
def prefixEnd_276504 : Nat := 4983230072969 + 3 ^ 40 * 276504 * 2
def baseEnd_276504 : Nat := 15775494987876823392043

theorem tailTrace_276504 : CollatzResearch.WordTrace tailWord_276504 prefixEnd_276504 15775494987876823392043 := by
  unfold tailWord_276504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042464695140352984342283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6723286260187137312456377 5042464695140352984342283)
  ·
    refine ⟨7563697042710529476513425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5042464695140352984342283 7563697042710529476513425)
    ·
      refine ⟨5672772782032897107385069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7563697042710529476513425 5672772782032897107385069)
      ·
        refine ⟨2127289793262336415269401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5672772782032897107385069 2127289793262336415269401)
        ·
          refine ⟨1595467344946752311452051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127289793262336415269401 1595467344946752311452051)
          ·
            refine ⟨2393201017420128467178077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595467344946752311452051 2393201017420128467178077)
            ·
              refine ⟨897450381532548175191779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2393201017420128467178077 897450381532548175191779)
              ·
                refine ⟨1346175572298822262787669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897450381532548175191779 1346175572298822262787669)
                ·
                  refine ⟨15775494987876823392043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1346175572298822262787669 15775494987876823392043)
                  ·
                    rfl

theorem cell23_276504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_276504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276504 prefixEnd_276504 := by exact prefixLift 276504
  have htrace : WordTrace (prefixWord ++ tailWord_276504) baseStart_276504 baseEnd_276504 := by
    simpa [prefixWord, tailWord_276504, baseEnd_276504] using wordTrace_append hprefix tailTrace_276504
  have hstable : (prefixWord ++ tailWord_276504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276504).length < 2 ^ (prefixWord ++ tailWord_276504).sum := by decide
  have hdescent : baseEnd_276504 < baseStart_276504 := by decide
  rcases family_descends (prefixWord ++ tailWord_276504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276508 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_276508 : Nat := 118140960795 + 276508 * 2 ^ 59
def prefixEnd_276508 : Nat := 4983230072969 + 3 ^ 40 * 276508 * 2
def baseEnd_276508 : Nat := 47327169604503131626123

theorem tailTrace_276508 : CollatzResearch.WordTrace tailWord_276508 prefixEnd_276508 47327169604503131626123 := by
  unfold tailWord_276508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042537641133107325915089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6723383521510809767886785 5042537641133107325915089)
  ·
    refine ⟨3781903230849830494436317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5042537641133107325915089 3781903230849830494436317)
    ·
      refine ⟨1418213711568686435413619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3781903230849830494436317 1418213711568686435413619)
      ·
        refine ⟨2127320567353029653120429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418213711568686435413619 2127320567353029653120429)
        ·
          refine ⟨797745212757386119920161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2127320567353029653120429 797745212757386119920161)
          ·
            refine ⟨598308909568039589940121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797745212757386119920161 598308909568039589940121)
            ·
              refine ⟨448731682176029692455091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598308909568039589940121 448731682176029692455091)
              ·
                refine ⟨673097523264044538682637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448731682176029692455091 673097523264044538682637)
                ·
                  refine ⟨252411571224016702005989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673097523264044538682637 252411571224016702005989)
                  ·
                    refine ⟨47327169604503131626123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 252411571224016702005989 47327169604503131626123)
                    ·
                      rfl

theorem cell23_276508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_276508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276508 prefixEnd_276508 := by exact prefixLift 276508
  have htrace : WordTrace (prefixWord ++ tailWord_276508) baseStart_276508 baseEnd_276508 := by
    simpa [prefixWord, tailWord_276508, baseEnd_276508] using wordTrace_append hprefix tailTrace_276508
  have hstable : (prefixWord ++ tailWord_276508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276508).length < 2 ^ (prefixWord ++ tailWord_276508).sum := by decide
  have hdescent : baseEnd_276508 < baseStart_276508 := by decide
  rcases family_descends (prefixWord ++ tailWord_276508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276551 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 1, 5]
def baseStart_276551 : Nat := 118140960795 + 276551 * 2 ^ 59
def prefixEnd_276551 : Nat := 4983230072969 + 3 ^ 40 * 276551 * 2
def baseEnd_276551 : Nat := 47334529493884242213557

theorem tailTrace_276551 : CollatzResearch.WordTrace tailWord_276551 prefixEnd_276551 47334529493884242213557 := by
  unfold tailWord_276551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086643621110432995645507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724429080740288663763671 10086643621110432995645507)
  ·
    refine ⟨15129965431665649493468261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086643621110432995645507 15129965431665649493468261)
    ·
      refine ⟨2836868518437309280025299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15129965431665649493468261 2836868518437309280025299)
      ·
        refine ⟨4255302777655963920037949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836868518437309280025299 4255302777655963920037949)
        ·
          refine ⟨1595738541620986470014231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4255302777655963920037949 1595738541620986470014231)
          ·
            refine ⟨2393607812431479705021347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595738541620986470014231 2393607812431479705021347)
            ·
              refine ⟨3590411718647219557532021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393607812431479705021347 3590411718647219557532021)
              ·
                refine ⟨336601098623176833518627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3590411718647219557532021 336601098623176833518627)
                ·
                  refine ⟨504901647934765250277941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336601098623176833518627 504901647934765250277941)
                  ·
                    refine ⟨47334529493884242213557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 504901647934765250277941 47334529493884242213557)
                    ·
                      rfl

theorem cell23_276551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_276551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276551 prefixEnd_276551 := by exact prefixLift 276551
  have htrace : WordTrace (prefixWord ++ tailWord_276551) baseStart_276551 baseEnd_276551 := by
    simpa [prefixWord, tailWord_276551, baseEnd_276551] using wordTrace_append hprefix tailTrace_276551
  have hstable : (prefixWord ++ tailWord_276551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276551).length < 2 ^ (prefixWord ++ tailWord_276551).sum := by decide
  have hdescent : baseEnd_276551 < baseStart_276551 := by decide
  rcases family_descends (prefixWord ++ tailWord_276551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276558 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_276558 : Nat := 118140960795 + 276558 * 2 ^ 59
def prefixEnd_276558 : Nat := 4983230072969 + 3 ^ 40 * 276558 * 2
def baseEnd_276558 : Nat := 142007182846234199253139

theorem tailTrace_276558 : CollatzResearch.WordTrace tailWord_276558 prefixEnd_276558 142007182846234199253139 := by
  unfold tailWord_276558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260862366510634148893791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6724599288056715460766885 1260862366510634148893791)
  ·
    refine ⟨1891293549765951223340687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260862366510634148893791 1891293549765951223340687)
    ·
      refine ⟨2836940324648926835011031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891293549765951223340687 2836940324648926835011031)
      ·
        refine ⟨4255410486973390252516547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836940324648926835011031 4255410486973390252516547)
        ·
          refine ⟨6383115730460085378774821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255410486973390252516547 6383115730460085378774821)
          ·
            refine ⟨1196834199461266008520279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6383115730460085378774821 1196834199461266008520279)
            ·
              refine ⟨1795251299191899012780419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196834199461266008520279 1795251299191899012780419)
              ·
                refine ⟨2692876948787848519170629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795251299191899012780419 2692876948787848519170629)
                ·
                  refine ⟨504914427897721597344493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2692876948787848519170629 504914427897721597344493)
                  ·
                    refine ⟨189342910461645599004185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504914427897721597344493 189342910461645599004185)
                    ·
                      refine ⟨142007182846234199253139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189342910461645599004185 142007182846234199253139)
                      ·
                        rfl

theorem cell23_276558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_276558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276558 prefixEnd_276558 := by exact prefixLift 276558
  have htrace : WordTrace (prefixWord ++ tailWord_276558) baseStart_276558 baseEnd_276558 := by
    simpa [prefixWord, tailWord_276558, baseEnd_276558] using wordTrace_append hprefix tailTrace_276558
  have hstable : (prefixWord ++ tailWord_276558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276558).length < 2 ^ (prefixWord ++ tailWord_276558).sum := by decide
  have hdescent : baseEnd_276558 < baseStart_276558 := by decide
  rcases family_descends (prefixWord ++ tailWord_276558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276565 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_276565 : Nat := 118140960795 + 276565 * 2 ^ 59
def prefixEnd_276565 : Nat := 4983230072969 + 3 ^ 40 * 276565 * 2
def baseEnd_276565 : Nat := 142010777210815671865607

theorem tailTrace_276565 : CollatzResearch.WordTrace tailWord_276565 prefixEnd_276565 142010777210815671865607 := by
  unfold tailWord_276565
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087154243059713386655149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6724769495373142257770099 10087154243059713386655149)
  ·
    refine ⟨3782682841147392519995681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10087154243059713386655149 3782682841147392519995681)
    ·
      refine ⟨2837012130860544389996761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3782682841147392519995681 2837012130860544389996761)
      ·
        refine ⟨2127759098145408292497571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2837012130860544389996761 2127759098145408292497571)
        ·
          refine ⟨3191638647218112438746357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127759098145408292497571 3191638647218112438746357)
          ·
            refine ⟨299216123176698041132471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3191638647218112438746357 299216123176698041132471)
            ·
              refine ⟨448824184765047061698707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299216123176698041132471 448824184765047061698707)
              ·
                refine ⟨673236277147570592548061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448824184765047061698707 673236277147570592548061)
                ·
                  refine ⟨252463603930338972205523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 673236277147570592548061 252463603930338972205523)
                  ·
                    refine ⟨378695405895508458308285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252463603930338972205523 378695405895508458308285)
                    ·
                      refine ⟨142010777210815671865607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 378695405895508458308285 142010777210815671865607)
                      ·
                        rfl

theorem cell23_276565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_276565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276565 prefixEnd_276565 := by exact prefixLift 276565
  have htrace : WordTrace (prefixWord ++ tailWord_276565) baseStart_276565 baseEnd_276565 := by
    simpa [prefixWord, tailWord_276565, baseEnd_276565] using wordTrace_append hprefix tailTrace_276565
  have hstable : (prefixWord ++ tailWord_276565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276565).length < 2 ^ (prefixWord ++ tailWord_276565).sum := by decide
  have hdescent : baseEnd_276565 < baseStart_276565 := by decide
  rcases family_descends (prefixWord ++ tailWord_276565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276588 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_276588 : Nat := 118140960795 + 276588 * 2 ^ 59
def prefixEnd_276588 : Nat := 4983230072969 + 3 ^ 40 * 276588 * 2
def baseEnd_276588 : Nat := 142022587265869081878001

theorem tailTrace_276588 : CollatzResearch.WordTrace tailWord_276588 prefixEnd_276588 142022587265869081878001 := by
  unfold tailWord_276588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043996560988194157371209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6725328747984258876494945 5043996560988194157371209)
  ·
    refine ⟨3782997420741145618028407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5043996560988194157371209 3782997420741145618028407)
    ·
      refine ⟨5674496131111718427042611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782997420741145618028407 5674496131111718427042611)
      ·
        refine ⟨8511744196667577640563917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5674496131111718427042611 8511744196667577640563917)
        ·
          refine ⟨3191904073750341615211469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8511744196667577640563917 3191904073750341615211469)
          ·
            refine ⟨1196964027656378105704301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3191904073750341615211469 1196964027656378105704301)
            ·
              refine ⟨448861510371141789639113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1196964027656378105704301 448861510371141789639113)
              ·
                refine ⟨336646132778356342229335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448861510371141789639113 336646132778356342229335)
                ·
                  refine ⟨504969199167534513344003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336646132778356342229335 504969199167534513344003)
                  ·
                    refine ⟨757453798751301770016005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 504969199167534513344003 757453798751301770016005)
                    ·
                      refine ⟨142022587265869081878001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 757453798751301770016005 142022587265869081878001)
                      ·
                        rfl

theorem cell23_276588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_276588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276588 prefixEnd_276588 := by exact prefixLift 276588
  have htrace : WordTrace (prefixWord ++ tailWord_276588) baseStart_276588 baseEnd_276588 := by
    simpa [prefixWord, tailWord_276588, baseEnd_276588] using wordTrace_append hprefix tailTrace_276588
  have hstable : (prefixWord ++ tailWord_276588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276588).length < 2 ^ (prefixWord ++ tailWord_276588).sum := by decide
  have hdescent : baseEnd_276588 < baseStart_276588 := by decide
  rcases family_descends (prefixWord ++ tailWord_276588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276598 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_276598 : Nat := 118140960795 + 276598 * 2 ^ 59
def prefixEnd_276598 : Nat := 4983230072969 + 3 ^ 40 * 276598 * 2
def baseEnd_276598 : Nat := 47342574024138014250985

theorem tailTrace_276598 : CollatzResearch.WordTrace tailWord_276598 prefixEnd_276598 47342574024138014250985 := by
  unfold tailWord_276598
  simp only [CollatzResearch.WordTrace]
  refine ⟨630522365746260001412903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6725571901293440015070965 630522365746260001412903)
  ·
    refine ⟨945783548619390002119355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630522365746260001412903 945783548619390002119355)
    ·
      refine ⟨1418675322929085003179033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945783548619390002119355 1418675322929085003179033)
      ·
        refine ⟨1064006492196813752384275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418675322929085003179033 1064006492196813752384275)
        ·
          refine ⟨1596009738295220628576413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064006492196813752384275 1596009738295220628576413)
          ·
            refine ⟨598503651860707735716155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1596009738295220628576413 598503651860707735716155)
            ·
              refine ⟨897755477791061603574233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598503651860707735716155 897755477791061603574233)
              ·
                refine ⟨673316608343296202680675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897755477791061603574233 673316608343296202680675)
                ·
                  refine ⟨1009974912514944304021013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673316608343296202680675 1009974912514944304021013)
                  ·
                    refine ⟨47342574024138014250985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1009974912514944304021013 47342574024138014250985)
                    ·
                      rfl

theorem cell23_276598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_276598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276598 prefixEnd_276598 := by exact prefixLift 276598
  have htrace : WordTrace (prefixWord ++ tailWord_276598) baseStart_276598 baseEnd_276598 := by
    simpa [prefixWord, tailWord_276598, baseEnd_276598] using wordTrace_append hprefix tailTrace_276598
  have hstable : (prefixWord ++ tailWord_276598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276598).length < 2 ^ (prefixWord ++ tailWord_276598).sum := by decide
  have hdescent : baseEnd_276598 < baseStart_276598 := by decide
  rcases family_descends (prefixWord ++ tailWord_276598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276601 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_276601 : Nat := 118140960795 + 276601 * 2 ^ 59
def prefixEnd_276601 : Nat := 4983230072969 + 3 ^ 40 * 276601 * 2
def baseEnd_276601 : Nat := 142029262514377531015441

theorem tailTrace_276601 : CollatzResearch.WordTrace tailWord_276601 prefixEnd_276601 142029262514377531015441 := by
  unfold tailWord_276601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10088467270929291534965657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6725644847286194356643771 10088467270929291534965657)
  ·
    refine ⟨7566350453196968651224243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10088467270929291534965657 7566350453196968651224243)
    ·
      refine ⟨11349525679795452976836365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7566350453196968651224243 11349525679795452976836365)
      ·
        refine ⟨4256072129923294866313637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11349525679795452976836365 4256072129923294866313637)
        ·
          refine ⟨798013524360617787433807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4256072129923294866313637 798013524360617787433807)
          ·
            refine ⟨1197020286540926681150711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798013524360617787433807 1197020286540926681150711)
            ·
              refine ⟨1795530429811390021726067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197020286540926681150711 1795530429811390021726067)
              ·
                refine ⟨2693295644717085032589101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795530429811390021726067 2693295644717085032589101)
                ·
                  refine ⟨1009985866768906887220913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2693295644717085032589101 1009985866768906887220913)
                  ·
                    refine ⟨757489400076680165415685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1009985866768906887220913 757489400076680165415685)
                    ·
                      refine ⟨142029262514377531015441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 757489400076680165415685 142029262514377531015441)
                      ·
                        rfl

theorem cell23_276601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_276601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276601 prefixEnd_276601 := by exact prefixLift 276601
  have htrace : WordTrace (prefixWord ++ tailWord_276601) baseStart_276601 baseEnd_276601 := by
    simpa [prefixWord, tailWord_276601, baseEnd_276601] using wordTrace_append hprefix tailTrace_276601
  have hstable : (prefixWord ++ tailWord_276601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276601).length < 2 ^ (prefixWord ++ tailWord_276601).sum := by decide
  have hdescent : baseEnd_276601 < baseStart_276601 := by decide
  rcases family_descends (prefixWord ++ tailWord_276601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276605 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_276605 : Nat := 118140960795 + 276605 * 2 ^ 59
def prefixEnd_276605 : Nat := 4983230072969 + 3 ^ 40 * 276605 * 2
def baseEnd_276605 : Nat := 142031316436995515365423

theorem tailTrace_276605 : CollatzResearch.WordTrace tailWord_276605 prefixEnd_276605 142031316436995515365423 := by
  unfold tailWord_276605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10088613162914800218111269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6725742108609866812074179 10088613162914800218111269)
  ·
    refine ⟨1891614968046525040895863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10088613162914800218111269 1891614968046525040895863)
    ·
      refine ⟨2837422452069787561343795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891614968046525040895863 2837422452069787561343795)
      ·
        refine ⟨4256133678104681342015693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837422452069787561343795 4256133678104681342015693)
        ·
          refine ⟨1596050129289255503255885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4256133678104681342015693 1596050129289255503255885)
          ·
            refine ⟨598518798483470813720957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1596050129289255503255885 598518798483470813720957)
            ·
              refine ⟨224444549431301555145359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 598518798483470813720957 224444549431301555145359)
              ·
                refine ⟨336666824146952332718039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224444549431301555145359 336666824146952332718039)
                ·
                  refine ⟨505000236220428499077059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336666824146952332718039 505000236220428499077059)
                  ·
                    refine ⟨757500354330642748615589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505000236220428499077059 757500354330642748615589)
                    ·
                      refine ⟨142031316436995515365423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 757500354330642748615589 142031316436995515365423)
                      ·
                        rfl

theorem cell23_276605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_276605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276605 prefixEnd_276605 := by exact prefixLift 276605
  have htrace : WordTrace (prefixWord ++ tailWord_276605) baseStart_276605 baseEnd_276605 := by
    simpa [prefixWord, tailWord_276605, baseEnd_276605] using wordTrace_append hprefix tailTrace_276605
  have hstable : (prefixWord ++ tailWord_276605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276605).length < 2 ^ (prefixWord ++ tailWord_276605).sum := by decide
  have hdescent : baseEnd_276605 < baseStart_276605 := by decide
  rcases family_descends (prefixWord ++ tailWord_276605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276624 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_276624 : Nat := 118140960795 + 276624 * 2 ^ 59
def prefixEnd_276624 : Nat := 4983230072969 + 3 ^ 40 * 276624 * 2
def baseEnd_276624 : Nat := 47347024189810313675945

theorem tailTrace_276624 : CollatzResearch.WordTrace tailWord_276624 prefixEnd_276624 47347024189810313675945 := by
  unfold tailWord_276624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044653074922983231526463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6726204099897310975368617 5044653074922983231526463)
  ·
    refine ⟨7566979612384474847289695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044653074922983231526463 7566979612384474847289695)
    ·
      refine ⟨11350469418576712270934543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7566979612384474847289695 11350469418576712270934543)
      ·
        refine ⟨17025704127865068406401815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11350469418576712270934543 17025704127865068406401815)
        ·
          refine ⟨25538556191797602609602723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17025704127865068406401815 25538556191797602609602723)
          ·
            refine ⟨38307834287696403914404085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25538556191797602609602723 38307834287696403914404085)
            ·
              refine ⟨3591359464471537866975383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38307834287696403914404085 3591359464471537866975383)
              ·
                refine ⟨5387039196707306800463075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591359464471537866975383 5387039196707306800463075)
                ·
                  refine ⟨8080558795060960200694613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387039196707306800463075 8080558795060960200694613)
                  ·
                    refine ⟨47347024189810313675945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 8080558795060960200694613 47347024189810313675945)
                    ·
                      rfl

theorem cell23_276624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_276624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276624 prefixEnd_276624 := by exact prefixLift 276624
  have htrace : WordTrace (prefixWord ++ tailWord_276624) baseStart_276624 baseEnd_276624 := by
    simpa [prefixWord, tailWord_276624, baseEnd_276624] using wordTrace_append hprefix tailTrace_276624
  have hstable : (prefixWord ++ tailWord_276624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276624).length < 2 ^ (prefixWord ++ tailWord_276624).sum := by decide
  have hdescent : baseEnd_276624 < baseStart_276624 := by decide
  rcases family_descends (prefixWord ++ tailWord_276624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276665 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 1, 3, 2]
def baseStart_276665 : Nat := 118140960795 + 276665 * 2 ^ 59
def prefixEnd_276665 : Nat := 4983230072969 + 3 ^ 40 * 276665 * 2
def baseEnd_276665 : Nat := 142062125276265280615147

theorem tailTrace_276665 : CollatzResearch.WordTrace tailWord_276665 prefixEnd_276665 142062125276265280615147 := by
  unfold tailWord_276665
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090801542697430465295449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6727201028464953643530299 10090801542697430465295449)
  ·
    refine ⟨7568101157023072848971587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10090801542697430465295449 7568101157023072848971587)
    ·
      refine ⟨11352151735534609273457381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568101157023072848971587 11352151735534609273457381)
      ·
        refine ⟨2128528450412739238773259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11352151735534609273457381 2128528450412739238773259)
        ·
          refine ⟨3192792675619108858159889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128528450412739238773259 3192792675619108858159889)
          ·
            refine ⟨2394594506714331643619917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3192792675619108858159889 2394594506714331643619917)
            ·
              refine ⟨897972940017874366357469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2394594506714331643619917 897972940017874366357469)
              ·
                refine ⟨336739852506702887384051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897972940017874366357469 336739852506702887384051)
                ·
                  refine ⟨505109778760054331076077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336739852506702887384051 505109778760054331076077)
                  ·
                    refine ⟨189416167035020374153529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505109778760054331076077 189416167035020374153529)
                    ·
                      refine ⟨142062125276265280615147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189416167035020374153529 142062125276265280615147)
                      ·
                        rfl

theorem cell23_276665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_276665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276665 prefixEnd_276665 := by exact prefixLift 276665
  have htrace : WordTrace (prefixWord ++ tailWord_276665) baseStart_276665 baseEnd_276665 := by
    simpa [prefixWord, tailWord_276665, baseEnd_276665] using wordTrace_append hprefix tailTrace_276665
  have hstable : (prefixWord ++ tailWord_276665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276665).length < 2 ^ (prefixWord ++ tailWord_276665).sum := by decide
  have hdescent : baseEnd_276665 < baseStart_276665 := by decide
  rcases family_descends (prefixWord ++ tailWord_276665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276672 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3]
def baseStart_276672 : Nat := 118140960795 + 276672 * 2 ^ 59
def prefixEnd_276672 : Nat := 4983230072969 + 3 ^ 40 * 276672 * 2
def baseEnd_276672 : Nat := 142065719640846753227615

theorem tailTrace_276672 : CollatzResearch.WordTrace tailWord_276672 prefixEnd_276672 142065719640846753227615 := by
  unfold tailWord_276672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5045528426836035330400135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6727371235781380440533513 5045528426836035330400135)
  ·
    refine ⟨7568292640254052995600203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5045528426836035330400135 7568292640254052995600203)
    ·
      refine ⟨11352438960381079493400305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568292640254052995600203 11352438960381079493400305)
      ·
        refine ⟨8514329220285809620050229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11352438960381079493400305 8514329220285809620050229)
        ·
          refine ⟨798218364401794651879709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8514329220285809620050229 798218364401794651879709)
          ·
            refine ⟨299331886650672994454891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 798218364401794651879709 299331886650672994454891)
            ·
              refine ⟨448997829976009491682337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299331886650672994454891 448997829976009491682337)
              ·
                refine ⟨336748372482007118761753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448997829976009491682337 336748372482007118761753)
                ·
                  refine ⟨252561279361505339071315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336748372482007118761753 252561279361505339071315)
                  ·
                    refine ⟨378841919042258008606973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252561279361505339071315 378841919042258008606973)
                    ·
                      refine ⟨142065719640846753227615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 378841919042258008606973 142065719640846753227615)
                      ·
                        rfl

theorem cell23_276672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_276672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276672 prefixEnd_276672 := by exact prefixLift 276672
  have htrace : WordTrace (prefixWord ++ tailWord_276672) baseStart_276672 baseEnd_276672 := by
    simpa [prefixWord, tailWord_276672, baseEnd_276672] using wordTrace_append hprefix tailTrace_276672
  have hstable : (prefixWord ++ tailWord_276672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276672).length < 2 ^ (prefixWord ++ tailWord_276672).sum := by decide
  have hdescent : baseEnd_276672 < baseStart_276672 := by decide
  rcases family_descends (prefixWord ++ tailWord_276672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276681 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_276681 : Nat := 118140960795 + 276681 * 2 ^ 59
def prefixEnd_276681 : Nat := 4983230072969 + 3 ^ 40 * 276681 * 2
def baseEnd_276681 : Nat := 142070340966737218015073

theorem tailTrace_276681 : CollatzResearch.WordTrace tailWord_276681 prefixEnd_276681 142070340966737218015073 := by
  unfold tailWord_276681
  simp only [CollatzResearch.WordTrace]
  refine ⟨10091385110639465197877897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6727590073759643465251931 10091385110639465197877897)
  ·
    refine ⟨7568538832979598898408423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10091385110639465197877897 7568538832979598898408423)
    ·
      refine ⟨11352808249469398347612635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568538832979598898408423 11352808249469398347612635)
      ·
        refine ⟨17029212374204097521418953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11352808249469398347612635 17029212374204097521418953)
        ·
          refine ⟨12771909280653073141064215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17029212374204097521418953 12771909280653073141064215)
          ·
            refine ⟨19157863920979609711596323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12771909280653073141064215 19157863920979609711596323)
            ·
              refine ⟨28736795881469414567394485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19157863920979609711596323 28736795881469414567394485)
              ·
                refine ⟨2694074613887757615693233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28736795881469414567394485 2694074613887757615693233)
                ·
                  refine ⟨2020555960415818211769925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694074613887757615693233 2020555960415818211769925)
                  ·
                    refine ⟨378854242577965914706861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020555960415818211769925 378854242577965914706861)
                    ·
                      refine ⟨142070340966737218015073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 378854242577965914706861 142070340966737218015073)
                      ·
                        rfl

theorem cell23_276681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_276681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276681 prefixEnd_276681 := by exact prefixLift 276681
  have htrace : WordTrace (prefixWord ++ tailWord_276681) baseStart_276681 baseEnd_276681 := by
    simpa [prefixWord, tailWord_276681, baseEnd_276681] using wordTrace_append hprefix tailTrace_276681
  have hstable : (prefixWord ++ tailWord_276681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276681).length < 2 ^ (prefixWord ++ tailWord_276681).sum := by decide
  have hdescent : baseEnd_276681 < baseStart_276681 := by decide
  rcases family_descends (prefixWord ++ tailWord_276681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276735 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 5]
def baseStart_276735 : Nat := 118140960795 + 276735 * 2 ^ 59
def prefixEnd_276735 : Nat := 4983230072969 + 3 ^ 40 * 276735 * 2
def baseEnd_276735 : Nat := 15788674324675556304425

theorem tailTrace_276735 : CollatzResearch.WordTrace tailWord_276735 prefixEnd_276735 15788674324675556304425 := by
  unfold tailWord_276735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10093354652443832420343659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6728903101629221613562439 10093354652443832420343659)
  ·
    refine ⟨15140031978665748630515489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10093354652443832420343659 15140031978665748630515489)
    ·
      refine ⟨11355023983999311472886617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15140031978665748630515489 11355023983999311472886617)
      ·
        refine ⟨8516267987999483604664963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11355023983999311472886617 8516267987999483604664963)
        ·
          refine ⟨12774401981999225406997445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8516267987999483604664963 12774401981999225406997445)
          ·
            refine ⟨2395200371624854763812021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12774401981999225406997445 2395200371624854763812021)
            ·
              refine ⟨224550034839830134107377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2395200371624854763812021 224550034839830134107377)
              ·
                refine ⟨168412526129872600580533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224550034839830134107377 168412526129872600580533)
                ·
                  refine ⟨15788674324675556304425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168412526129872600580533 15788674324675556304425)
                  ·
                    rfl

theorem cell23_276735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 5].length) (baseStart_276735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276735 prefixEnd_276735 := by exact prefixLift 276735
  have htrace : WordTrace (prefixWord ++ tailWord_276735) baseStart_276735 baseEnd_276735 := by
    simpa [prefixWord, tailWord_276735, baseEnd_276735] using wordTrace_append hprefix tailTrace_276735
  have hstable : (prefixWord ++ tailWord_276735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276735).length < 2 ^ (prefixWord ++ tailWord_276735).sum := by decide
  have hdescent : baseEnd_276735 < baseStart_276735 := by decide
  rcases family_descends (prefixWord ++ tailWord_276735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276751 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_276751 : Nat := 118140960795 + 276751 * 2 ^ 59
def prefixEnd_276751 : Nat := 4983230072969 + 3 ^ 40 * 276751 * 2
def baseEnd_276751 : Nat := 142106284612551944139751

theorem tailTrace_276751 : CollatzResearch.WordTrace tailWord_276751 prefixEnd_276751 142106284612551944139751 := by
  unfold tailWord_276751
  simp only [CollatzResearch.WordTrace]
  refine ⟨10093938220385867152926107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6729292146923911435284071 10093938220385867152926107)
  ·
    refine ⟨15140907330578800729389161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10093938220385867152926107 15140907330578800729389161)
    ·
      refine ⟨11355680497934100547041871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15140907330578800729389161 11355680497934100547041871)
      ·
        refine ⟨17033520746901150820562807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355680497934100547041871 17033520746901150820562807)
        ·
          refine ⟨25550281120351726230844211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17033520746901150820562807 25550281120351726230844211)
          ·
            refine ⟨38325421680527589346266317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25550281120351726230844211 38325421680527589346266317)
            ·
              refine ⟨14372033130197846004849869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38325421680527589346266317 14372033130197846004849869)
              ·
                refine ⟨5389512423824192251818701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14372033130197846004849869 5389512423824192251818701)
                ·
                  refine ⟨2021067158934072094432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5389512423824192251818701 2021067158934072094432013)
                  ·
                    refine ⟨757900184600277035412005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2021067158934072094432013 757900184600277035412005)
                    ·
                      refine ⟨142106284612551944139751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 757900184600277035412005 142106284612551944139751)
                      ·
                        rfl

theorem cell23_276751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_276751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276751 prefixEnd_276751 := by exact prefixLift 276751
  have htrace : WordTrace (prefixWord ++ tailWord_276751) baseStart_276751 baseEnd_276751 := by
    simpa [prefixWord, tailWord_276751, baseEnd_276751] using wordTrace_append hprefix tailTrace_276751
  have hstable : (prefixWord ++ tailWord_276751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276751).length < 2 ^ (prefixWord ++ tailWord_276751).sum := by decide
  have hdescent : baseEnd_276751 < baseStart_276751 := by decide
  rcases family_descends (prefixWord ++ tailWord_276751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276791 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 8]
def baseStart_276791 : Nat := 118140960795 + 276791 * 2 ^ 59
def prefixEnd_276791 : Nat := 4983230072969 + 3 ^ 40 * 276791 * 2
def baseEnd_276791 : Nat := 15791869315414643071063

theorem tailTrace_276791 : CollatzResearch.WordTrace tailWord_276791 prefixEnd_276791 15791869315414643071063 := by
  unfold tailWord_276791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10095397140240953984382227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6730264760160635989588151 10095397140240953984382227)
  ·
    refine ⟨15143095710361430976573341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10095397140240953984382227 15143095710361430976573341)
    ·
      refine ⟨5678660891385536616215003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15143095710361430976573341 5678660891385536616215003)
      ·
        refine ⟨8517991337078304924322505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5678660891385536616215003 8517991337078304924322505)
        ·
          refine ⟨6388493502808728693241879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8517991337078304924322505 6388493502808728693241879)
          ·
            refine ⟨9582740254213093039862819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6388493502808728693241879 9582740254213093039862819)
            ·
              refine ⟨14374110381319639559794229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9582740254213093039862819 14374110381319639559794229)
              ·
                refine ⟨1347572848248716208730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14374110381319639559794229 1347572848248716208730709)
                ·
                  refine ⟨15791869315414643071063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1347572848248716208730709 15791869315414643071063)
                  ·
                    rfl

theorem cell23_276791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 8].length) (baseStart_276791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276791 prefixEnd_276791 := by exact prefixLift 276791
  have htrace : WordTrace (prefixWord ++ tailWord_276791) baseStart_276791 baseEnd_276791 := by
    simpa [prefixWord, tailWord_276791, baseEnd_276791] using wordTrace_append hprefix tailTrace_276791
  have hstable : (prefixWord ++ tailWord_276791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276791).length < 2 ^ (prefixWord ++ tailWord_276791).sum := by decide
  have hdescent : baseEnd_276791 < baseStart_276791 := by decide
  rcases family_descends (prefixWord ++ tailWord_276791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276808 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 6]
def baseStart_276808 : Nat := 118140960795 + 276808 * 2 ^ 59
def prefixEnd_276808 : Nat := 4983230072969 + 3 ^ 40 * 276808 * 2
def baseEnd_276808 : Nat := 15792839223317580125221

theorem tailTrace_276808 : CollatzResearch.WordTrace tailWord_276808 prefixEnd_276808 15792839223317580125221 := by
  unfold tailWord_276808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5048008590589682943875539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6730678120786243925167385 5048008590589682943875539)
  ·
    refine ⟨7572012885884524415813309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5048008590589682943875539 7572012885884524415813309)
    ·
      refine ⟨2839504832206696655929991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7572012885884524415813309 2839504832206696655929991)
      ·
        refine ⟨4259257248310044983894987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839504832206696655929991 4259257248310044983894987)
        ·
          refine ⟨6388885872465067475842481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259257248310044983894987 6388885872465067475842481)
          ·
            refine ⟨4791664404348800606881861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6388885872465067475842481 4791664404348800606881861)
            ·
              refine ⟨898437075815400113790349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4791664404348800606881861 898437075815400113790349)
              ·
                refine ⟨336913903430775042671381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 898437075815400113790349 336913903430775042671381)
                ·
                  refine ⟨15792839223317580125221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 336913903430775042671381 15792839223317580125221)
                  ·
                    rfl

theorem cell23_276808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_276808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276808 prefixEnd_276808 := by exact prefixLift 276808
  have htrace : WordTrace (prefixWord ++ tailWord_276808) baseStart_276808 baseEnd_276808 := by
    simpa [prefixWord, tailWord_276808, baseEnd_276808] using wordTrace_append hprefix tailTrace_276808
  have hstable : (prefixWord ++ tailWord_276808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276808).length < 2 ^ (prefixWord ++ tailWord_276808).sum := by decide
  have hdescent : baseEnd_276808 < baseStart_276808 := by decide
  rcases family_descends (prefixWord ++ tailWord_276808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_276811 : Nat := 118140960795 + 276811 * 2 ^ 59
def prefixEnd_276811 : Nat := 4983230072969 + 3 ^ 40 * 276811 * 2
def baseEnd_276811 : Nat := 142137093451821709389475

theorem tailTrace_276811 : CollatzResearch.WordTrace tailWord_276811 prefixEnd_276811 142137093451821709389475 := by
  unfold tailWord_276811
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096126600168497400110287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6730751066778998266740191 10096126600168497400110287)
  ·
    refine ⟨15144189900252746100165431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10096126600168497400110287 15144189900252746100165431)
    ·
      refine ⟨22716284850379119150248147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15144189900252746100165431 22716284850379119150248147)
      ·
        refine ⟨34074427275568678725372221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22716284850379119150248147 34074427275568678725372221)
        ·
          refine ⟨12777910228338254522014583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34074427275568678725372221 12777910228338254522014583)
          ·
            refine ⟨19166865342507381783021875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12777910228338254522014583 19166865342507381783021875)
            ·
              refine ⟨28750298013761072674532813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19166865342507381783021875 28750298013761072674532813)
              ·
                refine ⟨10781361755160402252949805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28750298013761072674532813 10781361755160402252949805)
                ·
                  refine ⟨4043010658185150844856177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10781361755160402252949805 4043010658185150844856177)
                  ·
                    refine ⟨3032257993638863133642133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4043010658185150844856177 3032257993638863133642133)
                    ·
                      refine ⟨142137093451821709389475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3032257993638863133642133 142137093451821709389475)
                      ·
                        rfl

theorem cell23_276811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_276811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276811 prefixEnd_276811 := by exact prefixLift 276811
  have htrace : WordTrace (prefixWord ++ tailWord_276811) baseStart_276811 baseEnd_276811 := by
    simpa [prefixWord, tailWord_276811, baseEnd_276811] using wordTrace_append hprefix tailTrace_276811
  have hstable : (prefixWord ++ tailWord_276811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276811).length < 2 ^ (prefixWord ++ tailWord_276811).sum := by decide
  have hdescent : baseEnd_276811 < baseStart_276811 := by decide
  rcases family_descends (prefixWord ++ tailWord_276811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276835 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 3]
def baseStart_276835 : Nat := 118140960795 + 276835 * 2 ^ 59
def prefixEnd_276835 : Nat := 4983230072969 + 3 ^ 40 * 276835 * 2
def baseEnd_276835 : Nat := 142149416987529615489365

theorem tailTrace_276835 : CollatzResearch.WordTrace tailWord_276835 prefixEnd_276835 142149416987529615489365 := by
  unfold tailWord_276835
  simp only [CollatzResearch.WordTrace]
  refine ⟨10097001952081549498983959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6731334634721032999322639 10097001952081549498983959)
  ·
    refine ⟨15145502928122324248475939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10097001952081549498983959 15145502928122324248475939)
    ·
      refine ⟨22718254392183486372713909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15145502928122324248475939 22718254392183486372713909)
      ·
        refine ⟨2129836349267201847441929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22718254392183486372713909 2129836349267201847441929)
        ·
          refine ⟨1597377261950401385581447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2129836349267201847441929 1597377261950401385581447)
          ·
            refine ⟨2396065892925602078372171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597377261950401385581447 2396065892925602078372171)
            ·
              refine ⟨3594098839388403117558257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396065892925602078372171 3594098839388403117558257)
              ·
                refine ⟨2695574129541302338168693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3594098839388403117558257 2695574129541302338168693)
                ·
                  refine ⟨252710074644497094203315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2695574129541302338168693 252710074644497094203315)
                  ·
                    refine ⟨379065111966745641304973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252710074644497094203315 379065111966745641304973)
                    ·
                      refine ⟨142149416987529615489365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379065111966745641304973 142149416987529615489365)
                      ·
                        rfl

theorem cell23_276835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_276835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276835 prefixEnd_276835 := by exact prefixLift 276835
  have htrace : WordTrace (prefixWord ++ tailWord_276835) baseStart_276835 baseEnd_276835 := by
    simpa [prefixWord, tailWord_276835, baseEnd_276835] using wordTrace_append hprefix tailTrace_276835
  have hstable : (prefixWord ++ tailWord_276835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276835).length < 2 ^ (prefixWord ++ tailWord_276835).sum := by decide
  have hdescent : baseEnd_276835 < baseStart_276835 := by decide
  rcases family_descends (prefixWord ++ tailWord_276835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276842 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_276842 : Nat := 118140960795 + 276842 * 2 ^ 59
def prefixEnd_276842 : Nat := 4983230072969 + 3 ^ 40 * 276842 * 2
def baseEnd_276842 : Nat := 15794779039123454233537

theorem tailTrace_276842 : CollatzResearch.WordTrace tailWord_276842 prefixEnd_276842 15794779039123454233537 := by
  unfold tailWord_276842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524314315764047423622195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6731504842037459796325853 2524314315764047423622195)
  ·
    refine ⟨3786471473646071135433293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2524314315764047423622195 3786471473646071135433293)
    ·
      refine ⟨1419926802617276675787485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3786471473646071135433293 1419926802617276675787485)
      ·
        refine ⟨532472550981478753420307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1419926802617276675787485 532472550981478753420307)
        ·
          refine ⟨798708826472218130130461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532472550981478753420307 798708826472218130130461)
          ·
            refine ⟨299515809927081798798923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 798708826472218130130461 299515809927081798798923)
            ·
              refine ⟨449273714890622698198385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299515809927081798798923 449273714890622698198385)
              ·
                refine ⟨336955286167967023648789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449273714890622698198385 336955286167967023648789)
                ·
                  refine ⟨15794779039123454233537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 336955286167967023648789 15794779039123454233537)
                  ·
                    rfl

theorem cell23_276842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_276842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276842 prefixEnd_276842 := by exact prefixLift 276842
  have htrace : WordTrace (prefixWord ++ tailWord_276842) baseStart_276842 baseEnd_276842 := by
    simpa [prefixWord, tailWord_276842, baseEnd_276842] using wordTrace_append hprefix tailTrace_276842
  have hstable : (prefixWord ++ tailWord_276842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276842).length < 2 ^ (prefixWord ++ tailWord_276842).sum := by decide
  have hdescent : baseEnd_276842 < baseStart_276842 := by decide
  rcases family_descends (prefixWord ++ tailWord_276842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276875 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 4]
def baseStart_276875 : Nat := 118140960795 + 276875 * 2 ^ 59
def prefixEnd_276875 : Nat := 4983230072969 + 3 ^ 40 * 276875 * 2
def baseEnd_276875 : Nat := 142169956213709458989181

theorem tailTrace_276875 : CollatzResearch.WordTrace tailWord_276875 prefixEnd_276875 142169956213709458989181 := by
  unfold tailWord_276875
  simp only [CollatzResearch.WordTrace]
  refine ⟨10098460871936636330440079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6732307247957757553626719 10098460871936636330440079)
  ·
    refine ⟨15147691307904954495660119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10098460871936636330440079 15147691307904954495660119)
    ·
      refine ⟨22721536961857431743490179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15147691307904954495660119 22721536961857431743490179)
      ·
        refine ⟨34082305442786147615235269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721536961857431743490179 34082305442786147615235269)
        ·
          refine ⟨6390432270522402677856613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34082305442786147615235269 6390432270522402677856613)
          ·
            refine ⟨1198206050722950502098115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6390432270522402677856613 1198206050722950502098115)
            ·
              refine ⟨1797309076084425753147173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198206050722950502098115 1797309076084425753147173)
              ·
                refine ⟨336995451765829828715095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1797309076084425753147173 336995451765829828715095)
                ·
                  refine ⟨505493177648744743072643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336995451765829828715095 505493177648744743072643)
                  ·
                    refine ⟨758239766473117114608965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 505493177648744743072643 758239766473117114608965)
                    ·
                      refine ⟨142169956213709458989181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 758239766473117114608965 142169956213709458989181)
                      ·
                        rfl

theorem cell23_276875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 4].length) (baseStart_276875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276875 prefixEnd_276875 := by exact prefixLift 276875
  have htrace : WordTrace (prefixWord ++ tailWord_276875) baseStart_276875 baseEnd_276875 := by
    simpa [prefixWord, tailWord_276875, baseEnd_276875] using wordTrace_append hprefix tailTrace_276875
  have hstable : (prefixWord ++ tailWord_276875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276875).length < 2 ^ (prefixWord ++ tailWord_276875).sum := by decide
  have hdescent : baseEnd_276875 < baseStart_276875 := by decide
  rcases family_descends (prefixWord ++ tailWord_276875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276895 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_276895 : Nat := 118140960795 + 276895 * 2 ^ 59
def prefixEnd_276895 : Nat := 4983230072969 + 3 ^ 40 * 276895 * 2
def baseEnd_276895 : Nat := 142180225826799380739089

theorem tailTrace_276895 : CollatzResearch.WordTrace tailWord_276895 prefixEnd_276895 142180225826799380739089 := by
  unfold tailWord_276895
  simp only [CollatzResearch.WordTrace]
  refine ⟨10099190331864179746168139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6732793554576119830778759 10099190331864179746168139)
  ·
    refine ⟨15148785497796269619252209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10099190331864179746168139 15148785497796269619252209)
    ·
      refine ⟨11361589123347202214439157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15148785497796269619252209 11361589123347202214439157)
      ·
        refine ⟨1065148980313800207603671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11361589123347202214439157 1065148980313800207603671)
        ·
          refine ⟨1597723470470700311405507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065148980313800207603671 1597723470470700311405507)
          ·
            refine ⟨2396585205706050467108261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597723470470700311405507 2396585205706050467108261)
            ·
              refine ⟨449359726069884462582799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2396585205706050467108261 449359726069884462582799)
              ·
                refine ⟨674039589104826693874199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449359726069884462582799 674039589104826693874199)
                ·
                  refine ⟨1011059383657240040811299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674039589104826693874199 1011059383657240040811299)
                  ·
                    refine ⟨1516589075485860061216949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011059383657240040811299 1516589075485860061216949)
                    ·
                      refine ⟨142180225826799380739089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1516589075485860061216949 142180225826799380739089)
                      ·
                        rfl

theorem cell23_276895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_276895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276895 prefixEnd_276895 := by exact prefixLift 276895
  have htrace : WordTrace (prefixWord ++ tailWord_276895) baseStart_276895 baseEnd_276895 := by
    simpa [prefixWord, tailWord_276895, baseEnd_276895] using wordTrace_append hprefix tailTrace_276895
  have hstable : (prefixWord ++ tailWord_276895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276895).length < 2 ^ (prefixWord ++ tailWord_276895).sum := by decide
  have hdescent : baseEnd_276895 < baseStart_276895 := by decide
  rcases family_descends (prefixWord ++ tailWord_276895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276919 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 2, 4]
def baseStart_276919 : Nat := 118140960795 + 276919 * 2 ^ 59
def prefixEnd_276919 : Nat := 4983230072969 + 3 ^ 40 * 276919 * 2
def baseEnd_276919 : Nat := 47397516454169095612993

theorem tailTrace_276919 : CollatzResearch.WordTrace tailWord_276919 prefixEnd_276919 47397516454169095612993 := by
  unfold tailWord_276919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10100065683777231845041811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6733377122518154563361207 10100065683777231845041811)
  ·
    refine ⟨15150098525665847767562717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10100065683777231845041811 15150098525665847767562717)
    ·
      refine ⟨5681286947124692912836019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15150098525665847767562717 5681286947124692912836019)
      ·
        refine ⟨8521930420687039369254029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5681286947124692912836019 8521930420687039369254029)
        ·
          refine ⟨3195723907757639763470261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8521930420687039369254029 3195723907757639763470261)
          ·
            refine ⟨299599116352278727825337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3195723907757639763470261 299599116352278727825337)
            ·
              refine ⟨224699337264209045869003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299599116352278727825337 224699337264209045869003)
              ·
                refine ⟨337049005896313568803505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224699337264209045869003 337049005896313568803505)
                ·
                  refine ⟨252786754422235176602629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337049005896313568803505 252786754422235176602629)
                  ·
                    refine ⟨47397516454169095612993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 252786754422235176602629 47397516454169095612993)
                    ·
                      rfl

theorem cell23_276919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_276919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276919 prefixEnd_276919 := by exact prefixLift 276919
  have htrace : WordTrace (prefixWord ++ tailWord_276919) baseStart_276919 baseEnd_276919 := by
    simpa [prefixWord, tailWord_276919, baseEnd_276919] using wordTrace_append hprefix tailTrace_276919
  have hstable : (prefixWord ++ tailWord_276919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276919).length < 2 ^ (prefixWord ++ tailWord_276919).sum := by decide
  have hdescent : baseEnd_276919 < baseStart_276919 := by decide
  rcases family_descends (prefixWord ++ tailWord_276919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276946 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_276946 : Nat := 118140960795 + 276946 * 2 ^ 59
def prefixEnd_276946 : Nat := 4983230072969 + 3 ^ 40 * 276946 * 2
def baseEnd_276946 : Nat := 142206413340178681201355

theorem tailTrace_276946 : CollatzResearch.WordTrace tailWord_276946 prefixEnd_276946 142206413340178681201355 := by
  unfold tailWord_276946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525262613669853864068673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6734033636452943637516461 2525262613669853864068673)
  ·
    refine ⟨1893946960252390398051505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2525262613669853864068673 1893946960252390398051505)
    ·
      refine ⟨1420460220189292798538629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1893946960252390398051505 1420460220189292798538629)
      ·
        refine ⟨266336291285492399725993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1420460220189292798538629 266336291285492399725993)
        ·
          refine ⟨199752218464119299794495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266336291285492399725993 199752218464119299794495)
          ·
            refine ⟨299628327696178949691743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199752218464119299794495 299628327696178949691743)
            ·
              refine ⟨449442491544268424537615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299628327696178949691743 449442491544268424537615)
              ·
                refine ⟨674163737316402636806423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449442491544268424537615 674163737316402636806423)
                ·
                  refine ⟨1011245605974603955209635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674163737316402636806423 1011245605974603955209635)
                  ·
                    refine ⟨1516868408961905932814453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1011245605974603955209635 1516868408961905932814453)
                    ·
                      refine ⟨142206413340178681201355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1516868408961905932814453 142206413340178681201355)
                      ·
                        rfl

theorem cell23_276946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_276946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276946 prefixEnd_276946 := by exact prefixLift 276946
  have htrace : WordTrace (prefixWord ++ tailWord_276946) baseStart_276946 baseEnd_276946 := by
    simpa [prefixWord, tailWord_276946, baseEnd_276946] using wordTrace_append hprefix tailTrace_276946
  have hstable : (prefixWord ++ tailWord_276946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276946).length < 2 ^ (prefixWord ++ tailWord_276946).sum := by decide
  have hdescent : baseEnd_276946 < baseStart_276946 := by decide
  rcases family_descends (prefixWord ++ tailWord_276946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276959 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 3]
def baseStart_276959 : Nat := 118140960795 + 276959 * 2 ^ 59
def prefixEnd_276959 : Nat := 4983230072969 + 3 ^ 40 * 276959 * 2
def baseEnd_276959 : Nat := 142213088588687130338795

theorem tailTrace_276959 : CollatzResearch.WordTrace tailWord_276959 prefixEnd_276959 142213088588687130338795 := by
  unfold tailWord_276959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101524603632318676497931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6734349735754879117665287 10101524603632318676497931)
  ·
    refine ⟨15152286905448478014746897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10101524603632318676497931 15152286905448478014746897)
    ·
      refine ⟨11364215179086358511060173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15152286905448478014746897 11364215179086358511060173)
      ·
        refine ⟨4261580692157384441647565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11364215179086358511060173 4261580692157384441647565)
        ·
          refine ⟨1598092759559019165617837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4261580692157384441647565 1598092759559019165617837)
          ·
            refine ⟨599284784834632187106689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1598092759559019165617837 599284784834632187106689)
            ·
              refine ⟨449463588625974140330017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599284784834632187106689 449463588625974140330017)
              ·
                refine ⟨337097691469480605247513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449463588625974140330017 337097691469480605247513)
                ·
                  refine ⟨252823268602110453935635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337097691469480605247513 252823268602110453935635)
                  ·
                    refine ⟨379234902903165680903453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252823268602110453935635 379234902903165680903453)
                    ·
                      refine ⟨142213088588687130338795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379234902903165680903453 142213088588687130338795)
                      ·
                        rfl

theorem cell23_276959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_276959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_276959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_276959 prefixEnd_276959 := by exact prefixLift 276959
  have htrace : WordTrace (prefixWord ++ tailWord_276959) baseStart_276959 baseEnd_276959 := by
    simpa [prefixWord, tailWord_276959, baseEnd_276959] using wordTrace_append hprefix tailTrace_276959
  have hstable : (prefixWord ++ tailWord_276959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276959).length < 2 ^ (prefixWord ++ tailWord_276959).sum := by decide
  have hdescent : baseEnd_276959 < baseStart_276959 := by decide
  rcases family_descends (prefixWord ++ tailWord_276959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277008 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_277008 : Nat := 118140960795 + 277008 * 2 ^ 59
def prefixEnd_277008 : Nat := 4983230072969 + 3 ^ 40 * 277008 * 2
def baseEnd_277008 : Nat := 142238249140757438626069

theorem tailTrace_277008 : CollatzResearch.WordTrace tailWord_277008 prefixEnd_277008 142238249140757438626069 := by
  unfold tailWord_277008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051655890227400022515839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6735541186969866696687785 5051655890227400022515839)
  ·
    refine ⟨7577483835341100033773759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5051655890227400022515839 7577483835341100033773759)
    ·
      refine ⟨11366225753011650050660639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7577483835341100033773759 11366225753011650050660639)
      ·
        refine ⟨17049338629517475075990959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11366225753011650050660639 17049338629517475075990959)
        ·
          refine ⟨25574007944276212613986439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17049338629517475075990959 25574007944276212613986439)
          ·
            refine ⟨38361011916414318920979659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25574007944276212613986439 38361011916414318920979659)
            ·
              refine ⟨57541517874621478381469489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38361011916414318920979659 57541517874621478381469489)
              ·
                refine ⟨43156138405966108786102117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57541517874621478381469489 43156138405966108786102117)
                ·
                  refine ⟨8091775951118645397394147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43156138405966108786102117 8091775951118645397394147)
                  ·
                    refine ⟨12137663926677968096091221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8091775951118645397394147 12137663926677968096091221)
                    ·
                      refine ⟨142238249140757438626069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 12137663926677968096091221 142238249140757438626069)
                      ·
                        rfl

theorem cell23_277008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_277008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277008 prefixEnd_277008 := by exact prefixLift 277008
  have htrace : WordTrace (prefixWord ++ tailWord_277008) baseStart_277008 baseEnd_277008 := by
    simpa [prefixWord, tailWord_277008, baseEnd_277008] using wordTrace_append hprefix tailTrace_277008
  have hstable : (prefixWord ++ tailWord_277008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277008).length < 2 ^ (prefixWord ++ tailWord_277008).sum := by decide
  have hdescent : baseEnd_277008 < baseStart_277008 := by decide
  rcases family_descends (prefixWord ++ tailWord_277008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277016 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_277016 : Nat := 118140960795 + 277016 * 2 ^ 59
def prefixEnd_277016 : Nat := 4983230072969 + 3 ^ 40 * 277016 * 2
def baseEnd_277016 : Nat := 142242356985993407326033

theorem tailTrace_277016 : CollatzResearch.WordTrace tailWord_277016 prefixEnd_277016 142242356985993407326033 := by
  unfold tailWord_277016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051801782212908705661451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6735735709617211607548601 5051801782212908705661451)
  ·
    refine ⟨7577702673319363058492177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5051801782212908705661451 7577702673319363058492177)
    ·
      refine ⟨5683277004989522293869133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7577702673319363058492177 5683277004989522293869133)
      ·
        refine ⟨2131228876871070860200925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5683277004989522293869133 2131228876871070860200925)
        ·
          refine ⟨799210828826651572575347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2131228876871070860200925 799210828826651572575347)
          ·
            refine ⟨1198816243239977358863021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799210828826651572575347 1198816243239977358863021)
            ·
              refine ⟨449556091214991509573633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1198816243239977358863021 449556091214991509573633)
              ·
                refine ⟨337167068411243632180225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449556091214991509573633 337167068411243632180225)
                ·
                  refine ⟨252875301308432724135169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337167068411243632180225 252875301308432724135169)
                  ·
                    refine ⟨189656475981324543101377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 252875301308432724135169 189656475981324543101377)
                    ·
                      refine ⟨142242356985993407326033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189656475981324543101377 142242356985993407326033)
                      ·
                        rfl

theorem cell23_277016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_277016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277016 prefixEnd_277016 := by exact prefixLift 277016
  have htrace : WordTrace (prefixWord ++ tailWord_277016) baseStart_277016 baseEnd_277016 := by
    simpa [prefixWord, tailWord_277016, baseEnd_277016] using wordTrace_append hprefix tailTrace_277016
  have hstable : (prefixWord ++ tailWord_277016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277016).length < 2 ^ (prefixWord ++ tailWord_277016).sum := by decide
  have hdescent : baseEnd_277016 < baseStart_277016 := by decide
  rcases family_descends (prefixWord ++ tailWord_277016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277042 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_277042 : Nat := 118140960795 + 277042 * 2 ^ 59
def prefixEnd_277042 : Nat := 4983230072969 + 3 ^ 40 * 277042 * 2
def baseEnd_277042 : Nat := 142255707483010305600913

theorem tailTrace_277042 : CollatzResearch.WordTrace tailWord_277042 prefixEnd_277042 142255707483010305600913 := by
  unfold tailWord_277042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526137965582905962942345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6736367908221082567846253 2526137965582905962942345)
  ·
    refine ⟨1894603474187179472206759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2526137965582905962942345 1894603474187179472206759)
    ·
      refine ⟨2841905211280769208310139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894603474187179472206759 2841905211280769208310139)
      ·
        refine ⟨4262857816921153812465209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841905211280769208310139 4262857816921153812465209)
        ·
          refine ⟨3197143362690865359348907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262857816921153812465209 3197143362690865359348907)
          ·
            refine ⟨4795715044036298039023361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197143362690865359348907 4795715044036298039023361)
            ·
              refine ⟨3596786283027223529267521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4795715044036298039023361 3596786283027223529267521)
              ·
                refine ⟨2697589712270417646950641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596786283027223529267521 2697589712270417646950641)
                ·
                  refine ⟨2023192284202813235212981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2697589712270417646950641 2023192284202813235212981)
                  ·
                    refine ⟨189674276644013740801217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2023192284202813235212981 189674276644013740801217)
                    ·
                      refine ⟨142255707483010305600913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189674276644013740801217 142255707483010305600913)
                      ·
                        rfl

theorem cell23_277042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_277042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277042 prefixEnd_277042 := by exact prefixLift 277042
  have htrace : WordTrace (prefixWord ++ tailWord_277042) baseStart_277042 baseEnd_277042 := by
    simpa [prefixWord, tailWord_277042, baseEnd_277042] using wordTrace_append hprefix tailTrace_277042
  have hstable : (prefixWord ++ tailWord_277042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277042).length < 2 ^ (prefixWord ++ tailWord_277042).sum := by decide
  have hdescent : baseEnd_277042 < baseStart_277042 := by decide
  rcases family_descends (prefixWord ++ tailWord_277042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277055 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_277055 : Nat := 118140960795 + 277055 * 2 ^ 59
def prefixEnd_277055 : Nat := 4983230072969 + 3 ^ 40 * 277055 * 2
def baseEnd_277055 : Nat := 142262382731518754738353

theorem tailTrace_277055 : CollatzResearch.WordTrace tailWord_277055 prefixEnd_277055 142262382731518754738353 := by
  unfold tailWord_277055
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105026011284527071992619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6736684007523018047995079 10105026011284527071992619)
  ·
    refine ⟨15157539016926790607988929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10105026011284527071992619 15157539016926790607988929)
    ·
      refine ⟨11368154262695092955991697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15157539016926790607988929 11368154262695092955991697)
      ·
        refine ⟨8526115697021319716993773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11368154262695092955991697 8526115697021319716993773)
        ·
          refine ⟨3197293386382994893872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8526115697021319716993773 3197293386382994893872665)
          ·
            refine ⟨2397970039787246170404499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197293386382994893872665 2397970039787246170404499)
            ·
              refine ⟨3596955059680869255606749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397970039787246170404499 3596955059680869255606749)
              ·
                refine ⟨1348858147380325970852531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596955059680869255606749 1348858147380325970852531)
                ·
                  refine ⟨2023287221070488956278797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348858147380325970852531 2023287221070488956278797)
                  ·
                    refine ⟨758732707901433358604549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2023287221070488956278797 758732707901433358604549)
                    ·
                      refine ⟨142262382731518754738353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 758732707901433358604549 142262382731518754738353)
                      ·
                        rfl

theorem cell23_277055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_277055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277055 prefixEnd_277055 := by exact prefixLift 277055
  have htrace : WordTrace (prefixWord ++ tailWord_277055) baseStart_277055 baseEnd_277055 := by
    simpa [prefixWord, tailWord_277055, baseEnd_277055] using wordTrace_append hprefix tailTrace_277055
  have hstable : (prefixWord ++ tailWord_277055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277055).length < 2 ^ (prefixWord ++ tailWord_277055).sum := by decide
  have hdescent : baseEnd_277055 < baseStart_277055 := by decide
  rcases family_descends (prefixWord ++ tailWord_277055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277069 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_277069 : Nat := 118140960795 + 277069 * 2 ^ 59
def prefixEnd_277069 : Nat := 4983230072969 + 3 ^ 40 * 277069 * 2
def baseEnd_277069 : Nat := 47423190486893899987763

theorem tailTrace_277069 : CollatzResearch.WordTrace tailWord_277069 prefixEnd_277069 47423190486893899987763 := by
  unfold tailWord_277069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105536633233807463002261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6737024422155871642001507 10105536633233807463002261)
  ·
    refine ⟨473697029682834724828231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10105536633233807463002261 473697029682834724828231)
    ·
      refine ⟨710545544524252087242347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473697029682834724828231 710545544524252087242347)
      ·
        refine ⟨1065818316786378130863521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710545544524252087242347 1065818316786378130863521)
        ·
          refine ⟨799363737589783598147641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1065818316786378130863521 799363737589783598147641)
          ·
            refine ⟨599522803192337698610731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799363737589783598147641 599522803192337698610731)
            ·
              refine ⟨899284204788506547916097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599522803192337698610731 899284204788506547916097)
              ·
                refine ⟨674463153591379910937073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899284204788506547916097 674463153591379910937073)
                ·
                  refine ⟨505847365193534933202805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 674463153591379910937073 505847365193534933202805)
                  ·
                    refine ⟨47423190486893899987763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 505847365193534933202805 47423190486893899987763)
                    ·
                      rfl

theorem cell23_277069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_277069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277069 prefixEnd_277069 := by exact prefixLift 277069
  have htrace : WordTrace (prefixWord ++ tailWord_277069) baseStart_277069 baseEnd_277069 := by
    simpa [prefixWord, tailWord_277069, baseEnd_277069] using wordTrace_append hprefix tailTrace_277069
  have hstable : (prefixWord ++ tailWord_277069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277069).length < 2 ^ (prefixWord ++ tailWord_277069).sum := by decide
  have hdescent : baseEnd_277069 < baseStart_277069 := by decide
  rcases family_descends (prefixWord ++ tailWord_277069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277072 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2]
def baseStart_277072 : Nat := 118140960795 + 277072 * 2 ^ 59
def prefixEnd_277072 : Nat := 4983230072969 + 3 ^ 40 * 277072 * 2
def baseEnd_277072 : Nat := 142271111902645188225775

theorem tailTrace_277072 : CollatzResearch.WordTrace tailWord_277072 prefixEnd_277072 142271111902645188225775 := by
  unfold tailWord_277072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052823026111469487680735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6737097368148625983574313 5052823026111469487680735)
  ·
    refine ⟨7579234539167204231521103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5052823026111469487680735 7579234539167204231521103)
    ·
      refine ⟨11368851808750806347281655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7579234539167204231521103 11368851808750806347281655)
      ·
        refine ⟨17053277713126209520922483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11368851808750806347281655 17053277713126209520922483)
        ·
          refine ⟨25579916569689314281383725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17053277713126209520922483 25579916569689314281383725)
          ·
            refine ⟨9592468713633492855518897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25579916569689314281383725 9592468713633492855518897)
            ·
              refine ⟨7194351535225119641639173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9592468713633492855518897 7194351535225119641639173)
              ·
                refine ⟨1348940912854709932807345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7194351535225119641639173 1348940912854709932807345)
                ·
                  refine ⟨1011705684641032449605509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348940912854709932807345 1011705684641032449605509)
                  ·
                    refine ⟨189694815870193584301033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011705684641032449605509 189694815870193584301033)
                    ·
                      refine ⟨142271111902645188225775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189694815870193584301033 142271111902645188225775)
                      ·
                        rfl

theorem cell23_277072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2].length) (baseStart_277072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277072 prefixEnd_277072 := by exact prefixLift 277072
  have htrace : WordTrace (prefixWord ++ tailWord_277072) baseStart_277072 baseEnd_277072 := by
    simpa [prefixWord, tailWord_277072, baseEnd_277072] using wordTrace_append hprefix tailTrace_277072
  have hstable : (prefixWord ++ tailWord_277072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277072).length < 2 ^ (prefixWord ++ tailWord_277072).sum := by decide
  have hdescent : baseEnd_277072 < baseStart_277072 := by decide
  rcases family_descends (prefixWord ++ tailWord_277072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277092 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_277092 : Nat := 118140960795 + 277092 * 2 ^ 59
def prefixEnd_277092 : Nat := 4983230072969 + 3 ^ 40 * 277092 * 2
def baseEnd_277092 : Nat := 142281381515735109975683

theorem tailTrace_277092 : CollatzResearch.WordTrace tailWord_277092 prefixEnd_277092 142281381515735109975683 := by
  unfold tailWord_277092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053187756075241195544765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6737583674766988260726353 5053187756075241195544765)
  ·
    refine ⟨1894945408528215448329287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5053187756075241195544765 1894945408528215448329287)
    ·
      refine ⟨2842418112792323172493931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894945408528215448329287 2842418112792323172493931)
      ·
        refine ⟨4263627169188484758740897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842418112792323172493931 4263627169188484758740897)
        ·
          refine ⟨3197720376891363569055673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4263627169188484758740897 3197720376891363569055673)
          ·
            refine ⟨2398290282668522676791755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197720376891363569055673 2398290282668522676791755)
            ·
              refine ⟨3597435424002784015187633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398290282668522676791755 3597435424002784015187633)
              ·
                refine ⟨2698076568002088011390725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597435424002784015187633 2698076568002088011390725)
                ·
                  refine ⟨505889356500391502135761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2698076568002088011390725 505889356500391502135761)
                  ·
                    refine ⟨379417017375293626601821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505889356500391502135761 379417017375293626601821)
                    ·
                      refine ⟨142281381515735109975683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379417017375293626601821 142281381515735109975683)
                      ·
                        rfl

theorem cell23_277092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_277092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277092 prefixEnd_277092 := by exact prefixLift 277092
  have htrace : WordTrace (prefixWord ++ tailWord_277092) baseStart_277092 baseEnd_277092 := by
    simpa [prefixWord, tailWord_277092, baseEnd_277092] using wordTrace_append hprefix tailTrace_277092
  have hstable : (prefixWord ++ tailWord_277092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277092).length < 2 ^ (prefixWord ++ tailWord_277092).sum := by decide
  have hdescent : baseEnd_277092 < baseStart_277092 := by decide
  rcases family_descends (prefixWord ++ tailWord_277092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277149 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_277149 : Nat := 118140960795 + 277149 * 2 ^ 59
def prefixEnd_277149 : Nat := 4983230072969 + 3 ^ 40 * 277149 * 2
def baseEnd_277149 : Nat := 142310649913041386962921

theorem tailTrace_277149 : CollatzResearch.WordTrace tailWord_277149 prefixEnd_277149 142310649913041386962921 := by
  unfold tailWord_277149
  simp only [CollatzResearch.WordTrace]
  refine ⟨10108454472943981125914501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6738969648629320750609667 10108454472943981125914501)
  ·
    refine ⟨1895335213676996461108969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10108454472943981125914501 1895335213676996461108969)
    ·
      refine ⟨1421501410257747345831727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1895335213676996461108969 1421501410257747345831727)
      ·
        refine ⟨2132252115386621018747591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421501410257747345831727 2132252115386621018747591)
        ·
          refine ⟨3198378173079931528121387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132252115386621018747591 3198378173079931528121387)
          ·
            refine ⟨4797567259619897292182081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198378173079931528121387 4797567259619897292182081)
            ·
              refine ⟨3598175444714922969136561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4797567259619897292182081 3598175444714922969136561)
              ·
                refine ⟨2698631583536192226852421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598175444714922969136561 2698631583536192226852421)
                ·
                  refine ⟨505993421913036042534829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2698631583536192226852421 505993421913036042534829)
                  ·
                    refine ⟨189747533217388515950561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505993421913036042534829 189747533217388515950561)
                    ·
                      refine ⟨142310649913041386962921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189747533217388515950561 142310649913041386962921)
                      ·
                        rfl

theorem cell23_277149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_277149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277149 prefixEnd_277149 := by exact prefixLift 277149
  have htrace : WordTrace (prefixWord ++ tailWord_277149) baseStart_277149 baseEnd_277149 := by
    simpa [prefixWord, tailWord_277149, baseEnd_277149] using wordTrace_append hprefix tailTrace_277149
  have hstable : (prefixWord ++ tailWord_277149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277149).length < 2 ^ (prefixWord ++ tailWord_277149).sum := by decide
  have hdescent : baseEnd_277149 < baseStart_277149 := by decide
  rcases family_descends (prefixWord ++ tailWord_277149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277173 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_277173 : Nat := 118140960795 + 277173 * 2 ^ 59
def prefixEnd_277173 : Nat := 4983230072969 + 3 ^ 40 * 277173 * 2
def baseEnd_277173 : Nat := 142322973448749293062811

theorem tailTrace_277173 : CollatzResearch.WordTrace tailWord_277173 prefixEnd_277173 142322973448749293062811 := by
  unfold tailWord_277173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10109329824857033224788173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6739553216571355483192115 10109329824857033224788173)
  ·
    refine ⟨3790998684321387459295565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10109329824857033224788173 3790998684321387459295565)
    ·
      refine ⟨1421624506620520297235837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3790998684321387459295565 1421624506620520297235837)
      ·
        refine ⟨533109189982695111463439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1421624506620520297235837 533109189982695111463439)
        ·
          refine ⟨799663784974042667195159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533109189982695111463439 799663784974042667195159)
          ·
            refine ⟨1199495677461064000792739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799663784974042667195159 1199495677461064000792739)
            ·
              refine ⟨1799243516191596001189109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199495677461064000792739 1799243516191596001189109)
              ·
                refine ⟨168679079642962125111479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1799243516191596001189109 168679079642962125111479)
                ·
                  refine ⟨253018619464443187667219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168679079642962125111479 253018619464443187667219)
                  ·
                    refine ⟨379527929196664781500829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253018619464443187667219 379527929196664781500829)
                    ·
                      refine ⟨142322973448749293062811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379527929196664781500829 142322973448749293062811)
                      ·
                        rfl

theorem cell23_277173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_277173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277173 prefixEnd_277173 := by exact prefixLift 277173
  have htrace : WordTrace (prefixWord ++ tailWord_277173) baseStart_277173 baseEnd_277173 := by
    simpa [prefixWord, tailWord_277173, baseEnd_277173] using wordTrace_append hprefix tailTrace_277173
  have hstable : (prefixWord ++ tailWord_277173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277173).length < 2 ^ (prefixWord ++ tailWord_277173).sum := by decide
  have hdescent : baseEnd_277173 < baseStart_277173 := by decide
  rcases family_descends (prefixWord ++ tailWord_277173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277195 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_277195 : Nat := 118140960795 + 277195 * 2 ^ 59
def prefixEnd_277195 : Nat := 4983230072969 + 3 ^ 40 * 277195 * 2
def baseEnd_277195 : Nat := 142334270023148206987709

theorem tailTrace_277195 : CollatzResearch.WordTrace tailWord_277195 prefixEnd_277195 142334270023148206987709 := by
  unfold tailWord_277195
  simp only [CollatzResearch.WordTrace]
  refine ⟨10110132230777330982089039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6740088153851553988059359 10110132230777330982089039)
  ·
    refine ⟨15165198346165996473133559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10110132230777330982089039 15165198346165996473133559)
    ·
      refine ⟨22747797519248994709700339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15165198346165996473133559 22747797519248994709700339)
      ·
        refine ⟨34121696278873492064550509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22747797519248994709700339 34121696278873492064550509)
        ·
          refine ⟨12795636104577559524206441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34121696278873492064550509 12795636104577559524206441)
          ·
            refine ⟨9596727078433169643154831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12795636104577559524206441 9596727078433169643154831)
            ·
              refine ⟨14395090617649754464732247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9596727078433169643154831 14395090617649754464732247)
              ·
                refine ⟨21592635926474631697098371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14395090617649754464732247 21592635926474631697098371)
                ·
                  refine ⟨32388953889711947545647557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21592635926474631697098371 32388953889711947545647557)
                  ·
                    refine ⟨6072928854320990164808917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32388953889711947545647557 6072928854320990164808917)
                    ·
                      refine ⟨142334270023148206987709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6072928854320990164808917 142334270023148206987709)
                      ·
                        rfl

theorem cell23_277195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_277195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277195 prefixEnd_277195 := by exact prefixLift 277195
  have htrace : WordTrace (prefixWord ++ tailWord_277195) baseStart_277195 baseEnd_277195 := by
    simpa [prefixWord, tailWord_277195, baseEnd_277195] using wordTrace_append hprefix tailTrace_277195
  have hstable : (prefixWord ++ tailWord_277195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277195).length < 2 ^ (prefixWord ++ tailWord_277195).sum := by decide
  have hdescent : baseEnd_277195 < baseStart_277195 := by decide
  rcases family_descends (prefixWord ++ tailWord_277195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277219 : List Nat := [1, 1, 1, 7, 1, 1, 4, 7]
def baseStart_277219 : Nat := 118140960795 + 277219 * 2 ^ 59
def prefixEnd_277219 : Nat := 4983230072969 + 3 ^ 40 * 277219 * 2
def baseEnd_277219 : Nat := 5272096057735411595837

theorem tailTrace_277219 : CollatzResearch.WordTrace tailWord_277219 prefixEnd_277219 5272096057735411595837 := by
  unfold tailWord_277219
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111007582690383080962711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6740671721793588720641807 10111007582690383080962711)
  ·
    refine ⟨15166511374035574621444067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10111007582690383080962711 15166511374035574621444067)
    ·
      refine ⟨22749767061053361932166101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15166511374035574621444067 22749767061053361932166101)
      ·
        refine ⟨533197665493438170285143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 22749767061053361932166101 533197665493438170285143)
        ·
          refine ⟨799796498240157255427715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533197665493438170285143 799796498240157255427715)
          ·
            refine ⟨1199694747360235883141573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799796498240157255427715 1199694747360235883141573)
            ·
              refine ⟨224942765130044228089045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1199694747360235883141573 224942765130044228089045)
              ·
                refine ⟨5272096057735411595837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 224942765130044228089045 5272096057735411595837)
                ·
                  rfl

theorem cell23_277219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 7].length) (baseStart_277219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277219 prefixEnd_277219 := by exact prefixLift 277219
  have htrace : WordTrace (prefixWord ++ tailWord_277219) baseStart_277219 baseEnd_277219 := by
    simpa [prefixWord, tailWord_277219, baseEnd_277219] using wordTrace_append hprefix tailTrace_277219
  have hstable : (prefixWord ++ tailWord_277219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277219).length < 2 ^ (prefixWord ++ tailWord_277219).sum := by decide
  have hdescent : baseEnd_277219 < baseStart_277219 := by decide
  rcases family_descends (prefixWord ++ tailWord_277219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277229 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_277229 : Nat := 118140960795 + 277229 * 2 ^ 59
def prefixEnd_277229 : Nat := 4983230072969 + 3 ^ 40 * 277229 * 2
def baseEnd_277229 : Nat := 142351728365401073962553

theorem tailTrace_277229 : CollatzResearch.WordTrace tailWord_277229 prefixEnd_277229 142351728365401073962553 := by
  unfold tailWord_277229
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111372312654154788826741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6740914875102769859217827 10111372312654154788826741)
  ·
    refine ⟨947941154311327011452507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10111372312654154788826741 947941154311327011452507)
    ·
      refine ⟨1421911731466990517178761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947941154311327011452507 1421911731466990517178761)
      ·
        refine ⟨1066433798600242887884071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1421911731466990517178761 1066433798600242887884071)
        ·
          refine ⟨1599650697900364331826107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066433798600242887884071 1599650697900364331826107)
          ·
            refine ⟨2399476046850546497739161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599650697900364331826107 2399476046850546497739161)
            ·
              refine ⟨1799607035137909873304371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2399476046850546497739161 1799607035137909873304371)
              ·
                refine ⟨2699410552706864809956557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799607035137909873304371 2699410552706864809956557)
                ·
                  refine ⟨1012278957265074303733709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2699410552706864809956557 1012278957265074303733709)
                  ·
                    refine ⟨379604608974402863900141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012278957265074303733709 379604608974402863900141)
                    ·
                      refine ⟨142351728365401073962553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379604608974402863900141 142351728365401073962553)
                      ·
                        rfl

theorem cell23_277229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_277229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277229 prefixEnd_277229 := by exact prefixLift 277229
  have htrace : WordTrace (prefixWord ++ tailWord_277229) baseStart_277229 baseEnd_277229 := by
    simpa [prefixWord, tailWord_277229, baseEnd_277229] using wordTrace_append hprefix tailTrace_277229
  have hstable : (prefixWord ++ tailWord_277229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277229).length < 2 ^ (prefixWord ++ tailWord_277229).sum := by decide
  have hdescent : baseEnd_277229 < baseStart_277229 := by decide
  rcases family_descends (prefixWord ++ tailWord_277229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277230 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_277230 : Nat := 118140960795 + 277230 * 2 ^ 59
def prefixEnd_277230 : Nat := 4983230072969 + 3 ^ 40 * 277230 * 2
def baseEnd_277230 : Nat := 142352241846055570050049

theorem tailTrace_277230 : CollatzResearch.WordTrace tailWord_277230 prefixEnd_277230 142352241846055570050049 := by
  unfold tailWord_277230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263926098206316494951643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6740939190433687973075429 1263926098206316494951643)
  ·
    refine ⟨1895889147309474742427465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1263926098206316494951643 1895889147309474742427465)
    ·
      refine ⟨1421916860482106056820599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1895889147309474742427465 1421916860482106056820599)
      ·
        refine ⟨2132875290723159085230899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421916860482106056820599 2132875290723159085230899)
        ·
          refine ⟨3199312936084738627846349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132875290723159085230899 3199312936084738627846349)
          ·
            refine ⟨1199742351031776985442381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3199312936084738627846349 1199742351031776985442381)
            ·
              refine ⟨449903381636916369540893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1199742351031776985442381 449903381636916369540893)
              ·
                refine ⟨168713768113843638577835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449903381636916369540893 168713768113843638577835)
                ·
                  refine ⟨253070652170765457866753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168713768113843638577835 253070652170765457866753)
                  ·
                    refine ⟨189802989128074093400065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253070652170765457866753 189802989128074093400065)
                    ·
                      refine ⟨142352241846055570050049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189802989128074093400065 142352241846055570050049)
                      ·
                        rfl

theorem cell23_277230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_277230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277230 prefixEnd_277230 := by exact prefixLift 277230
  have htrace : WordTrace (prefixWord ++ tailWord_277230) baseStart_277230 baseEnd_277230 := by
    simpa [prefixWord, tailWord_277230, baseEnd_277230] using wordTrace_append hprefix tailTrace_277230
  have hstable : (prefixWord ++ tailWord_277230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277230).length < 2 ^ (prefixWord ++ tailWord_277230).sum := by decide
  have hdescent : baseEnd_277230 < baseStart_277230 := by decide
  rcases family_descends (prefixWord ++ tailWord_277230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277239 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_277239 : Nat := 118140960795 + 277239 * 2 ^ 59
def prefixEnd_277239 : Nat := 4983230072969 + 3 ^ 40 * 277239 * 2
def baseEnd_277239 : Nat := 142356863171946034837507

theorem tailTrace_277239 : CollatzResearch.WordTrace tailWord_277239 prefixEnd_277239 142356863171946034837507 := by
  unfold tailWord_277239
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111737042617926496690771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6741158028411950997793847 10111737042617926496690771)
  ·
    refine ⟨15167605563926889745036157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10111737042617926496690771 15167605563926889745036157)
    ·
      refine ⟨5687852086472583654388559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15167605563926889745036157 5687852086472583654388559)
      ·
        refine ⟨8531778129708875481582839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687852086472583654388559 8531778129708875481582839)
        ·
          refine ⟨12797667194563313222374259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531778129708875481582839 12797667194563313222374259)
          ·
            refine ⟨19196500791844969833561389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12797667194563313222374259 19196500791844969833561389)
            ·
              refine ⟨7198687796941863687585521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19196500791844969833561389 7198687796941863687585521)
              ·
                refine ⟨5399015847706397765689141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7198687796941863687585521 5399015847706397765689141)
                ·
                  refine ⟨506157735722474790533357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5399015847706397765689141 506157735722474790533357)
                  ·
                    refine ⟨189809150895928046450009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506157735722474790533357 189809150895928046450009)
                    ·
                      refine ⟨142356863171946034837507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189809150895928046450009 142356863171946034837507)
                      ·
                        rfl

theorem cell23_277239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_277239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277239 prefixEnd_277239 := by exact prefixLift 277239
  have htrace : WordTrace (prefixWord ++ tailWord_277239) baseStart_277239 baseEnd_277239 := by
    simpa [prefixWord, tailWord_277239, baseEnd_277239] using wordTrace_append hprefix tailTrace_277239
  have hstable : (prefixWord ++ tailWord_277239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277239).length < 2 ^ (prefixWord ++ tailWord_277239).sum := by decide
  have hdescent : baseEnd_277239 < baseStart_277239 := by decide
  rcases family_descends (prefixWord ++ tailWord_277239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277262 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_277262 : Nat := 118140960795 + 277262 * 2 ^ 59
def prefixEnd_277262 : Nat := 4983230072969 + 3 ^ 40 * 277262 * 2
def baseEnd_277262 : Nat := 47456224408999814949967

theorem tailTrace_277262 : CollatzResearch.WordTrace tailWord_277262 prefixEnd_277262 47456224408999814949967 := by
  unfold tailWord_277262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264071990191825178097255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6741717281023067616518693 1264071990191825178097255)
  ·
    refine ⟨1896107985287737767145883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264071990191825178097255 1896107985287737767145883)
    ·
      refine ⟨2844161977931606650718825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896107985287737767145883 2844161977931606650718825)
      ·
        refine ⟨2133121483448704988039119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2844161977931606650718825 2133121483448704988039119)
        ·
          refine ⟨3199682225173057482058679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133121483448704988039119 3199682225173057482058679)
          ·
            refine ⟨4799523337759586223088019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199682225173057482058679 4799523337759586223088019)
            ·
              refine ⟨7199285006639379334632029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799523337759586223088019 7199285006639379334632029)
              ·
                refine ⟨2699731877489767250487011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7199285006639379334632029 2699731877489767250487011)
                ·
                  refine ⟨4049597816234650875730517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699731877489767250487011 4049597816234650875730517)
                  ·
                    refine ⟨47456224408999814949967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4049597816234650875730517 47456224408999814949967)
                    ·
                      rfl

theorem cell23_277262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_277262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277262 prefixEnd_277262 := by exact prefixLift 277262
  have htrace : WordTrace (prefixWord ++ tailWord_277262) baseStart_277262 baseEnd_277262 := by
    simpa [prefixWord, tailWord_277262, baseEnd_277262] using wordTrace_append hprefix tailTrace_277262
  have hstable : (prefixWord ++ tailWord_277262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277262).length < 2 ^ (prefixWord ++ tailWord_277262).sum := by decide
  have hdescent : baseEnd_277262 < baseStart_277262 := by decide
  rcases family_descends (prefixWord ++ tailWord_277262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277303 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_277303 : Nat := 118140960795 + 277303 * 2 ^ 59
def prefixEnd_277303 : Nat := 4983230072969 + 3 ^ 40 * 277303 * 2
def baseEnd_277303 : Nat := 142389725933833784437213

theorem tailTrace_277303 : CollatzResearch.WordTrace tailWord_277303 prefixEnd_277303 142389725933833784437213 := by
  unfold tailWord_277303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10114071314386065427020563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6742714209590710284680375 10114071314386065427020563)
  ·
    refine ⟨15171106971579098140530845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10114071314386065427020563 15171106971579098140530845)
    ·
      refine ⟨5689165114342161802699067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15171106971579098140530845 5689165114342161802699067)
      ·
        refine ⟨8533747671513242704048601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5689165114342161802699067 8533747671513242704048601)
        ·
          refine ⟨6400310753634932028036451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8533747671513242704048601 6400310753634932028036451)
          ·
            refine ⟨9600466130452398042054677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400310753634932028036451 9600466130452398042054677)
            ·
              refine ⟨450021849864956158221313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9600466130452398042054677 450021849864956158221313)
              ·
                refine ⟨337516387398717118665985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450021849864956158221313 337516387398717118665985)
                ·
                  refine ⟨253137290549037838999489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337516387398717118665985 253137290549037838999489)
                  ·
                    refine ⟨189852967911778379249617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253137290549037838999489 189852967911778379249617)
                    ·
                      refine ⟨142389725933833784437213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189852967911778379249617 142389725933833784437213)
                      ·
                        rfl

theorem cell23_277303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_277303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277303 prefixEnd_277303 := by exact prefixLift 277303
  have htrace : WordTrace (prefixWord ++ tailWord_277303) baseStart_277303 baseEnd_277303 := by
    simpa [prefixWord, tailWord_277303, baseEnd_277303] using wordTrace_append hprefix tailTrace_277303
  have hstable : (prefixWord ++ tailWord_277303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277303).length < 2 ^ (prefixWord ++ tailWord_277303).sum := by decide
  have hdescent : baseEnd_277303 < baseStart_277303 := by decide
  rcases family_descends (prefixWord ++ tailWord_277303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277359 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_277359 : Nat := 118140960795 + 277359 * 2 ^ 59
def prefixEnd_277359 : Nat := 4983230072969 + 3 ^ 40 * 277359 * 2
def baseEnd_277359 : Nat := 142418480850485565336955

theorem tailTrace_277359 : CollatzResearch.WordTrace tailWord_277359 prefixEnd_277359 142418480850485565336955 := by
  unfold tailWord_277359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116113802183186991059131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6744075868122124660706087 10116113802183186991059131)
  ·
    refine ⟨15174170703274780486588697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10116113802183186991059131 15174170703274780486588697)
    ·
      refine ⟨11380628027456085364941523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15174170703274780486588697 11380628027456085364941523)
      ·
        refine ⟨17070942041184128047412285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11380628027456085364941523 17070942041184128047412285)
        ·
          refine ⟨6401603265444048017779607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17070942041184128047412285 6401603265444048017779607)
          ·
            refine ⟨9602404898166072026669411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6401603265444048017779607 9602404898166072026669411)
            ·
              refine ⟨14403607347249108040004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9602404898166072026669411 14403607347249108040004117)
              ·
                refine ⟨675169094402301939375193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14403607347249108040004117 675169094402301939375193)
                ·
                  refine ⟨506376820801726454531395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675169094402301939375193 506376820801726454531395)
                  ·
                    refine ⟨759565231202589681797093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 506376820801726454531395 759565231202589681797093)
                    ·
                      refine ⟨142418480850485565336955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 759565231202589681797093 142418480850485565336955)
                      ·
                        rfl

theorem cell23_277359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_277359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277359 prefixEnd_277359 := by exact prefixLift 277359
  have htrace : WordTrace (prefixWord ++ tailWord_277359) baseStart_277359 baseEnd_277359 := by
    simpa [prefixWord, tailWord_277359, baseEnd_277359] using wordTrace_append hprefix tailTrace_277359
  have hstable : (prefixWord ++ tailWord_277359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277359).length < 2 ^ (prefixWord ++ tailWord_277359).sum := by decide
  have hdescent : baseEnd_277359 < baseStart_277359 := by decide
  rcases family_descends (prefixWord ++ tailWord_277359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277379 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3]
def baseStart_277379 : Nat := 118140960795 + 277379 * 2 ^ 59
def prefixEnd_277379 : Nat := 4983230072969 + 3 ^ 40 * 277379 * 2
def baseEnd_277379 : Nat := 142428750463575487086863

theorem tailTrace_277379 : CollatzResearch.WordTrace tailWord_277379 prefixEnd_277379 142428750463575487086863 := by
  unfold tailWord_277379
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116843262110730406787191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6744562174740486937858127 10116843262110730406787191)
  ·
    refine ⟨15175264893166095610180787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10116843262110730406787191 15175264893166095610180787)
    ·
      refine ⟨22762897339749143415271181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15175264893166095610180787 22762897339749143415271181)
      ·
        refine ⟨8536086502405928780726693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22762897339749143415271181 8536086502405928780726693)
        ·
          refine ⟨1600516219201111646386255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8536086502405928780726693 1600516219201111646386255)
          ·
            refine ⟨2400774328801667469579383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600516219201111646386255 2400774328801667469579383)
            ·
              refine ⟨3601161493202501204369075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400774328801667469579383 3601161493202501204369075)
              ·
                refine ⟨5401742239803751806553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601161493202501204369075 5401742239803751806553613)
                ·
                  refine ⟨2025653339926406927457605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5401742239803751806553613 2025653339926406927457605)
                  ·
                    refine ⟨379810001236201298898301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025653339926406927457605 379810001236201298898301)
                    ·
                      refine ⟨142428750463575487086863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379810001236201298898301 142428750463575487086863)
                      ·
                        rfl

theorem cell23_277379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_277379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277379 prefixEnd_277379 := by exact prefixLift 277379
  have htrace : WordTrace (prefixWord ++ tailWord_277379) baseStart_277379 baseEnd_277379 := by
    simpa [prefixWord, tailWord_277379, baseEnd_277379] using wordTrace_append hprefix tailTrace_277379
  have hstable : (prefixWord ++ tailWord_277379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277379).length < 2 ^ (prefixWord ++ tailWord_277379).sum := by decide
  have hdescent : baseEnd_277379 < baseStart_277379 := by decide
  rcases family_descends (prefixWord ++ tailWord_277379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277396 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_277396 : Nat := 118140960795 + 277396 * 2 ^ 59
def prefixEnd_277396 : Nat := 4983230072969 + 3 ^ 40 * 277396 * 2
def baseEnd_277396 : Nat := 142437479634701920574285

theorem tailTrace_277396 : CollatzResearch.WordTrace tailWord_277396 prefixEnd_277396 142437479634701920574285 := by
  unfold tailWord_277396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5058731651524571155078021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6744975535366094873437361 5058731651524571155078021)
  ·
    refine ⟨948512184660857091577129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5058731651524571155078021 948512184660857091577129)
    ·
      refine ⟨711384138495642818682847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948512184660857091577129 711384138495642818682847)
      ·
        refine ⟨1067076207743464228024271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711384138495642818682847 1067076207743464228024271)
        ·
          refine ⟨1600614311615196342036407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067076207743464228024271 1600614311615196342036407)
          ·
            refine ⟨2400921467422794513054611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600614311615196342036407 2400921467422794513054611)
            ·
              refine ⟨3601382201134191769581917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400921467422794513054611 3601382201134191769581917)
              ·
                refine ⟨1350518325425321913593219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3601382201134191769581917 1350518325425321913593219)
                ·
                  refine ⟨2025777488137982870389829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350518325425321913593219 2025777488137982870389829)
                  ·
                    refine ⟨379833279025871788198093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025777488137982870389829 379833279025871788198093)
                    ·
                      refine ⟨142437479634701920574285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 379833279025871788198093 142437479634701920574285)
                      ·
                        rfl

theorem cell23_277396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_277396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277396 prefixEnd_277396 := by exact prefixLift 277396
  have htrace : WordTrace (prefixWord ++ tailWord_277396) baseStart_277396 baseEnd_277396 := by
    simpa [prefixWord, tailWord_277396, baseEnd_277396] using wordTrace_append hprefix tailTrace_277396
  have hstable : (prefixWord ++ tailWord_277396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277396).length < 2 ^ (prefixWord ++ tailWord_277396).sum := by decide
  have hdescent : baseEnd_277396 < baseStart_277396 := by decide
  rcases family_descends (prefixWord ++ tailWord_277396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277433 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 6]
def baseStart_277433 : Nat := 118140960795 + 277433 * 2 ^ 59
def prefixEnd_277433 : Nat := 4983230072969 + 3 ^ 40 * 277433 * 2
def baseEnd_277433 : Nat := 15828497602102030645735

theorem tailTrace_277433 : CollatzResearch.WordTrace tailWord_277433 prefixEnd_277433 15828497602102030645735 := by
  unfold tailWord_277433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10118812803915097629252953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6745875202610065086168635 10118812803915097629252953)
  ·
    refine ⟨7589109602936323221939715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10118812803915097629252953 7589109602936323221939715)
    ·
      refine ⟨11383664404404484832909573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7589109602936323221939715 11383664404404484832909573)
      ·
        refine ⟨2134437075825840906170545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11383664404404484832909573 2134437075825840906170545)
        ·
          refine ⟨1600827806869380679627909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134437075825840906170545 1600827806869380679627909)
          ·
            refine ⟨300155213788008877430233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1600827806869380679627909 300155213788008877430233)
            ·
              refine ⟨225116410341006658072675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300155213788008877430233 225116410341006658072675)
              ·
                refine ⟨337674615511509987109013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225116410341006658072675 337674615511509987109013)
                ·
                  refine ⟨15828497602102030645735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 337674615511509987109013 15828497602102030645735)
                  ·
                    rfl

theorem cell23_277433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 6].length) (baseStart_277433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277433 prefixEnd_277433 := by exact prefixLift 277433
  have htrace : WordTrace (prefixWord ++ tailWord_277433) baseStart_277433 baseEnd_277433 := by
    simpa [prefixWord, tailWord_277433, baseEnd_277433] using wordTrace_append hprefix tailTrace_277433
  have hstable : (prefixWord ++ tailWord_277433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277433).length < 2 ^ (prefixWord ++ tailWord_277433).sum := by decide
  have hdescent : baseEnd_277433 < baseStart_277433 := by decide
  rcases family_descends (prefixWord ++ tailWord_277433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277500 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_277500 : Nat := 118140960795 + 277500 * 2 ^ 59
def prefixEnd_277500 : Nat := 4983230072969 + 3 ^ 40 * 277500 * 2
def baseEnd_277500 : Nat := 142490881622769513673807

theorem tailTrace_277500 : CollatzResearch.WordTrace tailWord_277500 prefixEnd_277500 142490881622769513673807 := by
  unfold tailWord_277500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060628247336184035970977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6747504329781578714627969 5060628247336184035970977)
  ·
    refine ⟨3795471185502138026978233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5060628247336184035970977 3795471185502138026978233)
    ·
      refine ⟨2846603389126603520233675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3795471185502138026978233 2846603389126603520233675)
      ·
        refine ⟨4269905083689905280350513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846603389126603520233675 4269905083689905280350513)
        ·
          refine ⟨3202428812767428960262885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269905083689905280350513 3202428812767428960262885)
          ·
            refine ⟨600455402393892930049291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3202428812767428960262885 600455402393892930049291)
            ·
              refine ⟨900683103590839395073937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600455402393892930049291 900683103590839395073937)
              ·
                refine ⟨675512327693129546305453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900683103590839395073937 675512327693129546305453)
                ·
                  refine ⟨253317122884923579864545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 675512327693129546305453 253317122884923579864545)
                  ·
                    refine ⟨189987842163692684898409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253317122884923579864545 189987842163692684898409)
                    ·
                      refine ⟨142490881622769513673807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 189987842163692684898409 142490881622769513673807)
                      ·
                        rfl

theorem cell23_277500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_277500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277500 prefixEnd_277500 := by exact prefixLift 277500
  have htrace : WordTrace (prefixWord ++ tailWord_277500) baseStart_277500 baseEnd_277500 := by
    simpa [prefixWord, tailWord_277500, baseEnd_277500] using wordTrace_append hprefix tailTrace_277500
  have hstable : (prefixWord ++ tailWord_277500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277500).length < 2 ^ (prefixWord ++ tailWord_277500).sum := by decide
  have hdescent : baseEnd_277500 < baseStart_277500 := by decide
  rcases family_descends (prefixWord ++ tailWord_277500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277560 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_277560 : Nat := 118140960795 + 277560 * 2 ^ 59
def prefixEnd_277560 : Nat := 4983230072969 + 3 ^ 40 * 277560 * 2
def baseEnd_277560 : Nat := 142521690462039278923531

theorem tailTrace_277560 : CollatzResearch.WordTrace tailWord_277560 prefixEnd_277560 142521690462039278923531 := by
  unfold tailWord_277560
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061722437227499159563067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6748963249636665546084089 5061722437227499159563067)
  ·
    refine ⟨7592583655841248739344601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5061722437227499159563067 7592583655841248739344601)
    ·
      refine ⟨5694437741880936554508451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7592583655841248739344601 5694437741880936554508451)
      ·
        refine ⟨8541656612821404831762677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694437741880936554508451 8541656612821404831762677)
        ·
          refine ⟨800780307452006702977751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8541656612821404831762677 800780307452006702977751)
          ·
            refine ⟨1201170461178010054466627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800780307452006702977751 1201170461178010054466627)
            ·
              refine ⟨1801755691767015081699941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201170461178010054466627 1801755691767015081699941)
              ·
                refine ⟨337829192206315327818739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1801755691767015081699941 337829192206315327818739)
                ·
                  refine ⟨506743788309472991728109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337829192206315327818739 506743788309472991728109)
                  ·
                    refine ⟨190028920616052371898041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506743788309472991728109 190028920616052371898041)
                    ·
                      refine ⟨142521690462039278923531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190028920616052371898041 142521690462039278923531)
                      ·
                        rfl

theorem cell23_277560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_277560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277560 prefixEnd_277560 := by exact prefixLift 277560
  have htrace : WordTrace (prefixWord ++ tailWord_277560) baseStart_277560 baseEnd_277560 := by
    simpa [prefixWord, tailWord_277560, baseEnd_277560] using wordTrace_append hprefix tailTrace_277560
  have hstable : (prefixWord ++ tailWord_277560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277560).length < 2 ^ (prefixWord ++ tailWord_277560).sum := by decide
  have hdescent : baseEnd_277560 < baseStart_277560 := by decide
  rcases family_descends (prefixWord ++ tailWord_277560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277573 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_277573 : Nat := 118140960795 + 277573 * 2 ^ 59
def prefixEnd_277573 : Nat := 4983230072969 + 3 ^ 40 * 277573 * 2
def baseEnd_277573 : Nat := 142528365710547728060971

theorem tailTrace_277573 : CollatzResearch.WordTrace tailWord_277573 prefixEnd_277573 142528365710547728060971 := by
  unfold tailWord_277573
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123919023407901539349373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6749279348938601026232915 10123919023407901539349373)
  ·
    refine ⟨3796469633777963077256015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10123919023407901539349373 3796469633777963077256015)
    ·
      refine ⟨5694704450666944615884023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3796469633777963077256015 5694704450666944615884023)
      ·
        refine ⟨8542056676000416923826035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694704450666944615884023 8542056676000416923826035)
        ·
          refine ⟨12813085014000625385739053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542056676000416923826035 12813085014000625385739053)
          ·
            refine ⟨4804906880250234519652145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12813085014000625385739053 4804906880250234519652145)
            ·
              refine ⟨3603680160187675889739109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804906880250234519652145 3603680160187675889739109)
              ·
                refine ⟨675690030035189229326083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3603680160187675889739109 675690030035189229326083)
                ·
                  refine ⟨1013535045052783843989125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675690030035189229326083 1013535045052783843989125)
                  ·
                    refine ⟨190037820947396970747961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013535045052783843989125 190037820947396970747961)
                    ·
                      refine ⟨142528365710547728060971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190037820947396970747961 142528365710547728060971)
                      ·
                        rfl

theorem cell23_277573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_277573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277573 prefixEnd_277573 := by exact prefixLift 277573
  have htrace : WordTrace (prefixWord ++ tailWord_277573) baseStart_277573 baseEnd_277573 := by
    simpa [prefixWord, tailWord_277573, baseEnd_277573] using wordTrace_append hprefix tailTrace_277573
  have hstable : (prefixWord ++ tailWord_277573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277573).length < 2 ^ (prefixWord ++ tailWord_277573).sum := by decide
  have hdescent : baseEnd_277573 < baseStart_277573 := by decide
  rcases family_descends (prefixWord ++ tailWord_277573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277576 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_277576 : Nat := 118140960795 + 277576 * 2 ^ 59
def prefixEnd_277576 : Nat := 4983230072969 + 3 ^ 40 * 277576 * 2
def baseEnd_277576 : Nat := 142529906152511216323457

theorem tailTrace_277576 : CollatzResearch.WordTrace tailWord_277576 prefixEnd_277576 142529906152511216323457 := by
  unfold tailWord_277576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062014221198516525854291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6749352294931355367805721 5062014221198516525854291)
  ·
    refine ⟨7593021331797774788781437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5062014221198516525854291 7593021331797774788781437)
    ·
      refine ⟨2847382999424165545793039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7593021331797774788781437 2847382999424165545793039)
      ·
        refine ⟨4271074499136248318689559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847382999424165545793039 4271074499136248318689559)
        ·
          refine ⟨6406611748704372478034339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271074499136248318689559 6406611748704372478034339)
          ·
            refine ⟨9609917623056558717051509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406611748704372478034339 9609917623056558717051509)
            ·
              refine ⟨900929777161552379723579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9609917623056558717051509 900929777161552379723579)
              ·
                refine ⟨1351394665742328569585369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900929777161552379723579 1351394665742328569585369)
                ·
                  refine ⟨1013545999306746427189027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1351394665742328569585369 1013545999306746427189027)
                  ·
                    refine ⟨1520318998960119640783541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1013545999306746427189027 1520318998960119640783541)
                    ·
                      refine ⟨142529906152511216323457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1520318998960119640783541 142529906152511216323457)
                      ·
                        rfl

theorem cell23_277576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_277576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277576 prefixEnd_277576 := by exact prefixLift 277576
  have htrace : WordTrace (prefixWord ++ tailWord_277576) baseStart_277576 baseEnd_277576 := by
    simpa [prefixWord, tailWord_277576, baseEnd_277576] using wordTrace_append hprefix tailTrace_277576
  have hstable : (prefixWord ++ tailWord_277576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277576).length < 2 ^ (prefixWord ++ tailWord_277576).sum := by decide
  have hdescent : baseEnd_277576 < baseStart_277576 := by decide
  rcases family_descends (prefixWord ++ tailWord_277576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277607 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_277607 : Nat := 118140960795 + 277607 * 2 ^ 59
def prefixEnd_277607 : Nat := 4983230072969 + 3 ^ 40 * 277607 * 2
def baseEnd_277607 : Nat := 142545824052800595035815

theorem tailTrace_277607 : CollatzResearch.WordTrace tailWord_277607 prefixEnd_277607 142545824052800595035815 := by
  unfold tailWord_277607
  simp only [CollatzResearch.WordTrace]
  refine ⟨10125159105284725346087075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6750106070189816897391383 10125159105284725346087075)
  ·
    refine ⟨15187738657927088019130613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10125159105284725346087075 15187738657927088019130613)
    ·
      refine ⟨1423850499180664501793495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15187738657927088019130613 1423850499180664501793495)
      ·
        refine ⟨2135775748770996752690243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423850499180664501793495 2135775748770996752690243)
        ·
          refine ⟨3203663623156495129035365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135775748770996752690243 3203663623156495129035365)
          ·
            refine ⟨600686929341842836694131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3203663623156495129035365 600686929341842836694131)
            ·
              refine ⟨901030394012764255041197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600686929341842836694131 901030394012764255041197)
              ·
                refine ⟨337886397754786595640449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 901030394012764255041197 337886397754786595640449)
                ·
                  refine ⟨253414798316089946730337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337886397754786595640449 253414798316089946730337)
                  ·
                    refine ⟨190061098737067460047753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253414798316089946730337 190061098737067460047753)
                    ·
                      refine ⟨142545824052800595035815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190061098737067460047753 142545824052800595035815)
                      ·
                        rfl

theorem cell23_277607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_277607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277607 prefixEnd_277607 := by exact prefixLift 277607
  have htrace : WordTrace (prefixWord ++ tailWord_277607) baseStart_277607 baseEnd_277607 := by
    simpa [prefixWord, tailWord_277607, baseEnd_277607] using wordTrace_append hprefix tailTrace_277607
  have hstable : (prefixWord ++ tailWord_277607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277607).length < 2 ^ (prefixWord ++ tailWord_277607).sum := by decide
  have hdescent : baseEnd_277607 < baseStart_277607 := by decide
  rcases family_descends (prefixWord ++ tailWord_277607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277650 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_277650 : Nat := 118140960795 + 277650 * 2 ^ 59
def prefixEnd_277650 : Nat := 4983230072969 + 3 ^ 40 * 277650 * 2
def baseEnd_277650 : Nat := 142567903720943926798117

theorem tailTrace_277650 : CollatzResearch.WordTrace tailWord_277650 prefixEnd_277650 142567903720943926798117 := by
  unfold tailWord_277650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531681861032235922475601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6751151629419295793268269 2531681861032235922475601)
  ·
    refine ⟨1898761395774176941856701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2531681861032235922475601 1898761395774176941856701)
    ·
      refine ⟨712035523415316353196263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1898761395774176941856701 712035523415316353196263)
      ·
        refine ⟨1068053285122974529794395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712035523415316353196263 1068053285122974529794395)
        ·
          refine ⟨1602079927684461794691593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068053285122974529794395 1602079927684461794691593)
          ·
            refine ⟨1201559945763346346018695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602079927684461794691593 1201559945763346346018695)
            ·
              refine ⟨1802339918645019519028043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201559945763346346018695 1802339918645019519028043)
              ·
                refine ⟨2703509877967529278542065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802339918645019519028043 2703509877967529278542065)
                ·
                  refine ⟨2027632408475646958906549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703509877967529278542065 2027632408475646958906549)
                  ·
                    refine ⟨190090538294591902397489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2027632408475646958906549 190090538294591902397489)
                    ·
                      refine ⟨142567903720943926798117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190090538294591902397489 142567903720943926798117)
                      ·
                        rfl

theorem cell23_277650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_277650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277650 prefixEnd_277650 := by exact prefixLift 277650
  have htrace : WordTrace (prefixWord ++ tailWord_277650) baseStart_277650 baseEnd_277650 := by
    simpa [prefixWord, tailWord_277650, baseEnd_277650] using wordTrace_append hprefix tailTrace_277650
  have hstable : (prefixWord ++ tailWord_277650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277650).length < 2 ^ (prefixWord ++ tailWord_277650).sum := by decide
  have hdescent : baseEnd_277650 < baseStart_277650 := by decide
  rcases family_descends (prefixWord ++ tailWord_277650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277676 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_277676 : Nat := 118140960795 + 277676 * 2 ^ 59
def prefixEnd_277676 : Nat := 4983230072969 + 3 ^ 40 * 277676 * 2
def baseEnd_277676 : Nat := 142581254217960825072997

theorem tailTrace_277676 : CollatzResearch.WordTrace tailWord_277676 prefixEnd_277676 142581254217960825072997 := by
  unfold tailWord_277676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5063837871017375065174441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6751783828023166753565921 5063837871017375065174441)
  ·
    refine ⟨3797878403263031298880831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5063837871017375065174441 3797878403263031298880831)
    ·
      refine ⟨5696817604894546948321247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797878403263031298880831 5696817604894546948321247)
      ·
        refine ⟨8545226407341820422481871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696817604894546948321247 8545226407341820422481871)
        ·
          refine ⟨12817839611012730633722807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545226407341820422481871 12817839611012730633722807)
          ·
            refine ⟨19226759416519095950584211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12817839611012730633722807 19226759416519095950584211)
            ·
              refine ⟨28840139124778643925876317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19226759416519095950584211 28840139124778643925876317)
              ·
                refine ⟨10815052171791991472203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28840139124778643925876317 10815052171791991472203619)
                ·
                  refine ⟨16222578257687987208305429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10815052171791991472203619 16222578257687987208305429)
                  ·
                    refine ⟨760433355829124400389317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16222578257687987208305429 760433355829124400389317)
                    ·
                      refine ⟨142581254217960825072997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 760433355829124400389317 142581254217960825072997)
                      ·
                        rfl

theorem cell23_277676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_277676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277676 prefixEnd_277676 := by exact prefixLift 277676
  have htrace : WordTrace (prefixWord ++ tailWord_277676) baseStart_277676 baseEnd_277676 := by
    simpa [prefixWord, tailWord_277676, baseEnd_277676] using wordTrace_append hprefix tailTrace_277676
  have hstable : (prefixWord ++ tailWord_277676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277676).length < 2 ^ (prefixWord ++ tailWord_277676).sum := by decide
  have hdescent : baseEnd_277676 < baseStart_277676 := by decide
  rcases family_descends (prefixWord ++ tailWord_277676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277677 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_277677 : Nat := 118140960795 + 277677 * 2 ^ 59
def prefixEnd_277677 : Nat := 4983230072969 + 3 ^ 40 * 277677 * 2
def baseEnd_277677 : Nat := 47527255899538440386831

theorem tailTrace_277677 : CollatzResearch.WordTrace tailWord_277677 prefixEnd_277677 47527255899538440386831 := by
  unfold tailWord_277677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10127712215031127301135285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6751808143354084867423523 10127712215031127301135285)
  ·
    refine ⟨949473020159168184481433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10127712215031127301135285 949473020159168184481433)
    ·
      refine ⟨712104765119376138361075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 949473020159168184481433 712104765119376138361075)
      ·
        refine ⟨1068157147679064207541613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712104765119376138361075 1068157147679064207541613)
        ·
          refine ⟨400558930379649077828105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1068157147679064207541613 400558930379649077828105)
          ·
            refine ⟨300419197784736808371079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400558930379649077828105 300419197784736808371079)
            ·
              refine ⟨450628796677105212556619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300419197784736808371079 450628796677105212556619)
              ·
                refine ⟨675943195015657818834929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450628796677105212556619 675943195015657818834929)
                ·
                  refine ⟨506957396261743364126197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675943195015657818834929 506957396261743364126197)
                  ·
                    refine ⟨47527255899538440386831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 506957396261743364126197 47527255899538440386831)
                    ·
                      rfl

theorem cell23_277677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_277677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277677 prefixEnd_277677 := by exact prefixLift 277677
  have htrace : WordTrace (prefixWord ++ tailWord_277677) baseStart_277677 baseEnd_277677 := by
    simpa [prefixWord, tailWord_277677, baseEnd_277677] using wordTrace_append hprefix tailTrace_277677
  have hstable : (prefixWord ++ tailWord_277677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277677).length < 2 ^ (prefixWord ++ tailWord_277677).sum := by decide
  have hdescent : baseEnd_277677 < baseStart_277677 := by decide
  rcases family_descends (prefixWord ++ tailWord_277677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277697 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_277697 : Nat := 118140960795 + 277697 * 2 ^ 59
def prefixEnd_277697 : Nat := 4983230072969 + 3 ^ 40 * 277697 * 2
def baseEnd_277697 : Nat := 142592037311705242910401

theorem tailTrace_277697 : CollatzResearch.WordTrace tailWord_277697 prefixEnd_277697 142592037311705242910401 := by
  unfold tailWord_277697
  simp only [CollatzResearch.WordTrace]
  refine ⟨10128441674958670716863345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6752294449972447144575563 10128441674958670716863345)
  ·
    refine ⟨7596331256219003037647509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10128441674958670716863345 7596331256219003037647509)
    ·
      refine ⟨356078027635265767389727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7596331256219003037647509 356078027635265767389727)
      ·
        refine ⟨534117041452898651084591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356078027635265767389727 534117041452898651084591)
        ·
          refine ⟨801175562179347976626887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534117041452898651084591 801175562179347976626887)
          ·
            refine ⟨1201763343269021964940331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801175562179347976626887 1201763343269021964940331)
            ·
              refine ⟨1802645014903532947410497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201763343269021964940331 1802645014903532947410497)
              ·
                refine ⟨1351983761177649710557873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802645014903532947410497 1351983761177649710557873)
                ·
                  refine ⟨1013987820883237282918405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1351983761177649710557873 1013987820883237282918405)
                  ·
                    refine ⟨190122716415606990547201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013987820883237282918405 190122716415606990547201)
                    ·
                      refine ⟨142592037311705242910401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190122716415606990547201 142592037311705242910401)
                      ·
                        rfl

theorem cell23_277697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_277697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277697 prefixEnd_277697 := by exact prefixLift 277697
  have htrace : WordTrace (prefixWord ++ tailWord_277697) baseStart_277697 baseEnd_277697 := by
    simpa [prefixWord, tailWord_277697, baseEnd_277697] using wordTrace_append hprefix tailTrace_277697
  have hstable : (prefixWord ++ tailWord_277697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277697).length < 2 ^ (prefixWord ++ tailWord_277697).sum := by decide
  have hdescent : baseEnd_277697 < baseStart_277697 := by decide
  rcases family_descends (prefixWord ++ tailWord_277697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277740 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_277740 : Nat := 118140960795 + 277740 * 2 ^ 59
def prefixEnd_277740 : Nat := 4983230072969 + 3 ^ 40 * 277740 * 2
def baseEnd_277740 : Nat := 142614116979848574672703

theorem tailTrace_277740 : CollatzResearch.WordTrace tailWord_277740 prefixEnd_277740 142614116979848574672703 := by
  unfold tailWord_277740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065005006901444530339337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6753340009201926040452449 5065005006901444530339337)
  ·
    refine ⟨3798753755176083397754503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5065005006901444530339337 3798753755176083397754503)
    ·
      refine ⟨5698130632764125096631755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3798753755176083397754503 5698130632764125096631755)
      ·
        refine ⟨8547195949146187644947633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698130632764125096631755 8547195949146187644947633)
        ·
          refine ⟨6410396961859640733710725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547195949146187644947633 6410396961859640733710725)
          ·
            refine ⟨1201949430348682637570761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6410396961859640733710725 1201949430348682637570761)
            ·
              refine ⟨901462072761511978178071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1201949430348682637570761 901462072761511978178071)
              ·
                refine ⟨1352193109142267967267107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901462072761511978178071 1352193109142267967267107)
                ·
                  refine ⟨2028289663713401950900661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352193109142267967267107 2028289663713401950900661)
                  ·
                    refine ⟨190152155973131432896937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2028289663713401950900661 190152155973131432896937)
                    ·
                      refine ⟨142614116979848574672703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190152155973131432896937 142614116979848574672703)
                      ·
                        rfl

theorem cell23_277740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_277740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277740 prefixEnd_277740 := by exact prefixLift 277740
  have htrace : WordTrace (prefixWord ++ tailWord_277740) baseStart_277740 baseEnd_277740 := by
    simpa [prefixWord, tailWord_277740, baseEnd_277740] using wordTrace_append hprefix tailTrace_277740
  have hstable : (prefixWord ++ tailWord_277740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277740).length < 2 ^ (prefixWord ++ tailWord_277740).sum := by decide
  have hdescent : baseEnd_277740 < baseStart_277740 := by decide
  rcases family_descends (prefixWord ++ tailWord_277740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277764 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_277764 : Nat := 118140960795 + 277764 * 2 ^ 59
def prefixEnd_277764 : Nat := 4983230072969 + 3 ^ 40 * 277764 * 2
def baseEnd_277764 : Nat := 142626440515556480772593

theorem tailTrace_277764 : CollatzResearch.WordTrace tailWord_277764 prefixEnd_277764 142626440515556480772593 := by
  unfold tailWord_277764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065442682857970579776173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6753923577143960773034897 5065442682857970579776173)
  ·
    refine ⟨1899541006071738967416065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5065442682857970579776173 1899541006071738967416065)
    ·
      refine ⟨1424655754553804225562049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1899541006071738967416065 1424655754553804225562049)
      ·
        refine ⟨1068491815915353169171537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1424655754553804225562049 1068491815915353169171537)
        ·
          refine ⟨801368861936514876878653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068491815915353169171537 801368861936514876878653)
          ·
            refine ⟨300513323226193078829495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 801368861936514876878653 300513323226193078829495)
            ·
              refine ⟨450769984839289618244243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300513323226193078829495 450769984839289618244243)
              ·
                refine ⟨676154977258934427366365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450769984839289618244243 676154977258934427366365)
                ·
                  refine ⟨253558116472100410262387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676154977258934427366365 253558116472100410262387)
                  ·
                    refine ⟨380337174708150615393581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253558116472100410262387 380337174708150615393581)
                    ·
                      refine ⟨142626440515556480772593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 380337174708150615393581 142626440515556480772593)
                      ·
                        rfl

theorem cell23_277764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_277764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277764 prefixEnd_277764 := by exact prefixLift 277764
  have htrace : WordTrace (prefixWord ++ tailWord_277764) baseStart_277764 baseEnd_277764 := by
    simpa [prefixWord, tailWord_277764, baseEnd_277764] using wordTrace_append hprefix tailTrace_277764
  have hstable : (prefixWord ++ tailWord_277764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277764).length < 2 ^ (prefixWord ++ tailWord_277764).sum := by decide
  have hdescent : baseEnd_277764 < baseStart_277764 := by decide
  rcases family_descends (prefixWord ++ tailWord_277764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277783 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_277783 : Nat := 118140960795 + 277783 * 2 ^ 59
def prefixEnd_277783 : Nat := 4983230072969 + 3 ^ 40 * 277783 * 2
def baseEnd_277783 : Nat := 142636196647991906435005

theorem tailTrace_277783 : CollatzResearch.WordTrace tailWord_277783 prefixEnd_277783 142636196647991906435005 := by
  unfold tailWord_277783
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131578352647107404494003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6754385568431404936329335 10131578352647107404494003)
  ·
    refine ⟨15197367528970661106741005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10131578352647107404494003 15197367528970661106741005)
    ·
      refine ⟨5699012823363997915027877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15197367528970661106741005 5699012823363997915027877)
      ·
        refine ⟨1068564904380749609067727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5699012823363997915027877 1068564904380749609067727)
        ·
          refine ⟨1602847356571124413601591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068564904380749609067727 1602847356571124413601591)
          ·
            refine ⟨2404271034856686620402387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602847356571124413601591 2404271034856686620402387)
            ·
              refine ⟨3606406552285029930603581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404271034856686620402387 3606406552285029930603581)
              ·
                refine ⟨1352402457106886223976343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3606406552285029930603581 1352402457106886223976343)
                ·
                  refine ⟨2028603685660329335964515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352402457106886223976343 2028603685660329335964515)
                  ·
                    refine ⟨3042905528490494003946773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028603685660329335964515 3042905528490494003946773)
                    ·
                      refine ⟨142636196647991906435005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3042905528490494003946773 142636196647991906435005)
                      ·
                        rfl

theorem cell23_277783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_277783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277783 prefixEnd_277783 := by exact prefixLift 277783
  have htrace : WordTrace (prefixWord ++ tailWord_277783) baseStart_277783 baseEnd_277783 := by
    simpa [prefixWord, tailWord_277783, baseEnd_277783] using wordTrace_append hprefix tailTrace_277783
  have hstable : (prefixWord ++ tailWord_277783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277783).length < 2 ^ (prefixWord ++ tailWord_277783).sum := by decide
  have hdescent : baseEnd_277783 < baseStart_277783 := by decide
  rcases family_descends (prefixWord ++ tailWord_277783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277800 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_277800 : Nat := 118140960795 + 277800 * 2 ^ 59
def prefixEnd_277800 : Nat := 4983230072969 + 3 ^ 40 * 277800 * 2
def baseEnd_277800 : Nat := 142644925819118339922427

theorem tailTrace_277800 : CollatzResearch.WordTrace tailWord_277800 prefixEnd_277800 142644925819118339922427 := by
  unfold tailWord_277800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066099196792759653931427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6754798929057012871908569 5066099196792759653931427)
  ·
    refine ⟨7599148795189139480897141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5066099196792759653931427 7599148795189139480897141)
    ·
      refine ⟨712420199548981826334107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7599148795189139480897141 712420199548981826334107)
      ·
        refine ⟨1068630299323472739501161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712420199548981826334107 1068630299323472739501161)
        ·
          refine ⟨801472724492604554625871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068630299323472739501161 801472724492604554625871)
          ·
            refine ⟨1202209086738906831938807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801472724492604554625871 1202209086738906831938807)
            ·
              refine ⟨1803313630108360247908211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202209086738906831938807 1803313630108360247908211)
              ·
                refine ⟨2704970445162540371862317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803313630108360247908211 2704970445162540371862317)
                ·
                  refine ⟨1014363916935952639448369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2704970445162540371862317 1014363916935952639448369)
                  ·
                    refine ⟨760772937701964479586277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1014363916935952639448369 760772937701964479586277)
                    ·
                      refine ⟨142644925819118339922427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 760772937701964479586277 142644925819118339922427)
                      ·
                        rfl

theorem cell23_277800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_277800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277800 prefixEnd_277800 := by exact prefixLift 277800
  have htrace : WordTrace (prefixWord ++ tailWord_277800) baseStart_277800 baseEnd_277800 := by
    simpa [prefixWord, tailWord_277800, baseEnd_277800] using wordTrace_append hprefix tailTrace_277800
  have hstable : (prefixWord ++ tailWord_277800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277800).length < 2 ^ (prefixWord ++ tailWord_277800).sum := by decide
  have hdescent : baseEnd_277800 < baseStart_277800 := by decide
  rcases family_descends (prefixWord ++ tailWord_277800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277804 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 1, 2, 2]
def baseStart_277804 : Nat := 118140960795 + 277804 * 2 ^ 59
def prefixEnd_277804 : Nat := 4983230072969 + 3 ^ 40 * 277804 * 2
def baseEnd_277804 : Nat := 142646979741736324272409

theorem tailTrace_277804 : CollatzResearch.WordTrace tailWord_277804 prefixEnd_277804 142646979741736324272409 := by
  unfold tailWord_277804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066172142785513995504233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6754896190380685327338977 5066172142785513995504233)
  ·
    refine ⟨3799629107089135496628175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5066172142785513995504233 3799629107089135496628175)
    ·
      refine ⟨5699443660633703244942263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3799629107089135496628175 5699443660633703244942263)
      ·
        refine ⟨8549165490950554867413395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5699443660633703244942263 8549165490950554867413395)
        ·
          refine ⟨12823748236425832301120093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8549165490950554867413395 12823748236425832301120093)
          ·
            refine ⟨4808905588659687112920035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12823748236425832301120093 4808905588659687112920035)
            ·
              refine ⟨7213358382989530669380053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808905588659687112920035 7213358382989530669380053)
              ·
                refine ⟨169063087101317125063595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7213358382989530669380053 169063087101317125063595)
                ·
                  refine ⟨253594630651975687595393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169063087101317125063595 253594630651975687595393)
                  ·
                    refine ⟨190195972988981765696545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253594630651975687595393 190195972988981765696545)
                    ·
                      refine ⟨142646979741736324272409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190195972988981765696545 142646979741736324272409)
                      ·
                        rfl

theorem cell23_277804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_277804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277804 prefixEnd_277804 := by exact prefixLift 277804
  have htrace : WordTrace (prefixWord ++ tailWord_277804) baseStart_277804 baseEnd_277804 := by
    simpa [prefixWord, tailWord_277804, baseEnd_277804] using wordTrace_append hprefix tailTrace_277804
  have hstable : (prefixWord ++ tailWord_277804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277804).length < 2 ^ (prefixWord ++ tailWord_277804).sum := by decide
  have hdescent : baseEnd_277804 < baseStart_277804 := by decide
  rcases family_descends (prefixWord ++ tailWord_277804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277823 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 7]
def baseStart_277823 : Nat := 118140960795 + 277823 * 2 ^ 59
def prefixEnd_277823 : Nat := 4983230072969 + 3 ^ 40 * 277823 * 2
def baseEnd_277823 : Nat := 47552245291390583311607

theorem tailTrace_277823 : CollatzResearch.WordTrace tailWord_277823 prefixEnd_277823 47552245291390583311607 := by
  unfold tailWord_277823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133037272502194235950123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6755358181668129490633415 10133037272502194235950123)
  ·
    refine ⟨15199555908753291353925185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133037272502194235950123 15199555908753291353925185)
    ·
      refine ⟨11399666931564968515443889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15199555908753291353925185 11399666931564968515443889)
      ·
        refine ⟨8549750198673726386582917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11399666931564968515443889 8549750198673726386582917)
        ·
          refine ⟨1603078162251323697484297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8549750198673726386582917 1603078162251323697484297)
          ·
            refine ⟨1202308621688492773113223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603078162251323697484297 1202308621688492773113223)
            ·
              refine ⟨1803462932532739159669835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202308621688492773113223 1803462932532739159669835)
              ·
                refine ⟨2705194398799108739504753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803462932532739159669835 2705194398799108739504753)
                ·
                  refine ⟨2028895799099331554628565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705194398799108739504753 2028895799099331554628565)
                  ·
                    refine ⟨47552245291390583311607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2028895799099331554628565 47552245291390583311607)
                    ·
                      rfl

theorem cell23_277823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_277823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277823 prefixEnd_277823 := by exact prefixLift 277823
  have htrace : WordTrace (prefixWord ++ tailWord_277823) baseStart_277823 baseEnd_277823 := by
    simpa [prefixWord, tailWord_277823, baseEnd_277823] using wordTrace_append hprefix tailTrace_277823
  have hstable : (prefixWord ++ tailWord_277823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277823).length < 2 ^ (prefixWord ++ tailWord_277823).sum := by decide
  have hdescent : baseEnd_277823 < baseStart_277823 := by decide
  rcases family_descends (prefixWord ++ tailWord_277823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277843 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_277843 : Nat := 118140960795 + 277843 * 2 ^ 59
def prefixEnd_277843 : Nat := 4983230072969 + 3 ^ 40 * 277843 * 2
def baseEnd_277843 : Nat := 142667005487261671684729

theorem tailTrace_277843 : CollatzResearch.WordTrace tailWord_277843 prefixEnd_277843 142667005487261671684729 := by
  unfold tailWord_277843
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133766732429737651678183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6755844488286491767785455 10133766732429737651678183)
  ·
    refine ⟨15200650098644606477517275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133766732429737651678183 15200650098644606477517275)
    ·
      refine ⟨22800975147966909716275913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15200650098644606477517275 22800975147966909716275913)
      ·
        refine ⟨17100731360975182287206935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22800975147966909716275913 17100731360975182287206935)
        ·
          refine ⟨25651097041462773430810403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17100731360975182287206935 25651097041462773430810403)
          ·
            refine ⟨38476645562194160146215605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25651097041462773430810403 38476645562194160146215605)
            ·
              refine ⟨3607185521455702513707713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38476645562194160146215605 3607185521455702513707713)
              ·
                refine ⟨2705389141091776885280785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3607185521455702513707713 2705389141091776885280785)
                ·
                  refine ⟨2029041855818832663960589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705389141091776885280785 2029041855818832663960589)
                  ·
                    refine ⟨760890695932062248985221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2029041855818832663960589 760890695932062248985221)
                    ·
                      refine ⟨142667005487261671684729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 760890695932062248985221 142667005487261671684729)
                      ·
                        rfl

theorem cell23_277843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_277843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277843 prefixEnd_277843 := by exact prefixLift 277843
  have htrace : WordTrace (prefixWord ++ tailWord_277843) baseStart_277843 baseEnd_277843 := by
    simpa [prefixWord, tailWord_277843, baseEnd_277843] using wordTrace_append hprefix tailTrace_277843
  have hstable : (prefixWord ++ tailWord_277843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277843).length < 2 ^ (prefixWord ++ tailWord_277843).sum := by decide
  have hdescent : baseEnd_277843 < baseStart_277843 := by decide
  rcases family_descends (prefixWord ++ tailWord_277843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277847 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_277847 : Nat := 118140960795 + 277847 * 2 ^ 59
def prefixEnd_277847 : Nat := 4983230072969 + 3 ^ 40 * 277847 * 2
def baseEnd_277847 : Nat := 142669059409879656034711

theorem tailTrace_277847 : CollatzResearch.WordTrace tailWord_277847 prefixEnd_277847 142669059409879656034711 := by
  unfold tailWord_277847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133912624415246334823795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6755941749610164223215863 10133912624415246334823795)
  ·
    refine ⟨15200868936622869502235693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10133912624415246334823795 15200868936622869502235693)
    ·
      refine ⟨5700325851233576063338385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15200868936622869502235693 5700325851233576063338385)
      ·
        refine ⟨4275244388425182047503789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5700325851233576063338385 4275244388425182047503789)
        ·
          refine ⟨1603216645659443267813921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4275244388425182047503789 1603216645659443267813921)
          ·
            refine ⟨1202412484244582450860441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603216645659443267813921 1202412484244582450860441)
            ·
              refine ⟨901809363183436838145331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202412484244582450860441 901809363183436838145331)
              ·
                refine ⟨1352714044775155257217997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901809363183436838145331 1352714044775155257217997)
                ·
                  refine ⟨507267766790683221456749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1352714044775155257217997 507267766790683221456749)
                  ·
                    refine ⟨190225412546506208046281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507267766790683221456749 190225412546506208046281)
                    ·
                      refine ⟨142669059409879656034711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190225412546506208046281 142669059409879656034711)
                      ·
                        rfl

theorem cell23_277847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_277847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277847 prefixEnd_277847 := by exact prefixLift 277847
  have htrace : WordTrace (prefixWord ++ tailWord_277847) baseStart_277847 baseEnd_277847 := by
    simpa [prefixWord, tailWord_277847, baseEnd_277847] using wordTrace_append hprefix tailTrace_277847
  have hstable : (prefixWord ++ tailWord_277847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277847).length < 2 ^ (prefixWord ++ tailWord_277847).sum := by decide
  have hdescent : baseEnd_277847 < baseStart_277847 := by decide
  rcases family_descends (prefixWord ++ tailWord_277847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277937 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_277937 : Nat := 118140960795 + 277937 * 2 ^ 59
def prefixEnd_277937 : Nat := 4983230072969 + 3 ^ 40 * 277937 * 2
def baseEnd_277937 : Nat := 142715272668784303909297

theorem tailTrace_277937 : CollatzResearch.WordTrace tailWord_277937 prefixEnd_277937 142715272668784303909297 := by
  unfold tailWord_277937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137195194089191705600065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6758130129392794470400043 10137195194089191705600065)
  ·
    refine ⟨7602896395566893779200049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10137195194089191705600065 7602896395566893779200049)
    ·
      refine ⟨5702172296675170334400037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7602896395566893779200049 5702172296675170334400037)
      ·
        refine ⟨1069157305626594437700007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5702172296675170334400037 1069157305626594437700007)
        ·
          refine ⟨1603735958439891656550011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069157305626594437700007 1603735958439891656550011)
          ·
            refine ⟨2405603937659837484825017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603735958439891656550011 2405603937659837484825017)
            ·
              refine ⟨1804202953244878113618763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405603937659837484825017 1804202953244878113618763)
              ·
                refine ⟨2706304429867317170428145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804202953244878113618763 2706304429867317170428145)
                ·
                  refine ⟨2029728322400487877821109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706304429867317170428145 2029728322400487877821109)
                  ·
                    refine ⟨190287030225045738545729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2029728322400487877821109 190287030225045738545729)
                    ·
                      refine ⟨142715272668784303909297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190287030225045738545729 142715272668784303909297)
                      ·
                        rfl

theorem cell23_277937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_277937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277937 prefixEnd_277937 := by exact prefixLift 277937
  have htrace : WordTrace (prefixWord ++ tailWord_277937) baseStart_277937 baseEnd_277937 := by
    simpa [prefixWord, tailWord_277937, baseEnd_277937] using wordTrace_append hprefix tailTrace_277937
  have hstable : (prefixWord ++ tailWord_277937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277937).length < 2 ^ (prefixWord ++ tailWord_277937).sum := by decide
  have hdescent : baseEnd_277937 < baseStart_277937 := by decide
  rcases family_descends (prefixWord ++ tailWord_277937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277945 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 2, 2, 2]
def baseStart_277945 : Nat := 118140960795 + 277945 * 2 ^ 59
def prefixEnd_277945 : Nat := 4983230072969 + 3 ^ 40 * 277945 * 2
def baseEnd_277945 : Nat := 142719380514020272609261

theorem tailTrace_277945 : CollatzResearch.WordTrace tailWord_277945 prefixEnd_277945 142719380514020272609261 := by
  unfold tailWord_277945
  simp only [CollatzResearch.WordTrace]
  refine ⟨10137486978060209071891289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6758324652040139381260859 10137486978060209071891289)
  ·
    refine ⟨7603115233545156803918467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10137486978060209071891289 7603115233545156803918467)
    ·
      refine ⟨11404672850317735205877701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7603115233545156803918467 11404672850317735205877701)
      ·
        refine ⟨2138376159434575351102069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11404672850317735205877701 2138376159434575351102069)
        ·
          refine ⟨200472764946991439165819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2138376159434575351102069 200472764946991439165819)
          ·
            refine ⟨300709147420487158748729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200472764946991439165819 300709147420487158748729)
            ·
              refine ⟨225531860565365369061547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300709147420487158748729 225531860565365369061547)
              ·
                refine ⟨338297790848048053592321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225531860565365369061547 338297790848048053592321)
                ·
                  refine ⟨253723343136036040194241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338297790848048053592321 253723343136036040194241)
                  ·
                    refine ⟨190292507352027030145681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253723343136036040194241 190292507352027030145681)
                    ·
                      refine ⟨142719380514020272609261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190292507352027030145681 142719380514020272609261)
                      ·
                        rfl

theorem cell23_277945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_277945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_277945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_277945 prefixEnd_277945 := by exact prefixLift 277945
  have htrace : WordTrace (prefixWord ++ tailWord_277945) baseStart_277945 baseEnd_277945 := by
    simpa [prefixWord, tailWord_277945, baseEnd_277945] using wordTrace_append hprefix tailTrace_277945
  have hstable : (prefixWord ++ tailWord_277945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277945).length < 2 ^ (prefixWord ++ tailWord_277945).sum := by decide
  have hdescent : baseEnd_277945 < baseStart_277945 := by decide
  rcases family_descends (prefixWord ++ tailWord_277945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278044 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_278044 : Nat := 118140960795 + 278044 * 2 ^ 59
def prefixEnd_278044 : Nat := 4983230072969 + 3 ^ 40 * 278044 * 2
def baseEnd_278044 : Nat := 142770215098815385271305

theorem tailTrace_278044 : CollatzResearch.WordTrace tailWord_278044 prefixEnd_278044 142770215098815385271305 := by
  unfold tailWord_278044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070548902350774489872593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6760731869801032653163457 5070548902350774489872593)
  ·
    refine ⟨3802911676763080867404445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5070548902350774489872593 3802911676763080867404445)
    ·
      refine ⟨1426091878786155325276667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3802911676763080867404445 1426091878786155325276667)
      ·
        refine ⟨2139137818179232987915001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426091878786155325276667 2139137818179232987915001)
        ·
          refine ⟨1604353363634424740936251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2139137818179232987915001 1604353363634424740936251)
          ·
            refine ⟨2406530045451637111404377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604353363634424740936251 2406530045451637111404377)
            ·
              refine ⟨1804897534088727833553283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406530045451637111404377 1804897534088727833553283)
              ·
                refine ⟨2707346301133091750329925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804897534088727833553283 2707346301133091750329925)
                ·
                  refine ⟨507627431462454703186861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2707346301133091750329925 507627431462454703186861)
                  ·
                    refine ⟨190360286798420513695073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507627431462454703186861 190360286798420513695073)
                    ·
                      refine ⟨142770215098815385271305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190360286798420513695073 142770215098815385271305)
                      ·
                        rfl

theorem cell23_278044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_278044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278044 prefixEnd_278044 := by exact prefixLift 278044
  have htrace : WordTrace (prefixWord ++ tailWord_278044) baseStart_278044 baseEnd_278044 := by
    simpa [prefixWord, tailWord_278044, baseEnd_278044] using wordTrace_append hprefix tailTrace_278044
  have hstable : (prefixWord ++ tailWord_278044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278044).length < 2 ^ (prefixWord ++ tailWord_278044).sum := by decide
  have hdescent : baseEnd_278044 < baseStart_278044 := by decide
  rcases family_descends (prefixWord ++ tailWord_278044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278051 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 3]
def baseStart_278051 : Nat := 118140960795 + 278051 * 2 ^ 59
def prefixEnd_278051 : Nat := 4983230072969 + 3 ^ 40 * 278051 * 2
def baseEnd_278051 : Nat := 142773809463396857883773

theorem tailTrace_278051 : CollatzResearch.WordTrace tailWord_278051 prefixEnd_278051 142773809463396857883773 := by
  unfold tailWord_278051
  simp only [CollatzResearch.WordTrace]
  refine ⟨10141353115676189175250007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6760902077117459450166671 10141353115676189175250007)
  ·
    refine ⟨15212029673514283762875011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10141353115676189175250007 15212029673514283762875011)
    ·
      refine ⟨22818044510271425644312517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15212029673514283762875011 22818044510271425644312517)
      ·
        refine ⟨4278383345675892308308597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22818044510271425644312517 4278383345675892308308597)
        ·
          refine ⟨401098438657114903903931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4278383345675892308308597 401098438657114903903931)
          ·
            refine ⟨601647657985672355855897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401098438657114903903931 601647657985672355855897)
            ·
              refine ⟨451235743489254266891923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601647657985672355855897 451235743489254266891923)
              ·
                refine ⟨676853615233881400337885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451235743489254266891923 676853615233881400337885)
                ·
                  refine ⟨253820105712705525126707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676853615233881400337885 253820105712705525126707)
                  ·
                    refine ⟨380730158569058287690061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253820105712705525126707 380730158569058287690061)
                    ·
                      refine ⟨142773809463396857883773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 380730158569058287690061 142773809463396857883773)
                      ·
                        rfl

theorem cell23_278051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_278051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278051 prefixEnd_278051 := by exact prefixLift 278051
  have htrace : WordTrace (prefixWord ++ tailWord_278051) baseStart_278051 baseEnd_278051 := by
    simpa [prefixWord, tailWord_278051, baseEnd_278051] using wordTrace_append hprefix tailTrace_278051
  have hstable : (prefixWord ++ tailWord_278051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278051).length < 2 ^ (prefixWord ++ tailWord_278051).sum := by decide
  have hdescent : baseEnd_278051 < baseStart_278051 := by decide
  rcases family_descends (prefixWord ++ tailWord_278051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278067 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 1, 6]
def baseStart_278067 : Nat := 118140960795 + 278067 * 2 ^ 59
def prefixEnd_278067 : Nat := 4983230072969 + 3 ^ 40 * 278067 * 2
def baseEnd_278067 : Nat := 47594008384622931761233

theorem tailTrace_278067 : CollatzResearch.WordTrace tailWord_278067 prefixEnd_278067 47594008384622931761233 := by
  unfold tailWord_278067
  simp only [CollatzResearch.WordTrace]
  refine ⟨10141936683618223907832455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6761291122412149271888303 10141936683618223907832455)
  ·
    refine ⟨15212905025427335861748683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10141936683618223907832455 15212905025427335861748683)
    ·
      refine ⟨22819357538141003792623025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15212905025427335861748683 22819357538141003792623025)
      ·
        refine ⟨17114518153605752844467269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22819357538141003792623025 17114518153605752844467269)
        ·
          refine ⟨3208972153801078658337613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17114518153605752844467269 3208972153801078658337613)
          ·
            refine ⟨1203364557675404496876605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3208972153801078658337613 1203364557675404496876605)
            ·
              refine ⟨451261709128276686328727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203364557675404496876605 451261709128276686328727)
              ·
                refine ⟨676892563692415029493091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451261709128276686328727 676892563692415029493091)
                ·
                  refine ⟨1015338845538622544239637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676892563692415029493091 1015338845538622544239637)
                  ·
                    refine ⟨47594008384622931761233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1015338845538622544239637 47594008384622931761233)
                    ·
                      rfl

theorem cell23_278067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 6].length) (baseStart_278067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278067 prefixEnd_278067 := by exact prefixLift 278067
  have htrace : WordTrace (prefixWord ++ tailWord_278067) baseStart_278067 baseEnd_278067 := by
    simpa [prefixWord, tailWord_278067, baseEnd_278067] using wordTrace_append hprefix tailTrace_278067
  have hstable : (prefixWord ++ tailWord_278067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278067).length < 2 ^ (prefixWord ++ tailWord_278067).sum := by decide
  have hdescent : baseEnd_278067 < baseStart_278067 := by decide
  rcases family_descends (prefixWord ++ tailWord_278067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278074 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_278074 : Nat := 118140960795 + 278074 * 2 ^ 59
def prefixEnd_278074 : Nat := 4983230072969 + 3 ^ 40 * 278074 * 2
def baseEnd_278074 : Nat := 142785619518450267896167

theorem tailTrace_278074 : CollatzResearch.WordTrace tailWord_278074 prefixEnd_278074 142785619518450267896167 := by
  unfold tailWord_278074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535547998648216025834319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6761461329728576068891517 2535547998648216025834319)
  ·
    refine ⟨3803321997972324038751479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2535547998648216025834319 3803321997972324038751479)
    ·
      refine ⟨5704982996958486058127219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3803321997972324038751479 5704982996958486058127219)
      ·
        refine ⟨8557474495437729087190829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5704982996958486058127219 8557474495437729087190829)
        ·
          refine ⟨3209052935789148407696561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8557474495437729087190829 3209052935789148407696561)
          ·
            refine ⟨2406789701841861305772421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209052935789148407696561 2406789701841861305772421)
            ·
              refine ⟨451273069095348994832329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2406789701841861305772421 451273069095348994832329)
              ·
                refine ⟨338454801821511746124247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451273069095348994832329 338454801821511746124247)
                ·
                  refine ⟨507682202732267619186371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338454801821511746124247 507682202732267619186371)
                  ·
                    refine ⟨761523304098401428779557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507682202732267619186371 761523304098401428779557)
                    ·
                      refine ⟨142785619518450267896167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 761523304098401428779557 142785619518450267896167)
                      ·
                        rfl

theorem cell23_278074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_278074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278074 prefixEnd_278074 := by exact prefixLift 278074
  have htrace : WordTrace (prefixWord ++ tailWord_278074) baseStart_278074 baseEnd_278074 := by
    simpa [prefixWord, tailWord_278074, baseEnd_278074] using wordTrace_append hprefix tailTrace_278074
  have hstable : (prefixWord ++ tailWord_278074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278074).length < 2 ^ (prefixWord ++ tailWord_278074).sum := by decide
  have hdescent : baseEnd_278074 < baseStart_278074 := by decide
  rcases family_descends (prefixWord ++ tailWord_278074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278102 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_278102 : Nat := 118140960795 + 278102 * 2 ^ 59
def prefixEnd_278102 : Nat := 4983230072969 + 3 ^ 40 * 278102 * 2
def baseEnd_278102 : Nat := 142799996976776158346039

theorem tailTrace_278102 : CollatzResearch.WordTrace tailWord_278102 prefixEnd_278102 142799996976776158346039 := by
  unfold tailWord_278102
  simp only [CollatzResearch.WordTrace]
  refine ⟨633950827405714055334785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6762142158994283256904373 633950827405714055334785)
  ·
    refine ⟨475463120554285541501089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 633950827405714055334785 475463120554285541501089)
    ·
      refine ⟨356597340415714156125817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475463120554285541501089 356597340415714156125817)
      ·
        refine ⟨267448005311785617094363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356597340415714156125817 267448005311785617094363)
        ·
          refine ⟨401172007967678425641545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267448005311785617094363 401172007967678425641545)
          ·
            refine ⟨300879005975758819231159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401172007967678425641545 300879005975758819231159)
            ·
              refine ⟨451318508963638228846739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300879005975758819231159 451318508963638228846739)
              ·
                refine ⟨676977763445457343270109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451318508963638228846739 676977763445457343270109)
                ·
                  refine ⟨253866661292046503726291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676977763445457343270109 253866661292046503726291)
                  ·
                    refine ⟨380799991938069755589437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253866661292046503726291 380799991938069755589437)
                    ·
                      refine ⟨142799996976776158346039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 380799991938069755589437 142799996976776158346039)
                      ·
                        rfl

theorem cell23_278102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_278102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278102 prefixEnd_278102 := by exact prefixLift 278102
  have htrace : WordTrace (prefixWord ++ tailWord_278102) baseStart_278102 baseEnd_278102 := by
    simpa [prefixWord, tailWord_278102, baseEnd_278102] using wordTrace_append hprefix tailTrace_278102
  have hstable : (prefixWord ++ tailWord_278102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278102).length < 2 ^ (prefixWord ++ tailWord_278102).sum := by decide
  have hdescent : baseEnd_278102 < baseStart_278102 := by decide
  rcases family_descends (prefixWord ++ tailWord_278102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278108 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_278108 : Nat := 118140960795 + 278108 * 2 ^ 59
def prefixEnd_278108 : Nat := 4983230072969 + 3 ^ 40 * 278108 * 2
def baseEnd_278108 : Nat := 142803077860703134871011

theorem tailTrace_278108 : CollatzResearch.WordTrace tailWord_278108 prefixEnd_278108 142803077860703134871011 := by
  unfold tailWord_278108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071716038234843955037489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6762288050979791940049985 5071716038234843955037489)
  ·
    refine ⟨3803787028676132966278117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5071716038234843955037489 3803787028676132966278117)
    ·
      refine ⟨713210067876774931177147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3803787028676132966278117 713210067876774931177147)
      ·
        refine ⟨1069815101815162396765721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713210067876774931177147 1069815101815162396765721)
        ·
          refine ⟨802361326361371797574291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069815101815162396765721 802361326361371797574291)
          ·
            refine ⟨1203541989542057696361437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802361326361371797574291 1203541989542057696361437)
            ·
              refine ⟨451328246078271636135539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203541989542057696361437 451328246078271636135539)
              ·
                refine ⟨676992369117407454203309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451328246078271636135539 676992369117407454203309)
                ·
                  refine ⟨253872138419027795326241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676992369117407454203309 253872138419027795326241)
                  ·
                    refine ⟨190404103814270846494681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253872138419027795326241 190404103814270846494681)
                    ·
                      refine ⟨142803077860703134871011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190404103814270846494681 142803077860703134871011)
                      ·
                        rfl

theorem cell23_278108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_278108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278108 prefixEnd_278108 := by exact prefixLift 278108
  have htrace : WordTrace (prefixWord ++ tailWord_278108) baseStart_278108 baseEnd_278108 := by
    simpa [prefixWord, tailWord_278108, baseEnd_278108] using wordTrace_append hprefix tailTrace_278108
  have hstable : (prefixWord ++ tailWord_278108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278108).length < 2 ^ (prefixWord ++ tailWord_278108).sum := by decide
  have hdescent : baseEnd_278108 < baseStart_278108 := by decide
  rcases family_descends (prefixWord ++ tailWord_278108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278158 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_278158 : Nat := 118140960795 + 278158 * 2 ^ 59
def prefixEnd_278158 : Nat := 4983230072969 + 3 ^ 40 * 278158 * 2
def baseEnd_278158 : Nat := 142828751893427939245781

theorem tailTrace_278158 : CollatzResearch.WordTrace tailWord_278158 prefixEnd_278158 142828751893427939245781 := by
  unfold tailWord_278158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268156965786068306174391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6763503817525697632930085 1268156965786068306174391)
  ·
    refine ⟨1902235448679102459261587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268156965786068306174391 1902235448679102459261587)
    ·
      refine ⟨2853353173018653688892381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902235448679102459261587 2853353173018653688892381)
      ·
        refine ⟨1070007439881995133334643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2853353173018653688892381 1070007439881995133334643)
        ·
          refine ⟨1605011159822992700001965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070007439881995133334643 1605011159822992700001965)
          ·
            refine ⟨601879184933622262500737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1605011159822992700001965 601879184933622262500737)
            ·
              refine ⟨451409388700216696875553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601879184933622262500737 451409388700216696875553)
              ·
                refine ⟨338557041525162522656665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451409388700216696875553 338557041525162522656665)
                ·
                  refine ⟨253917781143871891992499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338557041525162522656665 253917781143871891992499)
                  ·
                    refine ⟨380876671715807837988749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253917781143871891992499 380876671715807837988749)
                    ·
                      refine ⟨142828751893427939245781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 380876671715807837988749 142828751893427939245781)
                      ·
                        rfl

theorem cell23_278158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_278158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278158 prefixEnd_278158 := by exact prefixLift 278158
  have htrace : WordTrace (prefixWord ++ tailWord_278158) baseStart_278158 baseEnd_278158 := by
    simpa [prefixWord, tailWord_278158, baseEnd_278158] using wordTrace_append hprefix tailTrace_278158
  have hstable : (prefixWord ++ tailWord_278158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278158).length < 2 ^ (prefixWord ++ tailWord_278158).sum := by decide
  have hdescent : baseEnd_278158 < baseStart_278158 := by decide
  rcases family_descends (prefixWord ++ tailWord_278158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278174 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_278174 : Nat := 118140960795 + 278174 * 2 ^ 59
def prefixEnd_278174 : Nat := 4983230072969 + 3 ^ 40 * 278174 * 2
def baseEnd_278174 : Nat := 47612322527966625548569

theorem tailTrace_278174 : CollatzResearch.WordTrace tailWord_278174 prefixEnd_278174 47612322527966625548569 := by
  unfold tailWord_278174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268229911778822647747197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6763892862820387454651717 1268229911778822647747197)
  ·
    refine ⟨475586216917058492905199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1268229911778822647747197 475586216917058492905199)
    ·
      refine ⟨713379325375587739357799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475586216917058492905199 713379325375587739357799)
      ·
        refine ⟨1070068988063381609036699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713379325375587739357799 1070068988063381609036699)
        ·
          refine ⟨1605103482095072413555049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070068988063381609036699 1605103482095072413555049)
          ·
            refine ⟨1203827611571304310166287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1605103482095072413555049 1203827611571304310166287)
            ·
              refine ⟨1805741417356956465249431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203827611571304310166287 1805741417356956465249431)
              ·
                refine ⟨2708612126035434697874147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805741417356956465249431 2708612126035434697874147)
                ·
                  refine ⟨4062918189053152046811221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708612126035434697874147 4062918189053152046811221)
                  ·
                    refine ⟨47612322527966625548569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4062918189053152046811221 47612322527966625548569)
                    ·
                      rfl

theorem cell23_278174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_278174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278174 prefixEnd_278174 := by exact prefixLift 278174
  have htrace : WordTrace (prefixWord ++ tailWord_278174) baseStart_278174 baseEnd_278174 := by
    simpa [prefixWord, tailWord_278174, baseEnd_278174] using wordTrace_append hprefix tailTrace_278174
  have hstable : (prefixWord ++ tailWord_278174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278174).length < 2 ^ (prefixWord ++ tailWord_278174).sum := by decide
  have hdescent : baseEnd_278174 < baseStart_278174 := by decide
  rcases family_descends (prefixWord ++ tailWord_278174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278221 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 7]
def baseStart_278221 : Nat := 118140960795 + 278221 * 2 ^ 59
def prefixEnd_278221 : Nat := 4983230072969 + 3 ^ 40 * 278221 * 2
def baseEnd_278221 : Nat := 15873455686073465861999

theorem tailTrace_278221 : CollatzResearch.WordTrace tailWord_278221 prefixEnd_278221 15873455686073465861999 := by
  unfold tailWord_278221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10147553525060308208938517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6765035683373538805959011 10147553525060308208938517)
  ·
    refine ⟨475666571487201947293993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10147553525060308208938517 475666571487201947293993)
    ·
      refine ⟨356749928615401460470495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475666571487201947293993 356749928615401460470495)
      ·
        refine ⟨535124892923102190705743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356749928615401460470495 535124892923102190705743)
        ·
          refine ⟨802687339384653286058615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535124892923102190705743 802687339384653286058615)
          ·
            refine ⟨1204031009076979929087923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802687339384653286058615 1204031009076979929087923)
            ·
              refine ⟨1806046513615469893631885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204031009076979929087923 1806046513615469893631885)
              ·
                refine ⟨677267442605801210111957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806046513615469893631885 677267442605801210111957)
                ·
                  refine ⟨15873455686073465861999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 677267442605801210111957 15873455686073465861999)
                  ·
                    rfl

theorem cell23_278221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_278221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278221 prefixEnd_278221 := by exact prefixLift 278221
  have htrace : WordTrace (prefixWord ++ tailWord_278221) baseStart_278221 baseEnd_278221 := by
    simpa [prefixWord, tailWord_278221, baseEnd_278221] using wordTrace_append hprefix tailTrace_278221
  have hstable : (prefixWord ++ tailWord_278221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278221).length < 2 ^ (prefixWord ++ tailWord_278221).sum := by decide
  have hdescent : baseEnd_278221 < baseStart_278221 := by decide
  rcases family_descends (prefixWord ++ tailWord_278221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278224 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2]
def baseStart_278224 : Nat := 118140960795 + 278224 * 2 ^ 59
def prefixEnd_278224 : Nat := 4983230072969 + 3 ^ 40 * 278224 * 2
def baseEnd_278224 : Nat := 142862641616624681020477

theorem tailTrace_278224 : CollatzResearch.WordTrace tailWord_278224 prefixEnd_278224 142862641616624681020477 := by
  unfold tailWord_278224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073831472024719860648863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6765108629366293147531817 5073831472024719860648863)
  ·
    refine ⟨7610747208037079790973295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5073831472024719860648863 7610747208037079790973295)
    ·
      refine ⟨11416120812055619686459943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610747208037079790973295 11416120812055619686459943)
      ·
        refine ⟨17124181218083429529689915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11416120812055619686459943 17124181218083429529689915)
        ·
          refine ⟨25686271827125144294534873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17124181218083429529689915 25686271827125144294534873)
          ·
            refine ⟨19264703870343858220901155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25686271827125144294534873 19264703870343858220901155)
            ·
              refine ⟨28897055805515787331351733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19264703870343858220901155 28897055805515787331351733)
              ·
                refine ⟨2709098981767105062314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28897055805515787331351733 2709098981767105062314225)
                ·
                  refine ⟨2031824236325328796735669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709098981767105062314225 2031824236325328796735669)
                  ·
                    refine ⟨190483522155499574693969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2031824236325328796735669 190483522155499574693969)
                    ·
                      refine ⟨142862641616624681020477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 190483522155499574693969 142862641616624681020477)
                      ·
                        rfl

theorem cell23_278224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2].length) (baseStart_278224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278224 prefixEnd_278224 := by exact prefixLift 278224
  have htrace : WordTrace (prefixWord ++ tailWord_278224) baseStart_278224 baseEnd_278224 := by
    simpa [prefixWord, tailWord_278224, baseEnd_278224] using wordTrace_append hprefix tailTrace_278224
  have hstable : (prefixWord ++ tailWord_278224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278224).length < 2 ^ (prefixWord ++ tailWord_278224).sum := by decide
  have hdescent : baseEnd_278224 < baseStart_278224 := by decide
  rcases family_descends (prefixWord ++ tailWord_278224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278254 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_278254 : Nat := 118140960795 + 278254 * 2 ^ 59
def prefixEnd_278254 : Nat := 4983230072969 + 3 ^ 40 * 278254 * 2
def baseEnd_278254 : Nat := 142878046036259563645339

theorem tailTrace_278254 : CollatzResearch.WordTrace tailWord_278254 prefixEnd_278254 142878046036259563645339 := by
  unfold tailWord_278254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268594641742594355611227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6765838089293836563259877 1268594641742594355611227)
  ·
    refine ⟨1902891962613891533416841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268594641742594355611227 1902891962613891533416841)
    ·
      refine ⟨1427168971960418650062631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1902891962613891533416841 1427168971960418650062631)
      ·
        refine ⟨2140753457940627975093947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1427168971960418650062631 2140753457940627975093947)
        ·
          refine ⟨3211130186910941962640921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140753457940627975093947 3211130186910941962640921)
          ·
            refine ⟨2408347640183206471980691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211130186910941962640921 2408347640183206471980691)
            ·
              refine ⟨3612521460274809707971037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408347640183206471980691 3612521460274809707971037)
              ·
                refine ⟨1354695547603053640489139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3612521460274809707971037 1354695547603053640489139)
                ·
                  refine ⟨2032043321404580460733709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354695547603053640489139 2032043321404580460733709)
                  ·
                    refine ⟨762016245526717672775141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2032043321404580460733709 762016245526717672775141)
                    ·
                      refine ⟨142878046036259563645339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 762016245526717672775141 142878046036259563645339)
                      ·
                        rfl

theorem cell23_278254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_278254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278254 prefixEnd_278254 := by exact prefixLift 278254
  have htrace : WordTrace (prefixWord ++ tailWord_278254) baseStart_278254 baseEnd_278254 := by
    simpa [prefixWord, tailWord_278254, baseEnd_278254] using wordTrace_append hprefix tailTrace_278254
  have hstable : (prefixWord ++ tailWord_278254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278254).length < 2 ^ (prefixWord ++ tailWord_278254).sum := by decide
  have hdescent : baseEnd_278254 < baseStart_278254 := by decide
  rcases family_descends (prefixWord ++ tailWord_278254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_278267 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_278267 : Nat := 118140960795 + 278267 * 2 ^ 59
def prefixEnd_278267 : Nat := 4983230072969 + 3 ^ 40 * 278267 * 2
def baseEnd_278267 : Nat := 142884721284768012782779

theorem tailTrace_278267 : CollatzResearch.WordTrace tailWord_278267 prefixEnd_278267 142884721284768012782779 := by
  unfold tailWord_278267
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149231282893658065113055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6766154188595772043408703 10149231282893658065113055)
  ·
    refine ⟨15223846924340487097669583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10149231282893658065113055 15223846924340487097669583)
    ·
      refine ⟨22835770386510730646504375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15223846924340487097669583 22835770386510730646504375)
      ·
        refine ⟨34253655579766095969756563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22835770386510730646504375 34253655579766095969756563)
        ·
          refine ⟨51380483369649143954634845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34253655579766095969756563 51380483369649143954634845)
          ·
            refine ⟨19267681263618428982988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51380483369649143954634845 19267681263618428982988067)
            ·
              refine ⟨28901521895427643474482101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19267681263618428982988067 28901521895427643474482101)
              ·
                refine ⟨2709517677696341575732697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28901521895427643474482101 2709517677696341575732697)
                ·
                  refine ⟨2032138258272256181799523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709517677696341575732697 2032138258272256181799523)
                  ·
                    refine ⟨3048207387408384272699285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2032138258272256181799523 3048207387408384272699285)
                    ·
                      refine ⟨142884721284768012782779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3048207387408384272699285 142884721284768012782779)
                      ·
                        rfl

theorem cell23_278267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_278267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_278267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_278267 prefixEnd_278267 := by exact prefixLift 278267
  have htrace : WordTrace (prefixWord ++ tailWord_278267) baseStart_278267 baseEnd_278267 := by
    simpa [prefixWord, tailWord_278267, baseEnd_278267] using wordTrace_append hprefix tailTrace_278267
  have hstable : (prefixWord ++ tailWord_278267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_278267).length < 2 ^ (prefixWord ++ tailWord_278267).sum := by decide
  have hdescent : baseEnd_278267 < baseStart_278267 := by decide
  rcases family_descends (prefixWord ++ tailWord_278267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
