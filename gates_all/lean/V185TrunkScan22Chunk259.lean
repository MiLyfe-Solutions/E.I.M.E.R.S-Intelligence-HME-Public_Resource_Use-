import V185TrunkScan22Chunk258

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2310848 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_2310848 : Nat := 118140960795 + 2310848 * 2 ^ 59
def prefixEnd_2310848 : Nat := 4983230072969 + 3 ^ 40 * 2310848 * 2
def baseEnd_2310848 : Nat := 791050495654053353515073

theorem tailTrace_2310848 : CollatzResearch.WordTrace tailWord_2310848 prefixEnd_2310848 791050495654053353515073 := by
  unfold tailWord_2310848
  simp only [CollatzResearch.WordTrace]
  refine ⟨42141775366099916131454599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56189033821466554841939465 42141775366099916131454599)
  ·
    refine ⟨63212663049149874197181899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42141775366099916131454599 63212663049149874197181899)
    ·
      refine ⟨94818994573724811295772849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63212663049149874197181899 94818994573724811295772849)
      ·
        refine ⟨71114245930293608471829637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94818994573724811295772849 71114245930293608471829637)
        ·
          refine ⟨13333921111930051588468057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71114245930293608471829637 13333921111930051588468057)
          ·
            refine ⟨10000440833947538691351043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13333921111930051588468057 10000440833947538691351043)
            ·
              refine ⟨15000661250921308037026565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000440833947538691351043 15000661250921308037026565)
              ·
                refine ⟨2812623984547745256942481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15000661250921308037026565 2812623984547745256942481)
                ·
                  refine ⟨2109467988410808942706861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812623984547745256942481 2109467988410808942706861)
                  ·
                    refine ⟨791050495654053353515073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109467988410808942706861 791050495654053353515073)
                    ·
                      rfl

theorem cell22_2310848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_2310848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310848 prefixEnd_2310848 := by exact prefixLift 2310848
  have htrace : WordTrace (prefixWord ++ tailWord_2310848) baseStart_2310848 baseEnd_2310848 := by
    simpa [prefixWord, tailWord_2310848, baseEnd_2310848] using wordTrace_append hprefix tailTrace_2310848
  have hstable : (prefixWord ++ tailWord_2310848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310848).length < 2 ^ (prefixWord ++ tailWord_2310848).sum := by decide
  have hdescent : baseEnd_2310848 < baseStart_2310848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310859 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_2310859 : Nat := 118140960795 + 2310859 * 2 ^ 59
def prefixEnd_2310859 : Nat := 4983230072969 + 3 ^ 40 * 2310859 * 2
def baseEnd_2310859 : Nat := 791054261178852991490039

theorem tailTrace_2310859 : CollatzResearch.WordTrace tailWord_2310859 prefixEnd_2310859 791054261178852991490039 := by
  unfold tailWord_2310859
  simp only [CollatzResearch.WordTrace]
  refine ⟨84283951935159981141559631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56189301290106654094373087 84283951935159981141559631)
  ·
    refine ⟨126425927902739971712339447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84283951935159981141559631 126425927902739971712339447)
    ·
      refine ⟨189638891854109957568509171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126425927902739971712339447 189638891854109957568509171)
      ·
        refine ⟨284458337781164936352763757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189638891854109957568509171 284458337781164936352763757)
        ·
          refine ⟨106671876667936851132286409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284458337781164936352763757 106671876667936851132286409)
          ·
            refine ⟨80003907500952638349214807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106671876667936851132286409 80003907500952638349214807)
            ·
              refine ⟨120005861251428957523822211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80003907500952638349214807 120005861251428957523822211)
              ·
                refine ⟨180008791877143436285733317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120005861251428957523822211 180008791877143436285733317)
                ·
                  refine ⟨33751648476964394303574997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180008791877143436285733317 33751648476964394303574997)
                  ·
                    refine ⟨791054261178852991490039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33751648476964394303574997 791054261178852991490039)
                    ·
                      rfl

theorem cell22_2310859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_2310859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310859 prefixEnd_2310859 := by exact prefixLift 2310859
  have htrace : WordTrace (prefixWord ++ tailWord_2310859) baseStart_2310859 baseEnd_2310859 := by
    simpa [prefixWord, tailWord_2310859, baseEnd_2310859] using wordTrace_append hprefix tailTrace_2310859
  have hstable : (prefixWord ++ tailWord_2310859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310859).length < 2 ^ (prefixWord ++ tailWord_2310859).sum := by decide
  have hdescent : baseEnd_2310859 < baseStart_2310859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310893 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_2310893 : Nat := 118140960795 + 2310893 * 2 ^ 59
def prefixEnd_2310893 : Nat := 4983230072969 + 3 ^ 40 * 2310893 * 2
def baseEnd_2310893 : Nat := 791065900073688236139935

theorem tailTrace_2310893 : CollatzResearch.WordTrace tailWord_2310893 prefixEnd_2310893 791065900073688236139935 := by
  unfold tailWord_2310893
  simp only [CollatzResearch.WordTrace]
  refine ⟨84285192017036804948297333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56190128011357869965531555 84285192017036804948297333)
  ·
    refine ⟨7901736751597200463902875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84285192017036804948297333 7901736751597200463902875)
    ·
      refine ⟨11852605127395800695854313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901736751597200463902875 11852605127395800695854313)
      ·
        refine ⟨8889453845546850521890735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11852605127395800695854313 8889453845546850521890735)
        ·
          refine ⟨13334180768320275782836103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889453845546850521890735 13334180768320275782836103)
          ·
            refine ⟨20001271152480413674254155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13334180768320275782836103 20001271152480413674254155)
            ·
              refine ⟨30001906728720620511381233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20001271152480413674254155 30001906728720620511381233)
              ·
                refine ⟨22501430046540465383535925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30001906728720620511381233 22501430046540465383535925)
                ·
                  refine ⟨2109509066863168629706493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22501430046540465383535925 2109509066863168629706493)
                  ·
                    refine ⟨791065900073688236139935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109509066863168629706493 791065900073688236139935)
                    ·
                      rfl

theorem cell22_2310893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_2310893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310893 prefixEnd_2310893 := by exact prefixLift 2310893
  have htrace : WordTrace (prefixWord ++ tailWord_2310893) baseStart_2310893 baseEnd_2310893 := by
    simpa [prefixWord, tailWord_2310893, baseEnd_2310893] using wordTrace_append hprefix tailTrace_2310893
  have hstable : (prefixWord ++ tailWord_2310893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310893).length < 2 ^ (prefixWord ++ tailWord_2310893).sum := by decide
  have hdescent : baseEnd_2310893 < baseStart_2310893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310910 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2310910 : Nat := 118140960795 + 2310910 * 2 ^ 59
def prefixEnd_2310910 : Nat := 4983230072969 + 3 ^ 40 * 2310910 * 2
def baseEnd_2310910 : Nat := 791071719521105858464883

theorem tailTrace_2310910 : CollatzResearch.WordTrace tailWord_2310910 prefixEnd_2310910 791071719521105858464883 := by
  unfold tailWord_2310910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535726507246902106458273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56190541371983477901110789 10535726507246902106458273)
  ·
    refine ⟨7901794880435176579843705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10535726507246902106458273 7901794880435176579843705)
    ·
      refine ⟨5926346160326382434882779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7901794880435176579843705 5926346160326382434882779)
      ·
        refine ⟨8889519240489573652324169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926346160326382434882779 8889519240489573652324169)
        ·
          refine ⟨6667139430367180239243127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8889519240489573652324169 6667139430367180239243127)
          ·
            refine ⟨10000709145550770358864691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667139430367180239243127 10000709145550770358864691)
            ·
              refine ⟨15001063718326155538297037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10000709145550770358864691 15001063718326155538297037)
              ·
                refine ⟨5625398894372308326861389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15001063718326155538297037 5625398894372308326861389)
                ·
                  refine ⟨2109524585389615622573021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5625398894372308326861389 2109524585389615622573021)
                  ·
                    refine ⟨791071719521105858464883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109524585389615622573021 791071719521105858464883)
                    ·
                      rfl

theorem cell22_2310910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2310910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310910 prefixEnd_2310910 := by exact prefixLift 2310910
  have htrace : WordTrace (prefixWord ++ tailWord_2310910) baseStart_2310910 baseEnd_2310910 := by
    simpa [prefixWord, tailWord_2310910, baseEnd_2310910] using wordTrace_append hprefix tailTrace_2310910
  have hstable : (prefixWord ++ tailWord_2310910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310910).length < 2 ^ (prefixWord ++ tailWord_2310910).sum := by decide
  have hdescent : baseEnd_2310910 < baseStart_2310910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310921 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_2310921 : Nat := 118140960795 + 2310921 * 2 ^ 59
def prefixEnd_2310921 : Nat := 4983230072969 + 3 ^ 40 * 2310921 * 2
def baseEnd_2310921 : Nat := 791075485045905496439849

theorem tailTrace_2310921 : CollatzResearch.WordTrace tailWord_2310921 prefixEnd_2310921 791075485045905496439849 := by
  unfold tailWord_2310921
  simp only [CollatzResearch.WordTrace]
  refine ⟨84286213260935365730316617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56190808840623577153544411 84286213260935365730316617)
  ·
    refine ⟨63214659945701524297737463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84286213260935365730316617 63214659945701524297737463)
    ·
      refine ⟨94821989918552286446606195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63214659945701524297737463 94821989918552286446606195)
      ·
        refine ⟨142232984877828429669909293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94821989918552286446606195 142232984877828429669909293)
        ·
          refine ⟨53337369329185661126215985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142232984877828429669909293 53337369329185661126215985)
          ·
            refine ⟨40003026996889245844661989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53337369329185661126215985 40003026996889245844661989)
            ·
              refine ⟨7500567561916733595874123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40003026996889245844661989 7500567561916733595874123)
              ·
                refine ⟨11250851342875100393811185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500567561916733595874123 11250851342875100393811185)
                ·
                  refine ⟨8438138507156325295358389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11250851342875100393811185 8438138507156325295358389)
                  ·
                    refine ⟨791075485045905496439849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8438138507156325295358389 791075485045905496439849)
                    ·
                      rfl

theorem cell22_2310921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_2310921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310921 prefixEnd_2310921 := by exact prefixLift 2310921
  have htrace : WordTrace (prefixWord ++ tailWord_2310921) baseStart_2310921 baseEnd_2310921 := by
    simpa [prefixWord, tailWord_2310921, baseEnd_2310921] using wordTrace_append hprefix tailTrace_2310921
  have hstable : (prefixWord ++ tailWord_2310921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310921).length < 2 ^ (prefixWord ++ tailWord_2310921).sum := by decide
  have hdescent : baseEnd_2310921 < baseStart_2310921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310974 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2310974 : Nat := 118140960795 + 2310974 * 2 ^ 59
def prefixEnd_2310974 : Nat := 4983230072969 + 3 ^ 40 * 2310974 * 2
def baseEnd_2310974 : Nat := 263697876009677008288229

theorem tailTrace_2310974 : CollatzResearch.WordTrace tailWord_2310974 prefixEnd_2310974 263697876009677008288229 := by
  unfold tailWord_2310974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536018291217919472749497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56192097553162237187997317 10536018291217919472749497)
  ·
    refine ⟨7902013718413439604562123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10536018291217919472749497 7902013718413439604562123)
    ·
      refine ⟨11853020577620159406843185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902013718413439604562123 11853020577620159406843185)
      ·
        refine ⟨8889765433215119555132389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11853020577620159406843185 8889765433215119555132389)
        ·
          refine ⟨1666831018727834916587323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8889765433215119555132389 1666831018727834916587323)
          ·
            refine ⟨2500246528091752374880985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666831018727834916587323 2500246528091752374880985)
            ·
              refine ⟨1875184896068814281160739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500246528091752374880985 1875184896068814281160739)
              ·
                refine ⟨2812777344103221421741109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875184896068814281160739 2812777344103221421741109)
                ·
                  refine ⟨263697876009677008288229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2812777344103221421741109 263697876009677008288229)
                  ·
                    rfl

theorem cell22_2310974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2310974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310974 prefixEnd_2310974 := by exact prefixLift 2310974
  have htrace : WordTrace (prefixWord ++ tailWord_2310974) baseStart_2310974 baseEnd_2310974 := by
    simpa [prefixWord, tailWord_2310974, baseEnd_2310974] using wordTrace_append hprefix tailTrace_2310974
  have hstable : (prefixWord ++ tailWord_2310974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310974).length < 2 ^ (prefixWord ++ tailWord_2310974).sum := by decide
  have hdescent : baseEnd_2310974 < baseStart_2310974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2310981 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_2310981 : Nat := 118140960795 + 2310981 * 2 ^ 59
def prefixEnd_2310981 : Nat := 4983230072969 + 3 ^ 40 * 2310981 * 2
def baseEnd_2310981 : Nat := 791096024272085339939665

theorem tailTrace_2310981 : CollatzResearch.WordTrace tailWord_2310981 prefixEnd_2310981 791096024272085339939665 := by
  unfold tailWord_2310981
  simp only [CollatzResearch.WordTrace]
  refine ⟨84288401640717995977500797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56192267760478663985000531 84288401640717995977500797)
  ·
    refine ⟨31608150615269248491562799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84288401640717995977500797 31608150615269248491562799)
    ·
      refine ⟨47412225922903872737344199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31608150615269248491562799 47412225922903872737344199)
      ·
        refine ⟨71118338884355809106016299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47412225922903872737344199 71118338884355809106016299)
        ·
          refine ⟨106677508326533713659024449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71118338884355809106016299 106677508326533713659024449)
          ·
            refine ⟨80008131244900285244268337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106677508326533713659024449 80008131244900285244268337)
            ·
              refine ⟨60006098433675213933201253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80008131244900285244268337 60006098433675213933201253)
              ·
                refine ⟨11251143456314102612475235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60006098433675213933201253 11251143456314102612475235)
                ·
                  refine ⟨16876715184471153918712853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11251143456314102612475235 16876715184471153918712853)
                  ·
                    refine ⟨791096024272085339939665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16876715184471153918712853 791096024272085339939665)
                    ·
                      rfl

theorem cell22_2310981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_2310981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2310981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2310981 prefixEnd_2310981 := by exact prefixLift 2310981
  have htrace : WordTrace (prefixWord ++ tailWord_2310981) baseStart_2310981 baseEnd_2310981 := by
    simpa [prefixWord, tailWord_2310981, baseEnd_2310981] using wordTrace_append hprefix tailTrace_2310981
  have hstable : (prefixWord ++ tailWord_2310981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2310981).length < 2 ^ (prefixWord ++ tailWord_2310981).sum := by decide
  have hdescent : baseEnd_2310981 < baseStart_2310981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2310981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311030 : List Nat := [5, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2311030 : Nat := 118140960795 + 2311030 * 2 ^ 59
def prefixEnd_2311030 : Nat := 4983230072969 + 3 ^ 40 * 2311030 * 2
def baseEnd_2311030 : Nat := 87901421997051727273835

theorem tailTrace_2311030 : CollatzResearch.WordTrace tailWord_2311030 prefixEnd_2311030 87901421997051727273835 := by
  unfold tailWord_2311030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268136801096279834127159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56193459211693651564023029 5268136801096279834127159)
  ·
    refine ⟨7902205201644419751190739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5268136801096279834127159 7902205201644419751190739)
    ·
      refine ⟨11853307802466629626786109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902205201644419751190739 11853307802466629626786109)
      ·
        refine ⟨4444990425924986110044791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11853307802466629626786109 4444990425924986110044791)
        ·
          refine ⟨6667485638887479165067187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444990425924986110044791 6667485638887479165067187)
          ·
            refine ⟨10001228458331218747600781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667485638887479165067187 10001228458331218747600781)
            ·
              refine ⟨3750460671874207030350293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10001228458331218747600781 3750460671874207030350293)
              ·
                refine ⟨87901421997051727273835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3750460671874207030350293 87901421997051727273835)
                ·
                  rfl

theorem cell22_2311030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2311030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311030 prefixEnd_2311030 := by exact prefixLift 2311030
  have htrace : WordTrace (prefixWord ++ tailWord_2311030) baseStart_2311030 baseEnd_2311030 := by
    simpa [prefixWord, tailWord_2311030, baseEnd_2311030] using wordTrace_append hprefix tailTrace_2311030
  have hstable : (prefixWord ++ tailWord_2311030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311030).length < 2 ^ (prefixWord ++ tailWord_2311030).sum := by decide
  have hdescent : baseEnd_2311030 < baseStart_2311030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311045 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_2311045 : Nat := 118140960795 + 2311045 * 2 ^ 59
def prefixEnd_2311045 : Nat := 4983230072969 + 3 ^ 40 * 2311045 * 2
def baseEnd_2311045 : Nat := 791117932780010506339469

theorem tailTrace_2311045 : CollatzResearch.WordTrace tailWord_2311045 prefixEnd_2311045 791117932780010506339469 := by
  unfold tailWord_2311045
  simp only [CollatzResearch.WordTrace]
  refine ⟨84290735912486134907830589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56193823941657423271887059 84290735912486134907830589)
  ·
    refine ⟨31609025967182300590436471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84290735912486134907830589 31609025967182300590436471)
    ·
      refine ⟨47413538950773450885654707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31609025967182300590436471 47413538950773450885654707)
      ·
        refine ⟨71120308426160176328482061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47413538950773450885654707 71120308426160176328482061)
        ·
          refine ⟨26670115659810066123180773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71120308426160176328482061 26670115659810066123180773)
          ·
            refine ⟨5000646686214387398096395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26670115659810066123180773 5000646686214387398096395)
            ·
              refine ⟨7500970029321581097144593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000646686214387398096395 7500970029321581097144593)
              ·
                refine ⟨5625727521991185822858445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7500970029321581097144593 5625727521991185822858445)
                ·
                  refine ⟨2109647820746694683571917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5625727521991185822858445 2109647820746694683571917)
                  ·
                    refine ⟨791117932780010506339469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109647820746694683571917 791117932780010506339469)
                    ·
                      rfl

theorem cell22_2311045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_2311045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311045 prefixEnd_2311045 := by exact prefixLift 2311045
  have htrace : WordTrace (prefixWord ++ tailWord_2311045) baseStart_2311045 baseEnd_2311045 := by
    simpa [prefixWord, tailWord_2311045, baseEnd_2311045] using wordTrace_append hprefix tailTrace_2311045
  have hstable : (prefixWord ++ tailWord_2311045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311045).length < 2 ^ (prefixWord ++ tailWord_2311045).sum := by decide
  have hdescent : baseEnd_2311045 < baseStart_2311045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311122 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2311122 : Nat := 118140960795 + 2311122 * 2 ^ 59
def prefixEnd_2311122 : Nat := 4983230072969 + 3 ^ 40 * 2311122 * 2
def baseEnd_2311122 : Nat := 791144291453607972164233

theorem tailTrace_2311122 : CollatzResearch.WordTrace tailWord_2311122 prefixEnd_2311122 791144291453607972164233 := by
  unfold tailWord_2311122
  simp only [CollatzResearch.WordTrace]
  refine ⟨21073386083301794264595905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56195696222138118038922413 21073386083301794264595905)
  ·
    refine ⟨15805039562476345698446929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21073386083301794264595905 15805039562476345698446929)
    ·
      refine ⟨11853779671857259273835197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15805039562476345698446929 11853779671857259273835197)
      ·
        refine ⟨4445167376946472227688199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11853779671857259273835197 4445167376946472227688199)
        ·
          refine ⟨6667751065419708341532299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445167376946472227688199 6667751065419708341532299)
          ·
            refine ⟨10001626598129562512298449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667751065419708341532299 10001626598129562512298449)
            ·
              refine ⟨7501219948597171884223837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001626598129562512298449 7501219948597171884223837)
              ·
                refine ⟨2812957480723939456583939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501219948597171884223837 2812957480723939456583939)
                ·
                  refine ⟨4219436221085909184875909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812957480723939456583939 4219436221085909184875909)
                  ·
                    refine ⟨791144291453607972164233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219436221085909184875909 791144291453607972164233)
                    ·
                      rfl

theorem cell22_2311122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2311122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311122 prefixEnd_2311122 := by exact prefixLift 2311122
  have htrace : WordTrace (prefixWord ++ tailWord_2311122) baseStart_2311122 baseEnd_2311122 := by
    simpa [prefixWord, tailWord_2311122, baseEnd_2311122] using wordTrace_append hprefix tailTrace_2311122
  have hstable : (prefixWord ++ tailWord_2311122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311122).length < 2 ^ (prefixWord ++ tailWord_2311122).sum := by decide
  have hdescent : baseEnd_2311122 < baseStart_2311122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311193 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 7]
def baseStart_2311193 : Nat := 118140960795 + 2311193 * 2 ^ 59
def prefixEnd_2311193 : Nat := 4983230072969 + 3 ^ 40 * 2311193 * 2
def baseEnd_2311193 : Nat := 263722865401529151213005

theorem tailTrace_2311193 : CollatzResearch.WordTrace tailWord_2311193 prefixEnd_2311193 263722865401529151213005 := by
  unfold tailWord_2311193
  simp only [CollatzResearch.WordTrace]
  refine ⟨84296133915949956184218233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56197422610633304122812155 84296133915949956184218233)
  ·
    refine ⟨63222100436962467138163675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84296133915949956184218233 63222100436962467138163675)
    ·
      refine ⟨94833150655443700707245513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63222100436962467138163675 94833150655443700707245513)
      ·
        refine ⟨71124862991582775530434135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94833150655443700707245513 71124862991582775530434135)
        ·
          refine ⟨106687294487374163295651203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71124862991582775530434135 106687294487374163295651203)
          ·
            refine ⟨160030941731061244943476805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106687294487374163295651203 160030941731061244943476805)
            ·
              refine ⟨30005801574573983426901901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160030941731061244943476805 30005801574573983426901901)
              ·
                refine ⟨11252175590465243785088213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30005801574573983426901901 11252175590465243785088213)
                ·
                  refine ⟨263722865401529151213005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11252175590465243785088213 263722865401529151213005)
                  ·
                    rfl

theorem cell22_2311193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_2311193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311193 prefixEnd_2311193 := by exact prefixLift 2311193
  have htrace : WordTrace (prefixWord ++ tailWord_2311193) baseStart_2311193 baseEnd_2311193 := by
    simpa [prefixWord, tailWord_2311193, baseEnd_2311193] using wordTrace_append hprefix tailTrace_2311193
  have hstable : (prefixWord ++ tailWord_2311193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311193).length < 2 ^ (prefixWord ++ tailWord_2311193).sum := by decide
  have hdescent : baseEnd_2311193 < baseStart_2311193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311261 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 5]
def baseStart_2311261 : Nat := 118140960795 + 2311261 * 2 ^ 59
def prefixEnd_2311261 : Nat := 4983230072969 + 3 ^ 40 * 2311261 * 2
def baseEnd_2311261 : Nat := 263730624664752647646269

theorem tailTrace_2311261 : CollatzResearch.WordTrace tailWord_2311261 prefixEnd_2311261 263730624664752647646269 := by
  unfold tailWord_2311261
  simp only [CollatzResearch.WordTrace]
  refine ⟨84298614079703603797693637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56199076053135735865129091 84298614079703603797693637)
  ·
    refine ⟨15805990139944425712067557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84298614079703603797693637 15805990139944425712067557)
    ·
      refine ⟨2963623151239579821012667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15805990139944425712067557 2963623151239579821012667)
      ·
        refine ⟨4445434726859369731519001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963623151239579821012667 4445434726859369731519001)
        ·
          refine ⟨3334076045144527298639251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4445434726859369731519001 3334076045144527298639251)
          ·
            refine ⟨5001114067716790947958877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334076045144527298639251 5001114067716790947958877)
            ·
              refine ⟨1875417775393796605484579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5001114067716790947958877 1875417775393796605484579)
              ·
                refine ⟨2813126663090694908226869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875417775393796605484579 2813126663090694908226869)
                ·
                  refine ⟨263730624664752647646269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2813126663090694908226869 263730624664752647646269)
                  ·
                    rfl

theorem cell22_2311261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_2311261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311261 prefixEnd_2311261 := by exact prefixLift 2311261
  have htrace : WordTrace (prefixWord ++ tailWord_2311261) baseStart_2311261 baseEnd_2311261 := by
    simpa [prefixWord, tailWord_2311261, baseEnd_2311261] using wordTrace_append hprefix tailTrace_2311261
  have hstable : (prefixWord ++ tailWord_2311261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311261).length < 2 ^ (prefixWord ++ tailWord_2311261).sum := by decide
  have hdescent : baseEnd_2311261 < baseStart_2311261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311274 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2311274 : Nat := 118140960795 + 2311274 * 2 ^ 59
def prefixEnd_2311274 : Nat := 4983230072969 + 3 ^ 40 * 2311274 * 2
def baseEnd_2311274 : Nat := 791196324159930242363767

theorem tailTrace_2311274 : CollatzResearch.WordTrace tailWord_2311274 prefixEnd_2311274 791196324159930242363767 := by
  unfold tailWord_2311274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21074772057164126754479219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56199392152437671345277917 21074772057164126754479219)
  ·
    refine ⟨31612158085746190131718829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21074772057164126754479219 31612158085746190131718829)
    ·
      refine ⟨11854559282154821299394561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31612158085746190131718829 11854559282154821299394561)
      ·
        refine ⟨8890919461616115974545921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11854559282154821299394561 8890919461616115974545921)
        ·
          refine ⟨6668189596212086980909441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8890919461616115974545921 6668189596212086980909441)
          ·
            refine ⟨5001142197159065235682081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6668189596212086980909441 5001142197159065235682081)
            ·
              refine ⟨3750856647869298926761561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5001142197159065235682081 3750856647869298926761561)
              ·
                refine ⟨2813142485901974195071171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750856647869298926761561 2813142485901974195071171)
                ·
                  refine ⟨4219713728852961292606757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813142485901974195071171 4219713728852961292606757)
                  ·
                    refine ⟨791196324159930242363767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219713728852961292606757 791196324159930242363767)
                    ·
                      rfl

theorem cell22_2311274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2311274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311274 prefixEnd_2311274 := by exact prefixLift 2311274
  have htrace : WordTrace (prefixWord ++ tailWord_2311274) baseStart_2311274 baseEnd_2311274 := by
    simpa [prefixWord, tailWord_2311274, baseEnd_2311274] using wordTrace_append hprefix tailTrace_2311274
  have hstable : (prefixWord ++ tailWord_2311274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311274).length < 2 ^ (prefixWord ++ tailWord_2311274).sum := by decide
  have hdescent : baseEnd_2311274 < baseStart_2311274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311300 : List Nat := [2, 3, 2, 1, 2, 2, 10]
def baseStart_2311300 : Nat := 118140960795 + 2311300 * 2 ^ 59
def prefixEnd_2311300 : Nat := 4983230072969 + 3 ^ 40 * 2311300 * 2
def baseEnd_2311300 : Nat := 29303897203380549674581

theorem tailTrace_2311300 : CollatzResearch.WordTrace tailWord_2311300 prefixEnd_2311300 29303897203380549674581 := by
  unfold tailWord_2311300
  simp only [CollatzResearch.WordTrace]
  refine ⟨42150018263281156729181677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56200024351041542305575569 42150018263281156729181677)
  ·
    refine ⟨15806256848730433773443129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42150018263281156729181677 15806256848730433773443129)
    ·
      refine ⟨11854692636547825330082347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15806256848730433773443129 11854692636547825330082347)
      ·
        refine ⟨17782038954821737995123521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11854692636547825330082347 17782038954821737995123521)
        ·
          refine ⟨13336529216116303496342641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17782038954821737995123521 13336529216116303496342641)
          ·
            refine ⟨10002396912087227622256981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13336529216116303496342641 10002396912087227622256981)
            ·
              refine ⟨29303897203380549674581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10002396912087227622256981 29303897203380549674581)
              ·
                rfl

theorem cell22_2311300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 10].length) (baseStart_2311300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311300 prefixEnd_2311300 := by exact prefixLift 2311300
  have htrace : WordTrace (prefixWord ++ tailWord_2311300) baseStart_2311300 baseEnd_2311300 := by
    simpa [prefixWord, tailWord_2311300, baseEnd_2311300] using wordTrace_append hprefix tailTrace_2311300
  have hstable : (prefixWord ++ tailWord_2311300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311300).length < 2 ^ (prefixWord ++ tailWord_2311300).sum := by decide
  have hdescent : baseEnd_2311300 < baseStart_2311300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311392 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_2311392 : Nat := 118140960795 + 2311392 * 2 ^ 59
def prefixEnd_2311392 : Nat := 4983230072969 + 3 ^ 40 * 2311392 * 2
def baseEnd_2311392 : Nat := 791236717971417267913405

theorem tailTrace_2311392 : CollatzResearch.WordTrace tailWord_2311392 prefixEnd_2311392 791236717971417267913405 := by
  unfold tailWord_2311392
  simp only [CollatzResearch.WordTrace]
  refine ⟨42151696021114506585356215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56202261361486008780474953 42151696021114506585356215)
  ·
    refine ⟨63227544031671759878034323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42151696021114506585356215 63227544031671759878034323)
    ·
      refine ⟨94841316047507639817051485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63227544031671759878034323 94841316047507639817051485)
      ·
        refine ⟨35565493517815364931394307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94841316047507639817051485 35565493517815364931394307)
        ·
          refine ⟨53348240276723047397091461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35565493517815364931394307 53348240276723047397091461)
          ·
            refine ⟨10002795051885571386954649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53348240276723047397091461 10002795051885571386954649)
            ·
              refine ⟨7502096288914178540215987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10002795051885571386954649 7502096288914178540215987)
              ·
                refine ⟨11253144433371267810323981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502096288914178540215987 11253144433371267810323981)
                ·
                  refine ⟨4219929162514225428871493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11253144433371267810323981 4219929162514225428871493)
                  ·
                    refine ⟨791236717971417267913405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4219929162514225428871493 791236717971417267913405)
                    ·
                      rfl

theorem cell22_2311392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_2311392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311392 prefixEnd_2311392 := by exact prefixLift 2311392
  have htrace : WordTrace (prefixWord ++ tailWord_2311392) baseStart_2311392 baseEnd_2311392 := by
    simpa [prefixWord, tailWord_2311392, baseEnd_2311392] using wordTrace_append hprefix tailTrace_2311392
  have hstable : (prefixWord ++ tailWord_2311392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311392).length < 2 ^ (prefixWord ++ tailWord_2311392).sum := by decide
  have hdescent : baseEnd_2311392 < baseStart_2311392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311458 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2311458 : Nat := 118140960795 + 2311458 * 2 ^ 59
def prefixEnd_2311458 : Nat := 4983230072969 + 3 ^ 40 * 2311458 * 2
def baseEnd_2311458 : Nat := 263753103706738365254401

theorem tailTrace_2311458 : CollatzResearch.WordTrace tailWord_2311458 prefixEnd_2311458 263753103706738365254401 := by
  unfold tailWord_2311458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076449814997476610653757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56203866173326604295076685 21076449814997476610653757)
  ·
    refine ⟨7903668680624053728995159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21076449814997476610653757 7903668680624053728995159)
    ·
      refine ⟨11855503020936080593492739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7903668680624053728995159 11855503020936080593492739)
      ·
        refine ⟨17783254531404120890239109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11855503020936080593492739 17783254531404120890239109)
        ·
          refine ⟨3334360224638272666919833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17783254531404120890239109 3334360224638272666919833)
          ·
            refine ⟨2500770168478704500189875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3334360224638272666919833 2500770168478704500189875)
            ·
              refine ⟨3751155252718056750284813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500770168478704500189875 3751155252718056750284813)
              ·
                refine ⟨1406683219769271281356805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3751155252718056750284813 1406683219769271281356805)
                ·
                  refine ⟨263753103706738365254401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1406683219769271281356805 263753103706738365254401)
                  ·
                    rfl

theorem cell22_2311458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2311458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311458 prefixEnd_2311458 := by exact prefixLift 2311458
  have htrace : WordTrace (prefixWord ++ tailWord_2311458) baseStart_2311458 baseEnd_2311458 := by
    simpa [prefixWord, tailWord_2311458, baseEnd_2311458] using wordTrace_append hprefix tailTrace_2311458
  have hstable : (prefixWord ++ tailWord_2311458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311458).length < 2 ^ (prefixWord ++ tailWord_2311458).sum := by decide
  have hdescent : baseEnd_2311458 < baseStart_2311458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311469 : List Nat := [1, 5, 3, 1, 1, 1, 10]
def baseStart_2311469 : Nat := 118140960795 + 2311469 * 2 ^ 59
def prefixEnd_2311469 : Nat := 4983230072969 + 3 ^ 40 * 2311469 * 2
def baseEnd_2311469 : Nat := 29306039875741286434747

theorem tailTrace_2311469 : CollatzResearch.WordTrace tailWord_2311469 prefixEnd_2311469 29306039875741286434747 := by
  unfold tailWord_2311469
  simp only [CollatzResearch.WordTrace]
  refine ⟨84306200462950055321265461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56204133641966703547510307 84306200462950055321265461)
  ·
    refine ⟨7903706293401567686368637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84306200462950055321265461 7903706293401567686368637)
    ·
      refine ⟨2963889860025587882388239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7903706293401567686368637 2963889860025587882388239)
      ·
        refine ⟨4445834790038381823582359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963889860025587882388239 4445834790038381823582359)
        ·
          refine ⟨6668752185057572735373539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445834790038381823582359 6668752185057572735373539)
          ·
            refine ⟨10003128277586359103060309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6668752185057572735373539 10003128277586359103060309)
            ·
              refine ⟨29306039875741286434747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10003128277586359103060309 29306039875741286434747)
              ·
                rfl

theorem cell22_2311469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 10].length) (baseStart_2311469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311469 prefixEnd_2311469 := by exact prefixLift 2311469
  have htrace : WordTrace (prefixWord ++ tailWord_2311469) baseStart_2311469 baseEnd_2311469 := by
    simpa [prefixWord, tailWord_2311469, baseEnd_2311469] using wordTrace_append hprefix tailTrace_2311469
  have hstable : (prefixWord ++ tailWord_2311469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311469).length < 2 ^ (prefixWord ++ tailWord_2311469).sum := by decide
  have hdescent : baseEnd_2311469 < baseStart_2311469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311482 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_2311482 : Nat := 118140960795 + 2311482 * 2 ^ 59
def prefixEnd_2311482 : Nat := 4983230072969 + 3 ^ 40 * 2311482 * 2
def baseEnd_2311482 : Nat := 791267526810687033163129

theorem tailTrace_2311482 : CollatzResearch.WordTrace tailWord_2311482 prefixEnd_2311482 791267526810687033163129 := by
  unfold tailWord_2311482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076668652975739635372175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56204449741268639027659133 21076668652975739635372175)
  ·
    refine ⟨31615002979463609453058263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21076668652975739635372175 31615002979463609453058263)
    ·
      refine ⟨47422504469195414179587395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31615002979463609453058263 47422504469195414179587395)
      ·
        refine ⟨71133756703793121269381093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47422504469195414179587395 71133756703793121269381093)
        ·
          refine ⟨13337579381961210238008955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71133756703793121269381093 13337579381961210238008955)
          ·
            refine ⟨20006369072941815357013433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13337579381961210238008955 20006369072941815357013433)
            ·
              refine ⟨15004776804706361517760075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20006369072941815357013433 15004776804706361517760075)
              ·
                refine ⟨22507165207059542276640113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15004776804706361517760075 22507165207059542276640113)
                ·
                  refine ⟨16880373905294656707480085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22507165207059542276640113 16880373905294656707480085)
                  ·
                    refine ⟨791267526810687033163129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16880373905294656707480085 791267526810687033163129)
                    ·
                      rfl

theorem cell22_2311482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_2311482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311482 prefixEnd_2311482 := by exact prefixLift 2311482
  have htrace : WordTrace (prefixWord ++ tailWord_2311482) baseStart_2311482 baseEnd_2311482 := by
    simpa [prefixWord, tailWord_2311482, baseEnd_2311482] using wordTrace_append hprefix tailTrace_2311482
  have hstable : (prefixWord ++ tailWord_2311482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311482).length < 2 ^ (prefixWord ++ tailWord_2311482).sum := by decide
  have hdescent : baseEnd_2311482 < baseStart_2311482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311559 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 6]
def baseStart_2311559 : Nat := 118140960795 + 2311559 * 2 ^ 59
def prefixEnd_2311559 : Nat := 4983230072969 + 3 ^ 40 * 2311559 * 2
def baseEnd_2311559 : Nat := 263764628494761499662631

theorem tailTrace_2311559 : CollatzResearch.WordTrace tailWord_2311559 prefixEnd_2311559 263764628494761499662631 := by
  unfold tailWord_2311559
  simp only [CollatzResearch.WordTrace]
  refine ⟨84309483032624000692041731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56206322021749333794694487 84309483032624000692041731)
  ·
    refine ⟨126464224548936001038062597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84309483032624000692041731 126464224548936001038062597)
    ·
      refine ⟨23712042102925500194636737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126464224548936001038062597 23712042102925500194636737)
      ·
        refine ⟨17784031577194125145977553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23712042102925500194636737 17784031577194125145977553)
        ·
          refine ⟨13338023682895593859483165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17784031577194125145977553 13338023682895593859483165)
          ·
            refine ⟨5001758881085847697306187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13338023682895593859483165 5001758881085847697306187)
            ·
              refine ⟨7502638321628771545959281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001758881085847697306187 7502638321628771545959281)
              ·
                refine ⟨5626978741221578659469461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7502638321628771545959281 5626978741221578659469461)
                ·
                  refine ⟨263764628494761499662631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5626978741221578659469461 263764628494761499662631)
                  ·
                    rfl

theorem cell22_2311559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_2311559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311559 prefixEnd_2311559 := by exact prefixLift 2311559
  have htrace : WordTrace (prefixWord ++ tailWord_2311559) baseStart_2311559 baseEnd_2311559 := by
    simpa [prefixWord, tailWord_2311559, baseEnd_2311559] using wordTrace_append hprefix tailTrace_2311559
  have hstable : (prefixWord ++ tailWord_2311559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311559).length < 2 ^ (prefixWord ++ tailWord_2311559).sum := by decide
  have hdescent : baseEnd_2311559 < baseStart_2311559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311587 : List Nat := [1, 1, 1, 4, 1, 3, 11]
def baseStart_2311587 : Nat := 118140960795 + 2311587 * 2 ^ 59
def prefixEnd_2311587 : Nat := 4983230072969 + 3 ^ 40 * 2311587 * 2
def baseEnd_2311587 : Nat := 29307535942833398492141

theorem tailTrace_2311587 : CollatzResearch.WordTrace tailWord_2311587 prefixEnd_2311587 29307535942833398492141 := by
  unfold tailWord_2311587
  simp only [CollatzResearch.WordTrace]
  refine ⟨84310504276522561474061015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56207002851015040982707343 84310504276522561474061015)
  ·
    refine ⟨126465756414783842211091523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84310504276522561474061015 126465756414783842211091523)
    ·
      refine ⟨189698634622175763316637285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126465756414783842211091523 189698634622175763316637285)
      ·
        refine ⟨35568493991657955621869491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189698634622175763316637285 35568493991657955621869491)
        ·
          refine ⟨53352740987486933432804237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35568493991657955621869491 53352740987486933432804237)
          ·
            refine ⟨20007277870307600037301589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53352740987486933432804237 20007277870307600037301589)
            ·
              refine ⟨29307535942833398492141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20007277870307600037301589 29307535942833398492141)
              ·
                rfl

theorem cell22_2311587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 11].length) (baseStart_2311587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311587 prefixEnd_2311587 := by exact prefixLift 2311587
  have htrace : WordTrace (prefixWord ++ tailWord_2311587) baseStart_2311587 baseEnd_2311587 := by
    simpa [prefixWord, tailWord_2311587, baseEnd_2311587] using wordTrace_append hprefix tailTrace_2311587
  have hstable : (prefixWord ++ tailWord_2311587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311587).length < 2 ^ (prefixWord ++ tailWord_2311587).sum := by decide
  have hdescent : baseEnd_2311587 < baseStart_2311587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311591 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2311591 : Nat := 118140960795 + 2311591 * 2 ^ 59
def prefixEnd_2311591 : Nat := 4983230072969 + 3 ^ 40 * 2311591 * 2
def baseEnd_2311591 : Nat := 791304839738247082187795

theorem tailTrace_2311591 : CollatzResearch.WordTrace tailWord_2311591 prefixEnd_2311591 791304839738247082187795 := by
  unfold tailWord_2311591
  simp only [CollatzResearch.WordTrace]
  refine ⟨84310650168508070157206627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56207100112338713438137751 84310650168508070157206627)
  ·
    refine ⟨126465975252762105235809941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84310650168508070157206627 126465975252762105235809941)
    ·
      refine ⟨5928092589973223682928591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126465975252762105235809941 5928092589973223682928591)
      ·
        refine ⟨8892138884959835524392887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928092589973223682928591 8892138884959835524392887)
        ·
          refine ⟨13338208327439753286589331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8892138884959835524392887 13338208327439753286589331)
          ·
            refine ⟨20007312491159629929883997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13338208327439753286589331 20007312491159629929883997)
            ·
              refine ⟨7502742184184861223706499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20007312491159629929883997 7502742184184861223706499)
              ·
                refine ⟨11254113276277291835559749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502742184184861223706499 11254113276277291835559749)
                ·
                  refine ⟨2110146239301992219167453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11254113276277291835559749 2110146239301992219167453)
                  ·
                    refine ⟨791304839738247082187795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110146239301992219167453 791304839738247082187795)
                    ·
                      rfl

theorem cell22_2311591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2311591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311591 prefixEnd_2311591 := by exact prefixLift 2311591
  have htrace : WordTrace (prefixWord ++ tailWord_2311591) baseStart_2311591 baseEnd_2311591 := by
    simpa [prefixWord, tailWord_2311591, baseEnd_2311591] using wordTrace_append hprefix tailTrace_2311591
  have hstable : (prefixWord ++ tailWord_2311591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311591).length < 2 ^ (prefixWord ++ tailWord_2311591).sum := by decide
  have hdescent : baseEnd_2311591 < baseStart_2311591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311649 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 7]
def baseStart_2311649 : Nat := 118140960795 + 2311649 * 2 ^ 59
def prefixEnd_2311649 : Nat := 4983230072969 + 3 ^ 40 * 2311649 * 2
def baseEnd_2311649 : Nat := 263774898107851421412539

theorem tailTrace_2311649 : CollatzResearch.WordTrace tailWord_2311649 prefixEnd_2311649 263774898107851421412539 := by
  unfold tailWord_2311649
  simp only [CollatzResearch.WordTrace]
  refine ⟨84312765602297946062818001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56208510401531964041878667 84312765602297946062818001)
  ·
    refine ⟨63234574201723459547113501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84312765602297946062818001 63234574201723459547113501)
    ·
      refine ⟨23712965325646297330167563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63234574201723459547113501 23712965325646297330167563)
      ·
        refine ⟨35569447988469445995251345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23712965325646297330167563 35569447988469445995251345)
        ·
          refine ⟨26677085991352084496438509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35569447988469445995251345 26677085991352084496438509)
          ·
            refine ⟨10003907246757031686164441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26677085991352084496438509 10003907246757031686164441)
            ·
              refine ⟨7502930435067773764623331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10003907246757031686164441 7502930435067773764623331)
              ·
                refine ⟨11254395652601660646934997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502930435067773764623331 11254395652601660646934997)
                ·
                  refine ⟨263774898107851421412539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11254395652601660646934997 263774898107851421412539)
                  ·
                    rfl

theorem cell22_2311649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_2311649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311649 prefixEnd_2311649 := by exact prefixLift 2311649
  have htrace : WordTrace (prefixWord ++ tailWord_2311649) baseStart_2311649 baseEnd_2311649 := by
    simpa [prefixWord, tailWord_2311649, baseEnd_2311649] using wordTrace_append hprefix tailTrace_2311649
  have hstable : (prefixWord ++ tailWord_2311649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311649).length < 2 ^ (prefixWord ++ tailWord_2311649).sum := by decide
  have hdescent : baseEnd_2311649 < baseStart_2311649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311653 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_2311653 : Nat := 118140960795 + 2311653 * 2 ^ 59
def prefixEnd_2311653 : Nat := 4983230072969 + 3 ^ 40 * 2311653 * 2
def baseEnd_2311653 : Nat := 791326063605299587137605

theorem tailTrace_2311653 : CollatzResearch.WordTrace tailWord_2311653 prefixEnd_2311653 791326063605299587137605 := by
  unfold tailWord_2311653
  simp only [CollatzResearch.WordTrace]
  refine ⟨84312911494283454745963613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56208607662855636497309075 84312911494283454745963613)
  ·
    refine ⟨31617341810356295529736355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84312911494283454745963613 31617341810356295529736355)
    ·
      refine ⟨47426012715534443294604533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31617341810356295529736355 47426012715534443294604533)
      ·
        refine ⟨4446188692081354058869175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47426012715534443294604533 4446188692081354058869175)
        ·
          refine ⟨6669283038122031088303763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446188692081354058869175 6669283038122031088303763)
          ·
            refine ⟨10003924557183046632455645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6669283038122031088303763 10003924557183046632455645)
            ·
              refine ⟨3751471708943642487170867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10003924557183046632455645 3751471708943642487170867)
              ·
                refine ⟨5627207563415463730756301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751471708943642487170867 5627207563415463730756301)
                ·
                  refine ⟨2110202836280798899033613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5627207563415463730756301 2110202836280798899033613)
                  ·
                    refine ⟨791326063605299587137605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110202836280798899033613 791326063605299587137605)
                    ·
                      rfl

theorem cell22_2311653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_2311653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311653 prefixEnd_2311653 := by exact prefixLift 2311653
  have htrace : WordTrace (prefixWord ++ tailWord_2311653) baseStart_2311653 baseEnd_2311653 := by
    simpa [prefixWord, tailWord_2311653, baseEnd_2311653] using wordTrace_append hprefix tailTrace_2311653
  have hstable : (prefixWord ++ tailWord_2311653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311653).length < 2 ^ (prefixWord ++ tailWord_2311653).sum := by decide
  have hdescent : baseEnd_2311653 < baseStart_2311653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311700 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2311700 : Nat := 118140960795 + 2311700 * 2 ^ 59
def prefixEnd_2311700 : Nat := 4983230072969 + 3 ^ 40 * 2311700 * 2
def baseEnd_2311700 : Nat := 263780717555269043737487

theorem tailTrace_2311700 : CollatzResearch.WordTrace tailWord_2311700 prefixEnd_2311700 263780717555269043737487 := by
  unfold tailWord_2311700
  simp only [CollatzResearch.WordTrace]
  refine ⟨42157312862556590886462277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56209750483408787848616369 42157312862556590886462277)
  ·
    refine ⟨7904496161729360791211677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42157312862556590886462277 7904496161729360791211677)
    ·
      refine ⟨2964186060648510296704379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7904496161729360791211677 2964186060648510296704379)
      ·
        refine ⟨4446279090972765445056569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964186060648510296704379 4446279090972765445056569)
        ·
          refine ⟨3334709318229574083792427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4446279090972765445056569 3334709318229574083792427)
          ·
            refine ⟨5002063977344361125688641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334709318229574083792427 5002063977344361125688641)
            ·
              refine ⟨3751547983008270844266481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002063977344361125688641 3751547983008270844266481)
              ·
                refine ⟨2813660987256203133199861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3751547983008270844266481 2813660987256203133199861)
                ·
                  refine ⟨263780717555269043737487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2813660987256203133199861 263780717555269043737487)
                  ·
                    rfl

theorem cell22_2311700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2311700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311700 prefixEnd_2311700 := by exact prefixLift 2311700
  have htrace : WordTrace (prefixWord ++ tailWord_2311700) baseStart_2311700 baseEnd_2311700 := by
    simpa [prefixWord, tailWord_2311700, baseEnd_2311700] using wordTrace_append hprefix tailTrace_2311700
  have hstable : (prefixWord ++ tailWord_2311700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311700).length < 2 ^ (prefixWord ++ tailWord_2311700).sum := by decide
  have hdescent : baseEnd_2311700 < baseStart_2311700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311704 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 1, 3]
def baseStart_2311704 : Nat := 118140960795 + 2311704 * 2 ^ 59
def prefixEnd_2311704 : Nat := 4983230072969 + 3 ^ 40 * 2311704 * 2
def baseEnd_2311704 : Nat := 791343521947552454112449

theorem tailTrace_2311704 : CollatzResearch.WordTrace tailWord_2311704 prefixEnd_2311704 791343521947552454112449 := by
  unfold tailWord_2311704
  simp only [CollatzResearch.WordTrace]
  refine ⟨42157385808549345228035083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56209847744732460304046777 42157385808549345228035083)
  ·
    refine ⟨63236078712824017842052625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42157385808549345228035083 63236078712824017842052625)
    ·
      refine ⟨47427059034618013381539469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63236078712824017842052625 47427059034618013381539469)
      ·
        refine ⟨17785147137981755018077301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47427059034618013381539469 17785147137981755018077301)
        ·
          refine ⟨1667357544185789532944747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17785147137981755018077301 1667357544185789532944747)
          ·
            refine ⟨2501036316278684299417121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667357544185789532944747 2501036316278684299417121)
            ·
              refine ⟨1875777237209013224562841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501036316278684299417121 1875777237209013224562841)
              ·
                refine ⟨1406832927906759918422131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875777237209013224562841 1406832927906759918422131)
                ·
                  refine ⟨2110249391860139877633197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406832927906759918422131 2110249391860139877633197)
                  ·
                    refine ⟨791343521947552454112449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110249391860139877633197 791343521947552454112449)
                    ·
                      rfl

theorem cell22_2311704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_2311704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311704 prefixEnd_2311704 := by exact prefixLift 2311704
  have htrace : WordTrace (prefixWord ++ tailWord_2311704) baseStart_2311704 baseEnd_2311704 := by
    simpa [prefixWord, tailWord_2311704, baseEnd_2311704] using wordTrace_append hprefix tailTrace_2311704
  have hstable : (prefixWord ++ tailWord_2311704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311704).length < 2 ^ (prefixWord ++ tailWord_2311704).sum := by decide
  have hdescent : baseEnd_2311704 < baseStart_2311704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311769 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_2311769 : Nat := 118140960795 + 2311769 * 2 ^ 59
def prefixEnd_2311769 : Nat := 4983230072969 + 3 ^ 40 * 2311769 * 2
def baseEnd_2311769 : Nat := 791365772775913951237249

theorem tailTrace_2311769 : CollatzResearch.WordTrace tailWord_2311769 prefixEnd_2311769 791365772775913951237249 := by
  unfold tailWord_2311769
  simp only [CollatzResearch.WordTrace]
  refine ⟨84317142361863206557186361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56211428241242137704790907 84317142361863206557186361)
  ·
    refine ⟨63237856771397404917889771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84317142361863206557186361 63237856771397404917889771)
    ·
      refine ⟨94856785157096107376834657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63237856771397404917889771 94856785157096107376834657)
      ·
        refine ⟨71142588867822080532625993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94856785157096107376834657 71142588867822080532625993)
        ·
          refine ⟨53356941650866560399469495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71142588867822080532625993 53356941650866560399469495)
          ·
            refine ⟨80035412476299840599204243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53356941650866560399469495 80035412476299840599204243)
            ·
              refine ⟨120053118714449760898806365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80035412476299840599204243 120053118714449760898806365)
              ·
                refine ⟨45019919517918660337052387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120053118714449760898806365 45019919517918660337052387)
                ·
                  refine ⟨67529879276877990505578581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45019919517918660337052387 67529879276877990505578581)
                  ·
                    refine ⟨791365772775913951237249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67529879276877990505578581 791365772775913951237249)
                    ·
                      rfl

theorem cell22_2311769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_2311769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311769 prefixEnd_2311769 := by exact prefixLift 2311769
  have htrace : WordTrace (prefixWord ++ tailWord_2311769) baseStart_2311769 baseEnd_2311769 := by
    simpa [prefixWord, tailWord_2311769, baseEnd_2311769] using wordTrace_append hprefix tailTrace_2311769
  have hstable : (prefixWord ++ tailWord_2311769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311769).length < 2 ^ (prefixWord ++ tailWord_2311769).sum := by decide
  have hdescent : baseEnd_2311769 < baseStart_2311769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311790 : List Nat := [4, 1, 2, 2, 3, 2, 2, 6]
def baseStart_2311790 : Nat := 118140960795 + 2311790 * 2 ^ 59
def prefixEnd_2311790 : Nat := 4983230072969 + 3 ^ 40 * 2311790 * 2
def baseEnd_2311790 : Nat := 87930329056119655162465

theorem tailTrace_2311790 : CollatzResearch.WordTrace tailWord_2311790 prefixEnd_2311790 87930329056119655162465 := by
  unfold tailWord_2311790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539738536848390892962603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56211938863191418095800549 10539738536848390892962603)
  ·
    refine ⟨15809607805272586339443905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10539738536848390892962603 15809607805272586339443905)
    ·
      refine ⟨11857205853954439754582929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15809607805272586339443905 11857205853954439754582929)
      ·
        refine ⟨8892904390465829815937197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11857205853954439754582929 8892904390465829815937197)
        ·
          refine ⟨3334839146424686180976449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8892904390465829815937197 3334839146424686180976449)
          ·
            refine ⟨2501129359818514635732337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3334839146424686180976449 2501129359818514635732337)
            ·
              refine ⟨1875847019863885976799253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501129359818514635732337 1875847019863885976799253)
              ·
                refine ⟨87930329056119655162465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1875847019863885976799253 87930329056119655162465)
                ·
                  rfl

theorem cell22_2311790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_2311790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311790 prefixEnd_2311790 := by exact prefixLift 2311790
  have htrace : WordTrace (prefixWord ++ tailWord_2311790) baseStart_2311790 baseEnd_2311790 := by
    simpa [prefixWord, tailWord_2311790, baseEnd_2311790] using wordTrace_append hprefix tailTrace_2311790
  have hstable : (prefixWord ++ tailWord_2311790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311790).length < 2 ^ (prefixWord ++ tailWord_2311790).sum := by decide
  have hdescent : baseEnd_2311790 < baseStart_2311790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311908 : List Nat := [2, 3, 1, 1, 1, 3, 5, 6]
def baseStart_2311908 : Nat := 118140960795 + 2311908 * 2 ^ 59
def prefixEnd_2311908 : Nat := 4983230072969 + 3 ^ 40 * 2311908 * 2
def baseEnd_2311908 : Nat := 87934817257395991334647

theorem tailTrace_2311908 : CollatzResearch.WordTrace tailWord_2311908 prefixEnd_2311908 87934817257395991334647 := by
  unfold tailWord_2311908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161106054179816648248189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56214808072239755530997585 42161106054179816648248189)
  ·
    refine ⟨15810414770317431243093071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42161106054179816648248189 15810414770317431243093071)
    ·
      refine ⟨23715622155476146864639607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15810414770317431243093071 23715622155476146864639607)
      ·
        refine ⟨35573433233214220296959411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23715622155476146864639607 35573433233214220296959411)
        ·
          refine ⟨53360149849821330445439117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35573433233214220296959411 53360149849821330445439117)
          ·
            refine ⟨20010056193682998917039669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53360149849821330445439117 20010056193682998917039669)
            ·
              refine ⟨1875942768157781148472469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20010056193682998917039669 1875942768157781148472469)
              ·
                refine ⟨87934817257395991334647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1875942768157781148472469 87934817257395991334647)
                ·
                  rfl

theorem cell22_2311908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_2311908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311908 prefixEnd_2311908 := by exact prefixLift 2311908
  have htrace : WordTrace (prefixWord ++ tailWord_2311908) baseStart_2311908 baseEnd_2311908 := by
    simpa [prefixWord, tailWord_2311908, baseEnd_2311908] using wordTrace_append hprefix tailTrace_2311908
  have hstable : (prefixWord ++ tailWord_2311908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311908).length < 2 ^ (prefixWord ++ tailWord_2311908).sum := by decide
  have hdescent : baseEnd_2311908 < baseStart_2311908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311936 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_2311936 : Nat := 118140960795 + 2311936 * 2 ^ 59
def prefixEnd_2311936 : Nat := 4983230072969 + 3 ^ 40 * 2311936 * 2
def baseEnd_2311936 : Nat := 263807646762927060770579

theorem tailTrace_2311936 : CollatzResearch.WordTrace tailWord_2311936 prefixEnd_2311936 263807646762927060770579 := by
  unfold tailWord_2311936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161616676129097039257831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56215488901505462719010441 42161616676129097039257831)
  ·
    refine ⟨63242425014193645558886747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42161616676129097039257831 63242425014193645558886747)
    ·
      refine ⟨94863637521290468338330121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63242425014193645558886747 94863637521290468338330121)
      ·
        refine ⟨71147728140967851253747591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94863637521290468338330121 71147728140967851253747591)
        ·
          refine ⟨106721592211451776880621387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71147728140967851253747591 106721592211451776880621387)
          ·
            refine ⟨160082388317177665320932081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106721592211451776880621387 160082388317177665320932081)
            ·
              refine ⟨120061791237883248990699061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160082388317177665320932081 120061791237883248990699061)
              ·
                refine ⟨11255792928551554592878037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120061791237883248990699061 11255792928551554592878037)
                ·
                  refine ⟨263807646762927060770579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11255792928551554592878037 263807646762927060770579)
                  ·
                    rfl

theorem cell22_2311936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_2311936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311936 prefixEnd_2311936 := by exact prefixLift 2311936
  have htrace : WordTrace (prefixWord ++ tailWord_2311936) baseStart_2311936 baseEnd_2311936 := by
    simpa [prefixWord, tailWord_2311936, baseEnd_2311936] using wordTrace_append hprefix tailTrace_2311936
  have hstable : (prefixWord ++ tailWord_2311936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311936).length < 2 ^ (prefixWord ++ tailWord_2311936).sum := by decide
  have hdescent : baseEnd_2311936 < baseStart_2311936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311940 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_2311940 : Nat := 118140960795 + 2311940 * 2 ^ 59
def prefixEnd_2311940 : Nat := 4983230072969 + 3 ^ 40 * 2311940 * 2
def baseEnd_2311940 : Nat := 791424309570526505211725

theorem tailTrace_2311940 : CollatzResearch.WordTrace tailWord_2311940 prefixEnd_2311940 791424309570526505211725 := by
  unfold tailWord_2311940
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161689622121851380830637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56215586162829135174440849 42161689622121851380830637)
  ·
    refine ⟨15810633608295694267811489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42161689622121851380830637 15810633608295694267811489)
    ·
      refine ⟨11857975206221770700858617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15810633608295694267811489 11857975206221770700858617)
      ·
        refine ⟨8893481404666328025643963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11857975206221770700858617 8893481404666328025643963)
        ·
          refine ⟨13340222106999492038465945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8893481404666328025643963 13340222106999492038465945)
          ·
            refine ⟨10005166580249619028849459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13340222106999492038465945 10005166580249619028849459)
            ·
              refine ⟨15007749870374428543274189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10005166580249619028849459 15007749870374428543274189)
              ·
                refine ⟨5627906201390410703727821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15007749870374428543274189 5627906201390410703727821)
                ·
                  refine ⟨2110464825521404013897933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5627906201390410703727821 2110464825521404013897933)
                  ·
                    refine ⟨791424309570526505211725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110464825521404013897933 791424309570526505211725)
                    ·
                      rfl

theorem cell22_2311940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_2311940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311940 prefixEnd_2311940 := by exact prefixLift 2311940
  have htrace : WordTrace (prefixWord ++ tailWord_2311940) baseStart_2311940 baseEnd_2311940 := by
    simpa [prefixWord, tailWord_2311940, baseEnd_2311940] using wordTrace_append hprefix tailTrace_2311940
  have hstable : (prefixWord ++ tailWord_2311940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311940).length < 2 ^ (prefixWord ++ tailWord_2311940).sum := by decide
  have hdescent : baseEnd_2311940 < baseStart_2311940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2311951 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_2311951 : Nat := 118140960795 + 2311951 * 2 ^ 59
def prefixEnd_2311951 : Nat := 4983230072969 + 3 ^ 40 * 2311951 * 2
def baseEnd_2311951 : Nat := 791428075095326143186691

theorem tailTrace_2311951 : CollatzResearch.WordTrace tailWord_2311951 prefixEnd_2311951 791428075095326143186691 := by
  unfold tailWord_2311951
  simp only [CollatzResearch.WordTrace]
  refine ⟨84323780447203851640311707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56215853631469234426874471 84323780447203851640311707)
  ·
    refine ⟨126485670670805777460467561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84323780447203851640311707 126485670670805777460467561)
    ·
      refine ⟨94864253003104333095350671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126485670670805777460467561 94864253003104333095350671)
      ·
        refine ⟨142296379504656499643026007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94864253003104333095350671 142296379504656499643026007)
        ·
          refine ⟨213444569256984749464539011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142296379504656499643026007 213444569256984749464539011)
          ·
            refine ⟨320166853885477124196808517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213444569256984749464539011 320166853885477124196808517)
            ·
              refine ⟨60031285103526960786901597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320166853885477124196808517 60031285103526960786901597)
              ·
                refine ⟨22511731913822610295088099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60031285103526960786901597 22511731913822610295088099)
                ·
                  refine ⟨33767597870733915442632149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22511731913822610295088099 33767597870733915442632149)
                  ·
                    refine ⟨791428075095326143186691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33767597870733915442632149 791428075095326143186691)
                    ·
                      rfl

theorem cell22_2311951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_2311951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2311951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2311951 prefixEnd_2311951 := by exact prefixLift 2311951
  have htrace : WordTrace (prefixWord ++ tailWord_2311951) baseStart_2311951 baseEnd_2311951 := by
    simpa [prefixWord, tailWord_2311951, baseEnd_2311951] using wordTrace_append hprefix tailTrace_2311951
  have hstable : (prefixWord ++ tailWord_2311951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2311951).length < 2 ^ (prefixWord ++ tailWord_2311951).sum := by decide
  have hdescent : baseEnd_2311951 < baseStart_2311951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2311951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312017 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_2312017 : Nat := 118140960795 + 2312017 * 2 ^ 59
def prefixEnd_2312017 : Nat := 4983230072969 + 3 ^ 40 * 2312017 * 2
def baseEnd_2312017 : Nat := 791450668244123971036489

theorem tailTrace_2312017 : CollatzResearch.WordTrace tailWord_2312017 prefixEnd_2312017 791450668244123971036489 := by
  unfold tailWord_2312017
  simp only [CollatzResearch.WordTrace]
  refine ⟨84326187664964744912214305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56217458443309829941476203 84326187664964744912214305)
  ·
    refine ⟨63244640748723558684160729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84326187664964744912214305 63244640748723558684160729)
    ·
      refine ⟨47433480561542669013120547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63244640748723558684160729 47433480561542669013120547)
      ·
        refine ⟨71150220842314003519680821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47433480561542669013120547 71150220842314003519680821)
        ·
          refine ⟨6670333203966937829970077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71150220842314003519680821 6670333203966937829970077)
          ·
            refine ⟨2501374951487601686238779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6670333203966937829970077 2501374951487601686238779)
            ·
              refine ⟨3752062427231402529358169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501374951487601686238779 3752062427231402529358169)
              ·
                refine ⟨2814046820423551897018627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752062427231402529358169 2814046820423551897018627)
                ·
                  refine ⟨4221070230635327845527941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814046820423551897018627 4221070230635327845527941)
                  ·
                    refine ⟨791450668244123971036489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221070230635327845527941 791450668244123971036489)
                    ·
                      rfl

theorem cell22_2312017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_2312017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312017 prefixEnd_2312017 := by exact prefixLift 2312017
  have htrace : WordTrace (prefixWord ++ tailWord_2312017) baseStart_2312017 baseEnd_2312017 := by
    simpa [prefixWord, tailWord_2312017, baseEnd_2312017] using wordTrace_append hprefix tailTrace_2312017
  have hstable : (prefixWord ++ tailWord_2312017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312017).length < 2 ^ (prefixWord ++ tailWord_2312017).sum := by decide
  have hdescent : baseEnd_2312017 < baseStart_2312017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312034 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2312034 : Nat := 118140960795 + 2312034 * 2 ^ 59
def prefixEnd_2312034 : Nat := 4983230072969 + 3 ^ 40 * 2312034 * 2
def baseEnd_2312034 : Nat := 791456487691541593361437

theorem tailTrace_2312034 : CollatzResearch.WordTrace tailWord_2312034 prefixEnd_2312034 791456487691541593361437 := by
  unfold tailWord_2312034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21081701926475789203895789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56217871803935437877055437 21081701926475789203895789)
  ·
    refine ⟨7905638222428420951460921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21081701926475789203895789 7905638222428420951460921)
    ·
      refine ⟨5929228666821315713595691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7905638222428420951460921 5929228666821315713595691)
      ·
        refine ⟨8893843000231973570393537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5929228666821315713595691 8893843000231973570393537)
        ·
          refine ⟨6670382250173980177795153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8893843000231973570393537 6670382250173980177795153)
          ·
            refine ⟨5002786687630485133346365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6670382250173980177795153 5002786687630485133346365)
            ·
              refine ⟨1876045007861431925004887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5002786687630485133346365 1876045007861431925004887)
              ·
                refine ⟨2814067511792147887507331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876045007861431925004887 2814067511792147887507331)
                ·
                  refine ⟨4221101267688221831260997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814067511792147887507331 4221101267688221831260997)
                  ·
                    refine ⟨791456487691541593361437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221101267688221831260997 791456487691541593361437)
                    ·
                      rfl

theorem cell22_2312034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2312034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312034 prefixEnd_2312034 := by exact prefixLift 2312034
  have htrace : WordTrace (prefixWord ++ tailWord_2312034) baseStart_2312034 baseEnd_2312034 := by
    simpa [prefixWord, tailWord_2312034, baseEnd_2312034] using wordTrace_append hprefix tailTrace_2312034
  have hstable : (prefixWord ++ tailWord_2312034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312034).length < 2 ^ (prefixWord ++ tailWord_2312034).sum := by decide
  have hdescent : baseEnd_2312034 < baseStart_2312034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312045 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2312045 : Nat := 118140960795 + 2312045 * 2 ^ 59
def prefixEnd_2312045 : Nat := 4983230072969 + 3 ^ 40 * 2312045 * 2
def baseEnd_2312045 : Nat := 791460253216341231336403

theorem tailTrace_2312045 : CollatzResearch.WordTrace tailWord_2312045 prefixEnd_2312045 791460253216341231336403 := by
  unfold tailWord_2312045
  simp only [CollatzResearch.WordTrace]
  refine ⟨84327208908863305694233589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56218139272575537129489059 84327208908863305694233589)
  ·
    refine ⟨7905675835205934908834399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84327208908863305694233589 7905675835205934908834399)
    ·
      refine ⟨11858513752808902363251599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7905675835205934908834399 11858513752808902363251599)
      ·
        refine ⟨17787770629213353544877399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11858513752808902363251599 17787770629213353544877399)
        ·
          refine ⟨26681655943820030317316099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17787770629213353544877399 26681655943820030317316099)
          ·
            refine ⟨40022483915730045475974149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26681655943820030317316099 40022483915730045475974149)
            ·
              refine ⟨7504215734199383526745153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40022483915730045475974149 7504215734199383526745153)
              ·
                refine ⟨5628161800649537645058865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7504215734199383526745153 5628161800649537645058865)
                ·
                  refine ⟨4221121350487153233794149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628161800649537645058865 4221121350487153233794149)
                  ·
                    refine ⟨791460253216341231336403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221121350487153233794149 791460253216341231336403)
                    ·
                      rfl

theorem cell22_2312045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2312045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312045 prefixEnd_2312045 := by exact prefixLift 2312045
  have htrace : WordTrace (prefixWord ++ tailWord_2312045) baseStart_2312045 baseEnd_2312045 := by
    simpa [prefixWord, tailWord_2312045, baseEnd_2312045] using wordTrace_append hprefix tailTrace_2312045
  have hstable : (prefixWord ++ tailWord_2312045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312045).length < 2 ^ (prefixWord ++ tailWord_2312045).sum := by decide
  have hdescent : baseEnd_2312045 < baseStart_2312045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312073 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_2312073 : Nat := 118140960795 + 2312073 * 2 ^ 59
def prefixEnd_2312073 : Nat := 4983230072969 + 3 ^ 40 * 2312073 * 2
def baseEnd_2312073 : Nat := 791469838188558491636317

theorem tailTrace_2312073 : CollatzResearch.WordTrace tailWord_2312073 prefixEnd_2312073 791469838188558491636317 := by
  unfold tailWord_2312073
  simp only [CollatzResearch.WordTrace]
  refine ⟨84328230152761866476252873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56218820101841244317501915 84328230152761866476252873)
  ·
    refine ⟨63246172614571399857189655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84328230152761866476252873 63246172614571399857189655)
    ·
      refine ⟨94869258921857099785784483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63246172614571399857189655 94869258921857099785784483)
      ·
        refine ⟨142303888382785649678676725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94869258921857099785784483 142303888382785649678676725)
        ·
          refine ⟨13340989535886154657375943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142303888382785649678676725 13340989535886154657375943)
          ·
            refine ⟨20011484303829231986063915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13340989535886154657375943 20011484303829231986063915)
            ·
              refine ⟨30017226455743847979095873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20011484303829231986063915 30017226455743847979095873)
              ·
                refine ⟨22512919841807885984321905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30017226455743847979095873 22512919841807885984321905)
                ·
                  refine ⟨16884689881355914488241429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22512919841807885984321905 16884689881355914488241429)
                  ·
                    refine ⟨791469838188558491636317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16884689881355914488241429 791469838188558491636317)
                    ·
                      rfl

theorem cell22_2312073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_2312073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312073 prefixEnd_2312073 := by exact prefixLift 2312073
  have htrace : WordTrace (prefixWord ++ tailWord_2312073) baseStart_2312073 baseEnd_2312073 := by
    simpa [prefixWord, tailWord_2312073, baseEnd_2312073] using wordTrace_append hprefix tailTrace_2312073
  have hstable : (prefixWord ++ tailWord_2312073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312073).length < 2 ^ (prefixWord ++ tailWord_2312073).sum := by decide
  have hdescent : baseEnd_2312073 < baseStart_2312073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312133 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 8]
def baseStart_2312133 : Nat := 118140960795 + 2312133 * 2 ^ 59
def prefixEnd_2312133 : Nat := 4983230072969 + 3 ^ 40 * 2312133 * 2
def baseEnd_2312133 : Nat := 263830125804912778378711

theorem tailTrace_2312133 : CollatzResearch.WordTrace tailWord_2312133 prefixEnd_2312133 263830125804912778378711 := by
  unfold tailWord_2312133
  simp only [CollatzResearch.WordTrace]
  refine ⟨84330418532544496723437053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56220279021696331148958035 84330418532544496723437053)
  ·
    refine ⟨31623906949704186271288895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84330418532544496723437053 31623906949704186271288895)
    ·
      refine ⟨47435860424556279406933343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31623906949704186271288895 47435860424556279406933343)
      ·
        refine ⟨71153790636834419110400015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47435860424556279406933343 71153790636834419110400015)
        ·
          refine ⟨106730685955251628665600023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71153790636834419110400015 106730685955251628665600023)
          ·
            refine ⟨160096028932877442998400035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106730685955251628665600023 160096028932877442998400035)
            ·
              refine ⟨240144043399316164497600053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160096028932877442998400035 240144043399316164497600053)
              ·
                refine ⟨22513504068685890421650005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240144043399316164497600053 22513504068685890421650005)
                ·
                  refine ⟨263830125804912778378711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22513504068685890421650005 263830125804912778378711)
                  ·
                    rfl

theorem cell22_2312133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_2312133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312133 prefixEnd_2312133 := by exact prefixLift 2312133
  have htrace : WordTrace (prefixWord ++ tailWord_2312133) baseStart_2312133 baseEnd_2312133 := by
    simpa [prefixWord, tailWord_2312133, baseEnd_2312133] using wordTrace_append hprefix tailTrace_2312133
  have hstable : (prefixWord ++ tailWord_2312133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312133).length < 2 ^ (prefixWord ++ tailWord_2312133).sum := by decide
  have hdescent : baseEnd_2312133 < baseStart_2312133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312173 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2312173 : Nat := 118140960795 + 2312173 * 2 ^ 59
def prefixEnd_2312173 : Nat := 4983230072969 + 3 ^ 40 * 2312173 * 2
def baseEnd_2312173 : Nat := 263834690077397188045337

theorem tailTrace_2312173 : CollatzResearch.WordTrace tailWord_2312173 prefixEnd_2312173 263834690077397188045337 := by
  unfold tailWord_2312173
  simp only [CollatzResearch.WordTrace]
  refine ⟨84331877452399583554893173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56221251634933055703262115 84331877452399583554893173)
  ·
    refine ⟨7906113511162460958271235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84331877452399583554893173 7906113511162460958271235)
    ·
      refine ⟨11859170266743691437406853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7906113511162460958271235 11859170266743691437406853)
      ·
        refine ⟨2223594425014442144513785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11859170266743691437406853 2223594425014442144513785)
        ·
          refine ⟨1667695818760831608385339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2223594425014442144513785 1667695818760831608385339)
          ·
            refine ⟨2501543728141247412578009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667695818760831608385339 2501543728141247412578009)
            ·
              refine ⟨1876157796105935559433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501543728141247412578009 1876157796105935559433507)
              ·
                refine ⟨2814236694158903339150261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876157796105935559433507 2814236694158903339150261)
                ·
                  refine ⟨263834690077397188045337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814236694158903339150261 263834690077397188045337)
                  ·
                    rfl

theorem cell22_2312173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2312173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312173 prefixEnd_2312173 := by exact prefixLift 2312173
  have htrace : WordTrace (prefixWord ++ tailWord_2312173) baseStart_2312173 baseEnd_2312173 := by
    simpa [prefixWord, tailWord_2312173, baseEnd_2312173] using wordTrace_append hprefix tailTrace_2312173
  have hstable : (prefixWord ++ tailWord_2312173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312173).length < 2 ^ (prefixWord ++ tailWord_2312173).sum := by decide
  have hdescent : baseEnd_2312173 < baseStart_2312173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312197 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_2312197 : Nat := 118140960795 + 2312197 * 2 ^ 59
def prefixEnd_2312197 : Nat := 4983230072969 + 3 ^ 40 * 2312197 * 2
def baseEnd_2312197 : Nat := 791512285922663501535937

theorem tailTrace_2312197 : CollatzResearch.WordTrace tailWord_2312197 prefixEnd_2312197 791512285922663501535937 := by
  unfold tailWord_2312197
  simp only [CollatzResearch.WordTrace]
  refine ⟨84332752804312635653766845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56221835202875090435844563 84332752804312635653766845)
  ·
    refine ⟨31624782301617238370162567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84332752804312635653766845 31624782301617238370162567)
    ·
      refine ⟨47437173452425857555243851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31624782301617238370162567 47437173452425857555243851)
      ·
        refine ⟨71155760178638786332865777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47437173452425857555243851 71155760178638786332865777)
        ·
          refine ⟨53366820133979089749649333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71155760178638786332865777 53366820133979089749649333)
          ·
            refine ⟨5003139387560539664029625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53366820133979089749649333 5003139387560539664029625)
            ·
              refine ⟨3752354540670404748022219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003139387560539664029625 3752354540670404748022219)
              ·
                refine ⟨5628531811005607122033329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752354540670404748022219 5628531811005607122033329)
                ·
                  refine ⟨4221398858254205341524997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5628531811005607122033329 4221398858254205341524997)
                  ·
                    refine ⟨791512285922663501535937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221398858254205341524997 791512285922663501535937)
                    ·
                      rfl

theorem cell22_2312197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_2312197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312197 prefixEnd_2312197 := by exact prefixLift 2312197
  have htrace : WordTrace (prefixWord ++ tailWord_2312197) baseStart_2312197 baseEnd_2312197 := by
    simpa [prefixWord, tailWord_2312197, baseEnd_2312197] using wordTrace_append hprefix tailTrace_2312197
  have hstable : (prefixWord ++ tailWord_2312197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312197).length < 2 ^ (prefixWord ++ tailWord_2312197).sum := by decide
  have hdescent : baseEnd_2312197 < baseStart_2312197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312212 : List Nat := [2, 4, 3, 2, 11]
def baseStart_2312212 : Nat := 118140960795 + 2312212 * 2 ^ 59
def prefixEnd_2312212 : Nat := 4983230072969 + 3 ^ 40 * 2312212 * 2
def baseEnd_2312212 : Nat := 3257273336334191203337

theorem tailTrace_2312212 : CollatzResearch.WordTrace tailWord_2312212 prefixEnd_2312212 3257273336334191203337 := by
  unfold tailWord_2312212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42166649949629146607781445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56222199932838862143708593 42166649949629146607781445)
  ·
    refine ⟨7906246865555464988959021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42166649949629146607781445 7906246865555464988959021)
    ·
      refine ⟨2964842574583299370859633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7906246865555464988959021 2964842574583299370859633)
      ·
        refine ⟨2223631930937474528144725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2964842574583299370859633 2223631930937474528144725)
        ·
          refine ⟨3257273336334191203337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2223631930937474528144725 3257273336334191203337)
          ·
            rfl

theorem cell22_2312212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 11].length) (baseStart_2312212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312212 prefixEnd_2312212 := by exact prefixLift 2312212
  have htrace : WordTrace (prefixWord ++ tailWord_2312212) baseStart_2312212 baseEnd_2312212 := by
    simpa [prefixWord, tailWord_2312212, baseEnd_2312212] using wordTrace_append hprefix tailTrace_2312212
  have hstable : (prefixWord ++ tailWord_2312212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312212).length < 2 ^ (prefixWord ++ tailWord_2312212).sum := by decide
  have hdescent : baseEnd_2312212 < baseStart_2312212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312227 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 3, 3]
def baseStart_2312227 : Nat := 118140960795 + 2312227 * 2 ^ 59
def prefixEnd_2312227 : Nat := 4983230072969 + 3 ^ 40 * 2312227 * 2
def baseEnd_2312227 : Nat := 791522555535753423285845

theorem tailTrace_2312227 : CollatzResearch.WordTrace tailWord_2312227 prefixEnd_2312227 791522555535753423285845 := by
  unfold tailWord_2312227
  simp only [CollatzResearch.WordTrace]
  refine ⟨84333846994203950777358935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56222564662802633851572623 84333846994203950777358935)
  ·
    refine ⟨126500770491305926166038403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84333846994203950777358935 126500770491305926166038403)
    ·
      refine ⟨189751155736958889249057605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126500770491305926166038403 189751155736958889249057605)
      ·
        refine ⟨35578341700679791734198301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189751155736958889249057605 35578341700679791734198301)
        ·
          refine ⟨13341878137754921900324363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35578341700679791734198301 13341878137754921900324363)
          ·
            refine ⟨20012817206632382850486545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13341878137754921900324363 20012817206632382850486545)
            ·
              refine ⟨15009612904974287137864909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20012817206632382850486545 15009612904974287137864909)
              ·
                refine ⟨5628604839365357676699341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15009612904974287137864909 5628604839365357676699341)
                ·
                  refine ⟨2110726814762009128762253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5628604839365357676699341 2110726814762009128762253)
                  ·
                    refine ⟨791522555535753423285845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110726814762009128762253 791522555535753423285845)
                    ·
                      rfl

theorem cell22_2312227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3].length) (baseStart_2312227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312227 prefixEnd_2312227 := by exact prefixLift 2312227
  have htrace : WordTrace (prefixWord ++ tailWord_2312227) baseStart_2312227 baseEnd_2312227 := by
    simpa [prefixWord, tailWord_2312227, baseEnd_2312227] using wordTrace_append hprefix tailTrace_2312227
  have hstable : (prefixWord ++ tailWord_2312227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312227).length < 2 ^ (prefixWord ++ tailWord_2312227).sum := by decide
  have hdescent : baseEnd_2312227 < baseStart_2312227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312278 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2312278 : Nat := 118140960795 + 2312278 * 2 ^ 59
def prefixEnd_2312278 : Nat := 4983230072969 + 3 ^ 40 * 2312278 * 2
def baseEnd_2312278 : Nat := 791540013878006290260689

theorem tailTrace_2312278 : CollatzResearch.WordTrace tailWord_2312278 prefixEnd_2312278 791540013878006290260689 := by
  unfold tailWord_2312278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270981694813699155466593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56223804744679457658310325 5270981694813699155466593)
  ·
    refine ⟨3953236271110274366599945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5270981694813699155466593 3953236271110274366599945)
    ·
      refine ⟨2964927203332705774949959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3953236271110274366599945 2964927203332705774949959)
      ·
        refine ⟨4447390804999058662424939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964927203332705774949959 4447390804999058662424939)
        ·
          refine ⟨6671086207498587993637409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447390804999058662424939 6671086207498587993637409)
          ·
            refine ⟨5003314655623940995228057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6671086207498587993637409 5003314655623940995228057)
            ·
              refine ⟨3752485991717955746421043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003314655623940995228057 3752485991717955746421043)
              ·
                refine ⟨5628728987576933619631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752485991717955746421043 5628728987576933619631565)
                ·
                  refine ⟨2110773370341350107361837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5628728987576933619631565 2110773370341350107361837)
                  ·
                    refine ⟨791540013878006290260689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110773370341350107361837 791540013878006290260689)
                    ·
                      rfl

theorem cell22_2312278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2312278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312278 prefixEnd_2312278 := by exact prefixLift 2312278
  have htrace : WordTrace (prefixWord ++ tailWord_2312278) baseStart_2312278 baseEnd_2312278 := by
    simpa [prefixWord, tailWord_2312278, baseEnd_2312278] using wordTrace_append hprefix tailTrace_2312278
  have hstable : (prefixWord ++ tailWord_2312278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312278).length < 2 ^ (prefixWord ++ tailWord_2312278).sum := by decide
  have hdescent : baseEnd_2312278 < baseStart_2312278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312302 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2312302 : Nat := 118140960795 + 2312302 * 2 ^ 59
def prefixEnd_2312302 : Nat := 4983230072969 + 3 ^ 40 * 2312302 * 2
def baseEnd_2312302 : Nat := 263849409856159409220205

theorem tailTrace_2312302 : CollatzResearch.WordTrace tailWord_2312302 prefixEnd_2312302 263849409856159409220205 := by
  unfold tailWord_2312302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542072808616529823292395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56224388312621492390892773 10542072808616529823292395)
  ·
    refine ⟨15813109212924794734938593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10542072808616529823292395 15813109212924794734938593)
    ·
      refine ⟨11859831909693596051203945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15813109212924794734938593 11859831909693596051203945)
      ·
        refine ⟨8894873932270197038402959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11859831909693596051203945 8894873932270197038402959)
        ·
          refine ⟨13342310898405295557604439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8894873932270197038402959 13342310898405295557604439)
          ·
            refine ⟨20013466347607943336406659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13342310898405295557604439 20013466347607943336406659)
            ·
              refine ⟨30020199521411915004609989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20013466347607943336406659 30020199521411915004609989)
              ·
                refine ⟨5628787410264734063364373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30020199521411915004609989 5628787410264734063364373)
                ·
                  refine ⟨263849409856159409220205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5628787410264734063364373 263849409856159409220205)
                  ·
                    rfl

theorem cell22_2312302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2312302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312302 prefixEnd_2312302 := by exact prefixLift 2312302
  have htrace : WordTrace (prefixWord ++ tailWord_2312302) baseStart_2312302 baseEnd_2312302 := by
    simpa [prefixWord, tailWord_2312302, baseEnd_2312302] using wordTrace_append hprefix tailTrace_2312302
  have hstable : (prefixWord ++ tailWord_2312302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312302).length < 2 ^ (prefixWord ++ tailWord_2312302).sum := by decide
  have hdescent : baseEnd_2312302 < baseStart_2312302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312304 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_2312304 : Nat := 118140960795 + 2312304 * 2 ^ 59
def prefixEnd_2312304 : Nat := 4983230072969 + 3 ^ 40 * 2312304 * 2
def baseEnd_2312304 : Nat := 791548914209350889110609

theorem tailTrace_2312304 : CollatzResearch.WordTrace tailWord_2312304 prefixEnd_2312304 791548914209350889110609 := by
  unfold tailWord_2312304
  simp only [CollatzResearch.WordTrace]
  refine ⟨42168327707462496463955983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56224436943283328618607977 42168327707462496463955983)
  ·
    refine ⟨63252491561193744695933975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42168327707462496463955983 63252491561193744695933975)
    ·
      refine ⟨94878737341790617043900963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63252491561193744695933975 94878737341790617043900963)
      ·
        refine ⟨142318106012685925565851445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94878737341790617043900963 142318106012685925565851445)
        ·
          refine ⟨13342322438689305521798573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142318106012685925565851445 13342322438689305521798573)
          ·
            refine ⟨5003370914508489570674465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13342322438689305521798573 5003370914508489570674465)
            ·
              refine ⟨3752528185881367178005849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003370914508489570674465 3752528185881367178005849)
              ·
                refine ⟨2814396139411025383504387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752528185881367178005849 2814396139411025383504387)
                ·
                  refine ⟨4221594209116538075256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814396139411025383504387 4221594209116538075256581)
                  ·
                    refine ⟨791548914209350889110609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221594209116538075256581 791548914209350889110609)
                    ·
                      rfl

theorem cell22_2312304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_2312304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312304 prefixEnd_2312304 := by exact prefixLift 2312304
  have htrace : WordTrace (prefixWord ++ tailWord_2312304) baseStart_2312304 baseEnd_2312304 := by
    simpa [prefixWord, tailWord_2312304, baseEnd_2312304] using wordTrace_append hprefix tailTrace_2312304
  have hstable : (prefixWord ++ tailWord_2312304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312304).length < 2 ^ (prefixWord ++ tailWord_2312304).sum := by decide
  have hdescent : baseEnd_2312304 < baseStart_2312304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312351 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 2, 3]
def baseStart_2312351 : Nat := 118140960795 + 2312351 * 2 ^ 59
def prefixEnd_2312351 : Nat := 4983230072969 + 3 ^ 40 * 2312351 * 2
def baseEnd_2312351 : Nat := 791565003269858433185465

theorem tailTrace_2312351 : CollatzResearch.WordTrace tailWord_2312351 prefixEnd_2312351 791565003269858433185465 := by
  unfold tailWord_2312351
  simp only [CollatzResearch.WordTrace]
  refine ⟨84338369645754719954872907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56225579763836479969915271 84338369645754719954872907)
  ·
    refine ⟨126507554468632079932309361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84338369645754719954872907 126507554468632079932309361)
    ·
      refine ⟨94880665851474059949232021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126507554468632079932309361 94880665851474059949232021)
      ·
        refine ⟨4447531211787846560120251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94880665851474059949232021 4447531211787846560120251)
        ·
          refine ⟨6671296817681769840180377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447531211787846560120251 6671296817681769840180377)
          ·
            refine ⟨5003472613261327380135283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6671296817681769840180377 5003472613261327380135283)
            ·
              refine ⟨7505208919891991070202925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003472613261327380135283 7505208919891991070202925)
              ·
                refine ⟨2814453344959496651326097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7505208919891991070202925 2814453344959496651326097)
                ·
                  refine ⟨2110840008719622488494573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814453344959496651326097 2110840008719622488494573)
                  ·
                    refine ⟨791565003269858433185465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110840008719622488494573 791565003269858433185465)
                    ·
                      rfl

theorem cell22_2312351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_2312351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312351 prefixEnd_2312351 := by exact prefixLift 2312351
  have htrace : WordTrace (prefixWord ++ tailWord_2312351) baseStart_2312351 baseEnd_2312351 := by
    simpa [prefixWord, tailWord_2312351, baseEnd_2312351] using wordTrace_append hprefix tailTrace_2312351
  have hstable : (prefixWord ++ tailWord_2312351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312351).length < 2 ^ (prefixWord ++ tailWord_2312351).sum := by decide
  have hdescent : baseEnd_2312351 < baseStart_2312351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312372 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2312372 : Nat := 118140960795 + 2312372 * 2 ^ 59
def prefixEnd_2312372 : Nat := 4983230072969 + 3 ^ 40 * 2312372 * 2
def baseEnd_2312372 : Nat := 791572191999021378410401

theorem tailTrace_2312372 : CollatzResearch.WordTrace tailWord_2312372 prefixEnd_2312372 791572191999021378410401 := by
  unfold tailWord_2312372
  simp only [CollatzResearch.WordTrace]
  refine ⟨42169567789339320270693685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56226090385785760360924913 42169567789339320270693685)
  ·
    refine ⟨3953396980250561275377533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42169567789339320270693685 3953396980250561275377533)
    ·
      refine ⟨1482523867593960478266575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3953396980250561275377533 1482523867593960478266575)
      ·
        refine ⟨2223785801390940717399863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482523867593960478266575 2223785801390940717399863)
        ·
          refine ⟨3335678702086411076099795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223785801390940717399863 3335678702086411076099795)
          ·
            refine ⟨5003518053129616614149693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335678702086411076099795 5003518053129616614149693)
            ·
              refine ⟨1876319269923606230306135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5003518053129616614149693 1876319269923606230306135)
              ·
                refine ⟨2814478904885409345459203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876319269923606230306135 2814478904885409345459203)
                ·
                  refine ⟨4221718357328114018188805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814478904885409345459203 4221718357328114018188805)
                  ·
                    refine ⟨791572191999021378410401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221718357328114018188805 791572191999021378410401)
                    ·
                      rfl

theorem cell22_2312372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2312372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312372 prefixEnd_2312372 := by exact prefixLift 2312372
  have htrace : WordTrace (prefixWord ++ tailWord_2312372) baseStart_2312372 baseEnd_2312372 := by
    simpa [prefixWord, tailWord_2312372, baseEnd_2312372] using wordTrace_append hprefix tailTrace_2312372
  have hstable : (prefixWord ++ tailWord_2312372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312372).length < 2 ^ (prefixWord ++ tailWord_2312372).sum := by decide
  have hdescent : baseEnd_2312372 < baseStart_2312372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312469 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_2312469 : Nat := 118140960795 + 2312469 * 2 ^ 59
def prefixEnd_2312469 : Nat := 4983230072969 + 3 ^ 40 * 2312469 * 2
def baseEnd_2312469 : Nat := 791605397081345458735103

theorem tailTrace_2312469 : CollatzResearch.WordTrace tailWord_2312469 prefixEnd_2312469 791605397081345458735103 := by
  unfold tailWord_2312469
  simp only [CollatzResearch.WordTrace]
  refine ⟨84342673459327226107668461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56228448972884817405112307 84342673459327226107668461)
  ·
    refine ⟨31628502547247709790375673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84342673459327226107668461 31628502547247709790375673)
    ·
      refine ⟨23721376910435782342781755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31628502547247709790375673 23721376910435782342781755)
      ·
        refine ⟨35582065365653673514172633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23721376910435782342781755 35582065365653673514172633)
        ·
          refine ⟨26686549024240255135629475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35582065365653673514172633 26686549024240255135629475)
          ·
            refine ⟨40029823536360382703444213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26686549024240255135629475 40029823536360382703444213)
            ·
              refine ⟨3752795956533785878447895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40029823536360382703444213 3752795956533785878447895)
              ·
                refine ⟨5629193934800678817671843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752795956533785878447895 5629193934800678817671843)
                ·
                  refine ⟨8443790902201018226507765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629193934800678817671843 8443790902201018226507765)
                  ·
                    refine ⟨791605397081345458735103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8443790902201018226507765 791605397081345458735103)
                    ·
                      rfl

theorem cell22_2312469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_2312469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312469 prefixEnd_2312469 := by exact prefixLift 2312469
  have htrace : WordTrace (prefixWord ++ tailWord_2312469) baseStart_2312469 baseEnd_2312469 := by
    simpa [prefixWord, tailWord_2312469, baseEnd_2312469] using wordTrace_append hprefix tailTrace_2312469
  have hstable : (prefixWord ++ tailWord_2312469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312469).length < 2 ^ (prefixWord ++ tailWord_2312469).sum := by decide
  have hdescent : baseEnd_2312469 < baseStart_2312469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312484 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2312484 : Nat := 118140960795 + 2312484 * 2 ^ 59
def prefixEnd_2312484 : Nat := 4983230072969 + 3 ^ 40 * 2312484 * 2
def baseEnd_2312484 : Nat := 791610531887890419610057

theorem tailTrace_2312484 : CollatzResearch.WordTrace tailWord_2312484 prefixEnd_2312484 791610531887890419610057 := by
  unfold tailWord_2312484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42171610277136441834732253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56228813702848589112976337 42171610277136441834732253)
  ·
    refine ⟨15814353853926165688024595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42171610277136441834732253 15814353853926165688024595)
    ·
      refine ⟨23721530780889248532036893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15814353853926165688024595 23721530780889248532036893)
      ·
        refine ⟨8895574042833468199513835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23721530780889248532036893 8895574042833468199513835)
        ·
          refine ⟨13343361064250202299270753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895574042833468199513835 13343361064250202299270753)
          ·
            refine ⟨10007520798187651724453065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13343361064250202299270753 10007520798187651724453065)
            ·
              refine ⟨7505640598640738793339799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10007520798187651724453065 7505640598640738793339799)
              ·
                refine ⟨11258460897961108190009699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505640598640738793339799 11258460897961108190009699)
                ·
                  refine ⟨16887691346941662285014549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11258460897961108190009699 16887691346941662285014549)
                  ·
                    refine ⟨791610531887890419610057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16887691346941662285014549 791610531887890419610057)
                    ·
                      rfl

theorem cell22_2312484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2312484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312484 prefixEnd_2312484 := by exact prefixLift 2312484
  have htrace : WordTrace (prefixWord ++ tailWord_2312484) baseStart_2312484 baseEnd_2312484 := by
    simpa [prefixWord, tailWord_2312484, baseEnd_2312484] using wordTrace_append hprefix tailTrace_2312484
  have hstable : (prefixWord ++ tailWord_2312484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312484).length < 2 ^ (prefixWord ++ tailWord_2312484).sum := by decide
  have hdescent : baseEnd_2312484 < baseStart_2312484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312527 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 9]
def baseStart_2312527 : Nat := 118140960795 + 2312527 * 2 ^ 59
def prefixEnd_2312527 : Nat := 4983230072969 + 3 ^ 40 * 2312527 * 2
def baseEnd_2312527 : Nat := 263875083888884213594975

theorem tailTrace_2312527 : CollatzResearch.WordTrace tailWord_2312527 prefixEnd_2312527 263875083888884213594975 := by
  unfold tailWord_2312527
  simp only [CollatzResearch.WordTrace]
  refine ⟨84344788893117102013279835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56229859262078068008853223 84344788893117102013279835)
  ·
    refine ⟨126517183339675653019919753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84344788893117102013279835 126517183339675653019919753)
    ·
      refine ⟨94887887504756739764939815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126517183339675653019919753 94887887504756739764939815)
      ·
        refine ⟨142331831257135109647409723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94887887504756739764939815 142331831257135109647409723)
        ·
          refine ⟨213497746885702664471114585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142331831257135109647409723 213497746885702664471114585)
          ·
            refine ⟨160123310164276998353335939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213497746885702664471114585 160123310164276998353335939)
            ·
              refine ⟨240184965246415497530003909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160123310164276998353335939 240184965246415497530003909)
              ·
                refine ⟨45034680983702905786875733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240184965246415497530003909 45034680983702905786875733)
                ·
                  refine ⟨263875083888884213594975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45034680983702905786875733 263875083888884213594975)
                  ·
                    rfl

theorem cell22_2312527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_2312527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312527 prefixEnd_2312527 := by exact prefixLift 2312527
  have htrace : WordTrace (prefixWord ++ tailWord_2312527) baseStart_2312527 baseEnd_2312527 := by
    simpa [prefixWord, tailWord_2312527, baseEnd_2312527] using wordTrace_append hprefix tailTrace_2312527
  have hstable : (prefixWord ++ tailWord_2312527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312527).length < 2 ^ (prefixWord ++ tailWord_2312527).sum := by decide
  have hdescent : baseEnd_2312527 < baseStart_2312527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312548 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_2312548 : Nat := 118140960795 + 2312548 * 2 ^ 59
def prefixEnd_2312548 : Nat := 4983230072969 + 3 ^ 40 * 2312548 * 2
def baseEnd_2312548 : Nat := 791632440395815586009861

theorem tailTrace_2312548 : CollatzResearch.WordTrace tailWord_2312548 prefixEnd_2312548 791632440395815586009861 := by
  unfold tailWord_2312548
  simp only [CollatzResearch.WordTrace]
  refine ⟨42172777413020511299897149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56230369884027348399862865 42172777413020511299897149)
  ·
    refine ⟨15814791529882691737461431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42172777413020511299897149 15814791529882691737461431)
    ·
      refine ⟨23722187294824037606192147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15814791529882691737461431 23722187294824037606192147)
      ·
        refine ⟨35583280942236056409288221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23722187294824037606192147 35583280942236056409288221)
        ·
          refine ⟨13343730353338521153483083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35583280942236056409288221 13343730353338521153483083)
          ·
            refine ⟨20015595530007781730224625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13343730353338521153483083 20015595530007781730224625)
            ·
              refine ⟨15011696647505836297668469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20015595530007781730224625 15011696647505836297668469)
              ·
                refine ⟨1407346560703672152906419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15011696647505836297668469 1407346560703672152906419)
                ·
                  refine ⟨2111019841055508229359629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407346560703672152906419 2111019841055508229359629)
                  ·
                    refine ⟨791632440395815586009861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111019841055508229359629 791632440395815586009861)
                    ·
                      rfl

theorem cell22_2312548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_2312548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312548 prefixEnd_2312548 := by exact prefixLift 2312548
  have htrace : WordTrace (prefixWord ++ tailWord_2312548) baseStart_2312548 baseEnd_2312548 := by
    simpa [prefixWord, tailWord_2312548, baseEnd_2312548] using wordTrace_append hprefix tailTrace_2312548
  have hstable : (prefixWord ++ tailWord_2312548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312548).length < 2 ^ (prefixWord ++ tailWord_2312548).sum := by decide
  have hdescent : baseEnd_2312548 < baseStart_2312548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312565 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2312565 : Nat := 118140960795 + 2312565 * 2 ^ 59
def prefixEnd_2312565 : Nat := 4983230072969 + 3 ^ 40 * 2312565 * 2
def baseEnd_2312565 : Nat := 791638259843233208334809

theorem tailTrace_2312565 : CollatzResearch.WordTrace tailWord_2312565 prefixEnd_2312565 791638259843233208334809 := by
  unfold tailWord_2312565
  simp only [CollatzResearch.WordTrace]
  refine ⟨84346174866979434503163149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56230783244652956335442099 84346174866979434503163149)
  ·
    refine ⟨31629815575117287938686181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84346174866979434503163149 31629815575117287938686181)
    ·
      refine ⟨5930590420334491488503659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31629815575117287938686181 5930590420334491488503659)
      ·
        refine ⟨8895885630501737232755489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930590420334491488503659 8895885630501737232755489)
        ·
          refine ⟨6671914222876302924566617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8895885630501737232755489 6671914222876302924566617)
          ·
            refine ⟨5003935667157227193424963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6671914222876302924566617 5003935667157227193424963)
            ·
              refine ⟨7505903500735840790137445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003935667157227193424963 7505903500735840790137445)
              ·
                refine ⟨1407356906387970148150771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7505903500735840790137445 1407356906387970148150771)
                ·
                  refine ⟨2111035359581955222226157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407356906387970148150771 2111035359581955222226157)
                  ·
                    refine ⟨791638259843233208334809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111035359581955222226157 791638259843233208334809)
                    ·
                      rfl

theorem cell22_2312565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2312565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312565 prefixEnd_2312565 := by exact prefixLift 2312565
  have htrace : WordTrace (prefixWord ++ tailWord_2312565) baseStart_2312565 baseEnd_2312565 := by
    simpa [prefixWord, tailWord_2312565, baseEnd_2312565] using wordTrace_append hprefix tailTrace_2312565
  have hstable : (prefixWord ++ tailWord_2312565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312565).length < 2 ^ (prefixWord ++ tailWord_2312565).sum := by decide
  have hdescent : baseEnd_2312565 < baseStart_2312565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312608 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_2312608 : Nat := 118140960795 + 2312608 * 2 ^ 59
def prefixEnd_2312608 : Nat := 4983230072969 + 3 ^ 40 * 2312608 * 2
def baseEnd_2312608 : Nat := 791652979621995429509677

theorem tailTrace_2312608 : CollatzResearch.WordTrace tailWord_2312608 prefixEnd_2312608 791652979621995429509677 := by
  unfold tailWord_2312608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42173871602911826423489239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56231828803882435231318985 42173871602911826423489239)
  ·
    refine ⟨63260807404367739635233859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42173871602911826423489239 63260807404367739635233859)
    ·
      refine ⟨94891211106551609452850789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63260807404367739635233859 94891211106551609452850789)
      ·
        refine ⟨17792102082478426772409523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94891211106551609452850789 17792102082478426772409523)
        ·
          refine ⟨26688153123717640158614285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792102082478426772409523 26688153123717640158614285)
          ·
            refine ⟨10008057421394115059480357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26688153123717640158614285 10008057421394115059480357)
            ·
              refine ⟨1876510766511396573652567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10008057421394115059480357 1876510766511396573652567)
              ·
                refine ⟨2814766149767094860478851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876510766511396573652567 2814766149767094860478851)
                ·
                  refine ⟨4222149224650642290718277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814766149767094860478851 4222149224650642290718277)
                  ·
                    refine ⟨791652979621995429509677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222149224650642290718277 791652979621995429509677)
                    ·
                      rfl

theorem cell22_2312608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_2312608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312608 prefixEnd_2312608 := by exact prefixLift 2312608
  have htrace : WordTrace (prefixWord ++ tailWord_2312608) baseStart_2312608 baseEnd_2312608 := by
    simpa [prefixWord, tailWord_2312608, baseEnd_2312608] using wordTrace_append hprefix tailTrace_2312608
  have hstable : (prefixWord ++ tailWord_2312608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312608).length < 2 ^ (prefixWord ++ tailWord_2312608).sum := by decide
  have hdescent : baseEnd_2312608 < baseStart_2312608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312636 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_2312636 : Nat := 118140960795 + 2312636 * 2 ^ 59
def prefixEnd_2312636 : Nat := 4983230072969 + 3 ^ 40 * 2312636 * 2
def baseEnd_2312636 : Nat := 791662564594212689809591

theorem tailTrace_2312636 : CollatzResearch.WordTrace tailWord_2312636 prefixEnd_2312636 791662564594212689809591 := by
  unfold tailWord_2312636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42174382224861106814498881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56232509633148142419331841 42174382224861106814498881)
  ·
    refine ⟨31630786668645830110874161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42174382224861106814498881 31630786668645830110874161)
    ·
      refine ⟨23723090001484372583155621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31630786668645830110874161 23723090001484372583155621)
      ·
        refine ⟨4448079375278319859341679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23723090001484372583155621 4448079375278319859341679)
        ·
          refine ⟨6672119062917479789012519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448079375278319859341679 6672119062917479789012519)
          ·
            refine ⟨10008178594376219683518779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6672119062917479789012519 10008178594376219683518779)
            ·
              refine ⟨15012267891564329525278169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10008178594376219683518779 15012267891564329525278169)
              ·
                refine ⟨11259200918673247143958627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15012267891564329525278169 11259200918673247143958627)
                ·
                  refine ⟨16888801378009870715937941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11259200918673247143958627 16888801378009870715937941)
                  ·
                    refine ⟨791662564594212689809591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16888801378009870715937941 791662564594212689809591)
                    ·
                      rfl

theorem cell22_2312636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_2312636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312636 prefixEnd_2312636 := by exact prefixLift 2312636
  have htrace : WordTrace (prefixWord ++ tailWord_2312636) baseStart_2312636 baseEnd_2312636 := by
    simpa [prefixWord, tailWord_2312636, baseEnd_2312636] using wordTrace_append hprefix tailTrace_2312636
  have hstable : (prefixWord ++ tailWord_2312636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312636).length < 2 ^ (prefixWord ++ tailWord_2312636).sum := by decide
  have hdescent : baseEnd_2312636 < baseStart_2312636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312638 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_2312638 : Nat := 118140960795 + 2312638 * 2 ^ 59
def prefixEnd_2312638 : Nat := 4983230072969 + 3 ^ 40 * 2312638 * 2
def baseEnd_2312638 : Nat := 791663249235085351259585

theorem tailTrace_2312638 : CollatzResearch.WordTrace tailWord_2312638 prefixEnd_2312638 791663249235085351259585 := by
  unfold tailWord_2312638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543604674464370996321321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56232558263809978647047045 10543604674464370996321321)
  ·
    refine ⟨7907703505848278247240991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10543604674464370996321321 7907703505848278247240991)
    ·
      refine ⟨11861555258772417370861487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7907703505848278247240991 11861555258772417370861487)
      ·
        refine ⟨17792332888158626056292231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861555258772417370861487 17792332888158626056292231)
        ·
          refine ⟨26688499332237939084438347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792332888158626056292231 26688499332237939084438347)
          ·
            refine ⟨40032748998356908626657521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26688499332237939084438347 40032748998356908626657521)
            ·
              refine ⟨30024561748767681469993141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40032748998356908626657521 30024561748767681469993141)
              ·
                refine ⟨2814802663946970137811857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30024561748767681469993141 2814802663946970137811857)
                ·
                  refine ⟨2111101997960227603358893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814802663946970137811857 2111101997960227603358893)
                  ·
                    refine ⟨791663249235085351259585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111101997960227603358893 791663249235085351259585)
                    ·
                      rfl

theorem cell22_2312638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_2312638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312638 prefixEnd_2312638 := by exact prefixLift 2312638
  have htrace : WordTrace (prefixWord ++ tailWord_2312638) baseStart_2312638 baseEnd_2312638 := by
    simpa [prefixWord, tailWord_2312638, baseEnd_2312638] using wordTrace_append hprefix tailTrace_2312638
  have hstable : (prefixWord ++ tailWord_2312638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312638).length < 2 ^ (prefixWord ++ tailWord_2312638).sum := by decide
  have hdescent : baseEnd_2312638 < baseStart_2312638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312664 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2312664 : Nat := 118140960795 + 2312664 * 2 ^ 59
def prefixEnd_2312664 : Nat := 4983230072969 + 3 ^ 40 * 2312664 * 2
def baseEnd_2312664 : Nat := 791672149566429950109505

theorem tailTrace_2312664 : CollatzResearch.WordTrace tailWord_2312664 prefixEnd_2312664 791672149566429950109505 := by
  unfold tailWord_2312664
  simp only [CollatzResearch.WordTrace]
  refine ⟨42174892846810387205508523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56233190462413849607344697 42174892846810387205508523)
  ·
    refine ⟨63262339270215580808262785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42174892846810387205508523 63262339270215580808262785)
    ·
      refine ⟨47446754452661685606197089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63262339270215580808262785 47446754452661685606197089)
      ·
        refine ⟨35585065839496264204647817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47446754452661685606197089 35585065839496264204647817)
        ·
          refine ⟨26688799379622198153485863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35585065839496264204647817 26688799379622198153485863)
          ·
            refine ⟨40033199069433297230228795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26688799379622198153485863 40033199069433297230228795)
            ·
              refine ⟨60049798604149945845343193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40033199069433297230228795 60049798604149945845343193)
              ·
                refine ⟨45037348953112459384007395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60049798604149945845343193 45037348953112459384007395)
                ·
                  refine ⟨67556023429668689076011093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45037348953112459384007395 67556023429668689076011093)
                  ·
                    refine ⟨791672149566429950109505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67556023429668689076011093 791672149566429950109505)
                    ·
                      rfl

theorem cell22_2312664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2312664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312664 prefixEnd_2312664 := by exact prefixLift 2312664
  have htrace : WordTrace (prefixWord ++ tailWord_2312664) baseStart_2312664 baseEnd_2312664 := by
    simpa [prefixWord, tailWord_2312664, baseEnd_2312664] using wordTrace_append hprefix tailTrace_2312664
  have hstable : (prefixWord ++ tailWord_2312664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312664).length < 2 ^ (prefixWord ++ tailWord_2312664).sum := by decide
  have hdescent : baseEnd_2312664 < baseStart_2312664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312674 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2312674 : Nat := 118140960795 + 2312674 * 2 ^ 59
def prefixEnd_2312674 : Nat := 4983230072969 + 3 ^ 40 * 2312674 * 2
def baseEnd_2312674 : Nat := 263891857590264419119825

theorem tailTrace_2312674 : CollatzResearch.WordTrace tailWord_2312674 prefixEnd_2312674 263891857590264419119825 := by
  unfold tailWord_2312674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21087537605896136529720269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56233433615723030745920717 21087537605896136529720269)
  ·
    refine ⟨7907826602211051198645101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21087537605896136529720269 7907826602211051198645101)
    ·
      refine ⟨2965434975829144199491913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7907826602211051198645101 2965434975829144199491913)
      ·
        refine ⟨2224076231871858149618935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2965434975829144199491913 2224076231871858149618935)
        ·
          refine ⟨3336114347807787224428403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224076231871858149618935 3336114347807787224428403)
          ·
            refine ⟨5004171521711680836642605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336114347807787224428403 5004171521711680836642605)
            ·
              refine ⟨1876564320641880313740977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5004171521711680836642605 1876564320641880313740977)
              ·
                refine ⟨1407423240481410235305733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876564320641880313740977 1407423240481410235305733)
                ·
                  refine ⟨263891857590264419119825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407423240481410235305733 263891857590264419119825)
                  ·
                    rfl

theorem cell22_2312674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2312674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312674 prefixEnd_2312674 := by exact prefixLift 2312674
  have htrace : WordTrace (prefixWord ++ tailWord_2312674) baseStart_2312674 baseEnd_2312674 := by
    simpa [prefixWord, tailWord_2312674, baseEnd_2312674] using wordTrace_append hprefix tailTrace_2312674
  have hstable : (prefixWord ++ tailWord_2312674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312674).length < 2 ^ (prefixWord ++ tailWord_2312674).sum := by decide
  have hdescent : baseEnd_2312674 < baseStart_2312674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312696 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_2312696 : Nat := 118140960795 + 2312696 * 2 ^ 59
def prefixEnd_2312696 : Nat := 4983230072969 + 3 ^ 40 * 2312696 * 2
def baseEnd_2312696 : Nat := 263894367940130844436469

theorem tailTrace_2312696 : CollatzResearch.WordTrace tailWord_2312696 prefixEnd_2312696 263894367940130844436469 := by
  unfold tailWord_2312696
  simp only [CollatzResearch.WordTrace]
  refine ⟨42175476414752421938090971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56233968553003229250787961 42175476414752421938090971)
  ·
    refine ⟨63263214622128632907136457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42175476414752421938090971 63263214622128632907136457)
    ·
      refine ⟨47447410966596474680352343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63263214622128632907136457 47447410966596474680352343)
      ·
        refine ⟨71171116449894712020528515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47447410966596474680352343 71171116449894712020528515)
        ·
          refine ⟨106756674674842068030792773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71171116449894712020528515 106756674674842068030792773)
          ·
            refine ⟨20016876501532887755773645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106756674674842068030792773 20016876501532887755773645)
            ·
              refine ⟨7506328688074832908415117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20016876501532887755773645 7506328688074832908415117)
              ·
                refine ⟨2814873258028062340655669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7506328688074832908415117 2814873258028062340655669)
                ·
                  refine ⟨263894367940130844436469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814873258028062340655669 263894367940130844436469)
                  ·
                    rfl

theorem cell22_2312696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_2312696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312696 prefixEnd_2312696 := by exact prefixLift 2312696
  have htrace : WordTrace (prefixWord ++ tailWord_2312696) baseStart_2312696 baseEnd_2312696 := by
    simpa [prefixWord, tailWord_2312696, baseEnd_2312696] using wordTrace_append hprefix tailTrace_2312696
  have hstable : (prefixWord ++ tailWord_2312696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312696).length < 2 ^ (prefixWord ++ tailWord_2312696).sum := by decide
  have hdescent : baseEnd_2312696 < baseStart_2312696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312758 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2312758 : Nat := 118140960795 + 2312758 * 2 ^ 59
def prefixEnd_2312758 : Nat := 4983230072969 + 3 ^ 40 * 2312758 * 2
def baseEnd_2312758 : Nat := 263901442562481679419739

theorem tailTrace_2312758 : CollatzResearch.WordTrace tailWord_2312758 prefixEnd_2312758 263901442562481679419739 := by
  unfold tailWord_2312758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272075884705014279058683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56235476103520152309959285 5272075884705014279058683)
  ·
    refine ⟨7908113827057521418588025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272075884705014279058683 7908113827057521418588025)
    ·
      refine ⟨5931085370293141063941019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7908113827057521418588025 5931085370293141063941019)
      ·
        refine ⟨8896628055439711595911529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5931085370293141063941019 8896628055439711595911529)
        ·
          refine ⟨6672471041579783696933647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8896628055439711595911529 6672471041579783696933647)
          ·
            refine ⟨10008706562369675545400471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6672471041579783696933647 10008706562369675545400471)
            ·
              refine ⟨15013059843554513318100707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10008706562369675545400471 15013059843554513318100707)
              ·
                refine ⟨22519589765331769977151061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15013059843554513318100707 22519589765331769977151061)
                ·
                  refine ⟨263901442562481679419739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22519589765331769977151061 263901442562481679419739)
                  ·
                    rfl

theorem cell22_2312758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2312758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312758 prefixEnd_2312758 := by exact prefixLift 2312758
  have htrace : WordTrace (prefixWord ++ tailWord_2312758) baseStart_2312758 baseEnd_2312758 := by
    simpa [prefixWord, tailWord_2312758, baseEnd_2312758] using wordTrace_append hprefix tailTrace_2312758
  have hstable : (prefixWord ++ tailWord_2312758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312758).length < 2 ^ (prefixWord ++ tailWord_2312758).sum := by decide
  have hdescent : baseEnd_2312758 < baseStart_2312758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312775 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 4]
def baseStart_2312775 : Nat := 118140960795 + 2312775 * 2 ^ 59
def prefixEnd_2312775 : Nat := 4983230072969 + 3 ^ 40 * 2312775 * 2
def baseEnd_2312775 : Nat := 263903382378287553528055

theorem tailTrace_2312775 : CollatzResearch.WordTrace tailWord_2312775 prefixEnd_2312775 263903382378287553528055 := by
  unfold tailWord_2312775
  simp only [CollatzResearch.WordTrace]
  refine ⟨84353834196218640368307779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56235889464145760245538519 84353834196218640368307779)
  ·
    refine ⟨126530751294327960552461669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84353834196218640368307779 126530751294327960552461669)
    ·
      refine ⟨23724515867686492603586563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126530751294327960552461669 23724515867686492603586563)
      ·
        refine ⟨35586773801529738905379845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23724515867686492603586563 35586773801529738905379845)
        ·
          refine ⟨6672520087786826044758721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35586773801529738905379845 6672520087786826044758721)
          ·
            refine ⟨5004390065840119533569041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672520087786826044758721 5004390065840119533569041)
            ·
              refine ⟨3753292549380089650176781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5004390065840119533569041 3753292549380089650176781)
              ·
                refine ⟨1407484706017533618816293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3753292549380089650176781 1407484706017533618816293)
                ·
                  refine ⟨263903382378287553528055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1407484706017533618816293 263903382378287553528055)
                  ·
                    rfl

theorem cell22_2312775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 4].length) (baseStart_2312775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312775 prefixEnd_2312775 := by exact prefixLift 2312775
  have htrace : WordTrace (prefixWord ++ tailWord_2312775) baseStart_2312775 baseEnd_2312775 := by
    simpa [prefixWord, tailWord_2312775, baseEnd_2312775] using wordTrace_append hprefix tailTrace_2312775
  have hstable : (prefixWord ++ tailWord_2312775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312775).length < 2 ^ (prefixWord ++ tailWord_2312775).sum := by decide
  have hdescent : baseEnd_2312775 < baseStart_2312775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312786 : List Nat := [3, 2, 2, 1, 2, 1, 11]
def baseStart_2312786 : Nat := 118140960795 + 2312786 * 2 ^ 59
def prefixEnd_2312786 : Nat := 4983230072969 + 3 ^ 40 * 2312786 * 2
def baseEnd_2312786 : Nat := 29322737505913418465153

theorem tailTrace_2312786 : CollatzResearch.WordTrace tailWord_2312786 prefixEnd_2312786 29322737505913418465153 := by
  unfold tailWord_2312786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21088558849794697311739553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56236156932785859497972141 21088558849794697311739553)
  ·
    refine ⟨15816419137346022983804665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21088558849794697311739553 15816419137346022983804665)
    ·
      refine ⟨11862314353009517237853499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15816419137346022983804665 11862314353009517237853499)
      ·
        refine ⟨17793471529514275856780249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11862314353009517237853499 17793471529514275856780249)
        ·
          refine ⟨13345103647135706892585187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17793471529514275856780249 13345103647135706892585187)
          ·
            refine ⟨20017655470703560338877781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13345103647135706892585187 20017655470703560338877781)
            ·
              refine ⟨29322737505913418465153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20017655470703560338877781 29322737505913418465153)
              ·
                rfl

theorem cell22_2312786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 11].length) (baseStart_2312786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312786 prefixEnd_2312786 := by exact prefixLift 2312786
  have htrace : WordTrace (prefixWord ++ tailWord_2312786) baseStart_2312786 baseEnd_2312786 := by
    simpa [prefixWord, tailWord_2312786, baseEnd_2312786] using wordTrace_append hprefix tailTrace_2312786
  have hstable : (prefixWord ++ tailWord_2312786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312786).length < 2 ^ (prefixWord ++ tailWord_2312786).sum := by decide
  have hdescent : baseEnd_2312786 < baseStart_2312786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312852 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2312852 : Nat := 118140960795 + 2312852 * 2 ^ 59
def prefixEnd_2312852 : Nat := 4983230072969 + 3 ^ 40 * 2312852 * 2
def baseEnd_2312852 : Nat := 791736505808460126408929

theorem tailTrace_2312852 : CollatzResearch.WordTrace tailWord_2312852 prefixEnd_2312852 791736505808460126408929 := by
  unfold tailWord_2312852
  simp only [CollatzResearch.WordTrace]
  refine ⟨42178321308469841259430405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56237761744626455012573873 42178321308469841259430405)
  ·
    refine ⟨7908435245338095236143201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42178321308469841259430405 7908435245338095236143201)
    ·
      refine ⟨5931326434003571427107401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7908435245338095236143201 5931326434003571427107401)
      ·
        refine ⟨4448494825502678570330551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5931326434003571427107401 4448494825502678570330551)
        ·
          refine ⟨6672742238254017855495827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448494825502678570330551 6672742238254017855495827)
          ·
            refine ⟨10009113357381026783243741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6672742238254017855495827 10009113357381026783243741)
            ·
              refine ⟨3753417509017885043716403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10009113357381026783243741 3753417509017885043716403)
              ·
                refine ⟨5630126263526827565574605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753417509017885043716403 5630126263526827565574605)
                ·
                  refine ⟨2111297348822560337090477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5630126263526827565574605 2111297348822560337090477)
                  ·
                    refine ⟨791736505808460126408929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111297348822560337090477 791736505808460126408929)
                    ·
                      rfl

theorem cell22_2312852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2312852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312852 prefixEnd_2312852 := by exact prefixLift 2312852
  have htrace : WordTrace (prefixWord ++ tailWord_2312852) baseStart_2312852 baseEnd_2312852 := by
    simpa [prefixWord, tailWord_2312852, baseEnd_2312852] using wordTrace_append hprefix tailTrace_2312852
  have hstable : (prefixWord ++ tailWord_2312852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312852).length < 2 ^ (prefixWord ++ tailWord_2312852).sum := by decide
  have hdescent : baseEnd_2312852 < baseStart_2312852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312865 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 5]
def baseStart_2312865 : Nat := 118140960795 + 2312865 * 2 ^ 59
def prefixEnd_2312865 : Nat := 4983230072969 + 3 ^ 40 * 2312865 * 2
def baseEnd_2312865 : Nat := 263913651991377475277963

theorem tailTrace_2312865 : CollatzResearch.WordTrace tailWord_2312865 prefixEnd_2312865 263913651991377475277963 := by
  unfold tailWord_2312865
  simp only [CollatzResearch.WordTrace]
  refine ⟨84357116765892585739084049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56238077843928390492722699 84357116765892585739084049)
  ·
    refine ⟨63267837574419439304313037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84357116765892585739084049 63267837574419439304313037)
    ·
      refine ⟨23725439090407289739117389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63267837574419439304313037 23725439090407289739117389)
      ·
        refine ⟨8897039658902733652169021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23725439090407289739117389 8897039658902733652169021)
        ·
          refine ⟨3336389872088525119563383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8897039658902733652169021 3336389872088525119563383)
          ·
            refine ⟨5004584808132787679345075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336389872088525119563383 5004584808132787679345075)
            ·
              refine ⟨7506877212199181519017613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004584808132787679345075 7506877212199181519017613)
              ·
                refine ⟨2815078954574693069631605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7506877212199181519017613 2815078954574693069631605)
                ·
                  refine ⟨263913651991377475277963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2815078954574693069631605 263913651991377475277963)
                  ·
                    rfl

theorem cell22_2312865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_2312865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312865 prefixEnd_2312865 := by exact prefixLift 2312865
  have htrace : WordTrace (prefixWord ++ tailWord_2312865) baseStart_2312865 baseEnd_2312865 := by
    simpa [prefixWord, tailWord_2312865, baseEnd_2312865] using wordTrace_append hprefix tailTrace_2312865
  have hstable : (prefixWord ++ tailWord_2312865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312865).length < 2 ^ (prefixWord ++ tailWord_2312865).sum := by decide
  have hdescent : baseEnd_2312865 < baseStart_2312865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312989 : List Nat := [1, 4, 2, 4, 1, 2, 2, 6]
def baseStart_2312989 : Nat := 118140960795 + 2312989 * 2 ^ 59
def prefixEnd_2312989 : Nat := 4983230072969 + 3 ^ 40 * 2312989 * 2
def baseEnd_2312989 : Nat := 87975933745359715081501

theorem tailTrace_2312989 : CollatzResearch.WordTrace tailWord_2312989 prefixEnd_2312989 87975933745359715081501 := by
  unfold tailWord_2312989
  simp only [CollatzResearch.WordTrace]
  refine ⟨84361639417443354916598021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56241092944962236611065347 84361639417443354916598021)
  ·
    refine ⟨15817807390770629046862129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84361639417443354916598021 15817807390770629046862129)
    ·
      refine ⟨11863355543077971785146597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15817807390770629046862129 11863355543077971785146597)
      ·
        refine ⟨2224379164327119709714987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11863355543077971785146597 2224379164327119709714987)
        ·
          refine ⟨3336568746490679564572481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224379164327119709714987 3336568746490679564572481)
          ·
            refine ⟨2502426559868009673429361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336568746490679564572481 2502426559868009673429361)
            ·
              refine ⟨1876819919901007255072021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2502426559868009673429361 1876819919901007255072021)
              ·
                refine ⟨87975933745359715081501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1876819919901007255072021 87975933745359715081501)
                ·
                  rfl

theorem cell22_2312989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 6].length) (baseStart_2312989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2312989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2312989 prefixEnd_2312989 := by exact prefixLift 2312989
  have htrace : WordTrace (prefixWord ++ tailWord_2312989) baseStart_2312989 baseEnd_2312989 := by
    simpa [prefixWord, tailWord_2312989, baseEnd_2312989] using wordTrace_append hprefix tailTrace_2312989
  have hstable : (prefixWord ++ tailWord_2312989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312989).length < 2 ^ (prefixWord ++ tailWord_2312989).sum := by decide
  have hdescent : baseEnd_2312989 < baseStart_2312989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313021 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_2313021 : Nat := 118140960795 + 2313021 * 2 ^ 59
def prefixEnd_2313021 : Nat := 4983230072969 + 3 ^ 40 * 2313021 * 2
def baseEnd_2313021 : Nat := 791794357962200018933411

theorem tailTrace_2313021 : CollatzResearch.WordTrace tailWord_2313021 prefixEnd_2313021 791794357962200018933411 := by
  unfold tailWord_2313021
  simp only [CollatzResearch.WordTrace]
  refine ⟨84362806553327424381762917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56241871035551616254508611 84362806553327424381762917)
  ·
    refine ⟨15818026228748892071580547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84362806553327424381762917 15818026228748892071580547)
    ·
      refine ⟨23727039343123338107370821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15818026228748892071580547 23727039343123338107370821)
      ·
        refine ⟨4448819876835625895132029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23727039343123338107370821 4448819876835625895132029)
        ·
          refine ⟨1668307453813359710674511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4448819876835625895132029 1668307453813359710674511)
          ·
            refine ⟨2502461180720039566011767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668307453813359710674511 2502461180720039566011767)
            ·
              refine ⟨3753691771080059349017651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502461180720039566011767 3753691771080059349017651)
              ·
                refine ⟨5630537656620089023526477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753691771080059349017651 5630537656620089023526477)
                ·
                  refine ⟨2111451621232533383822429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5630537656620089023526477 2111451621232533383822429)
                  ·
                    refine ⟨791794357962200018933411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111451621232533383822429 791794357962200018933411)
                    ·
                      rfl

theorem cell22_2313021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_2313021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313021 prefixEnd_2313021 := by exact prefixLift 2313021
  have htrace : WordTrace (prefixWord ++ tailWord_2313021) baseStart_2313021 baseEnd_2313021 := by
    simpa [prefixWord, tailWord_2313021, baseEnd_2313021] using wordTrace_append hprefix tailTrace_2313021
  have hstable : (prefixWord ++ tailWord_2313021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313021).length < 2 ^ (prefixWord ++ tailWord_2313021).sum := by decide
  have hdescent : baseEnd_2313021 < baseStart_2313021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313043 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_2313043 : Nat := 118140960795 + 2313043 * 2 ^ 59
def prefixEnd_2313043 : Nat := 4983230072969 + 3 ^ 40 * 2313043 * 2
def baseEnd_2313043 : Nat := 791801889011799294883343

theorem tailTrace_2313043 : CollatzResearch.WordTrace tailWord_2313043 prefixEnd_2313043 791801889011799294883343 := by
  unfold tailWord_2313043
  simp only [CollatzResearch.WordTrace]
  refine ⟨84363608959247722139063783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56242405972831814759375855 84363608959247722139063783)
  ·
    refine ⟨126545413438871583208595675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84363608959247722139063783 126545413438871583208595675)
    ·
      refine ⟨189818120158307374812893513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126545413438871583208595675 189818120158307374812893513)
      ·
        refine ⟨142363590118730531109670135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189818120158307374812893513 142363590118730531109670135)
        ·
          refine ⟨213545385178095796664505203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142363590118730531109670135 213545385178095796664505203)
          ·
            refine ⟨320318077767143694996757805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213545385178095796664505203 320318077767143694996757805)
            ·
              refine ⟨120119279162678885623784177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320318077767143694996757805 120119279162678885623784177)
              ·
                refine ⟨90089459372009164217838133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120119279162678885623784177 90089459372009164217838133)
                ·
                  refine ⟨8445886816125859145422325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90089459372009164217838133 8445886816125859145422325)
                  ·
                    refine ⟨791801889011799294883343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8445886816125859145422325 791801889011799294883343)
                    ·
                      rfl

theorem cell22_2313043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_2313043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313043 prefixEnd_2313043 := by exact prefixLift 2313043
  have htrace : WordTrace (prefixWord ++ tailWord_2313043) baseStart_2313043 baseEnd_2313043 := by
    simpa [prefixWord, tailWord_2313043, baseEnd_2313043] using wordTrace_append hprefix tailTrace_2313043
  have hstable : (prefixWord ++ tailWord_2313043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313043).length < 2 ^ (prefixWord ++ tailWord_2313043).sum := by decide
  have hdescent : baseEnd_2313043 < baseStart_2313043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313047 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 1, 4]
def baseStart_2313047 : Nat := 118140960795 + 2313047 * 2 ^ 59
def prefixEnd_2313047 : Nat := 4983230072969 + 3 ^ 40 * 2313047 * 2
def baseEnd_2313047 : Nat := 791803258293544617783331

theorem tailTrace_2313047 : CollatzResearch.WordTrace tailWord_2313047 prefixEnd_2313047 791803258293544617783331 := by
  unfold tailWord_2313047
  simp only [CollatzResearch.WordTrace]
  refine ⟨84363754851233230822209395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56242503234155487214806263 84363754851233230822209395)
  ·
    refine ⟨126545632276849846233314093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84363754851233230822209395 126545632276849846233314093)
    ·
      refine ⟨47454612103818692337492785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126545632276849846233314093 47454612103818692337492785)
      ·
        refine ⟨35590959077864019253119589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47454612103818692337492785 35590959077864019253119589)
        ·
          refine ⟨6673304827099503609959923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35590959077864019253119589 6673304827099503609959923)
          ·
            refine ⟨10009957240649255414939885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6673304827099503609959923 10009957240649255414939885)
            ·
              refine ⟨3753733965243470780602457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10009957240649255414939885 3753733965243470780602457)
              ·
                refine ⟨2815300473932603085451843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753733965243470780602457 2815300473932603085451843)
                ·
                  refine ⟨4222950710898904628177765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815300473932603085451843 4222950710898904628177765)
                  ·
                    refine ⟨791803258293544617783331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222950710898904628177765 791803258293544617783331)
                    ·
                      rfl

theorem cell22_2313047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_2313047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313047 prefixEnd_2313047 := by exact prefixLift 2313047
  have htrace : WordTrace (prefixWord ++ tailWord_2313047) baseStart_2313047 baseEnd_2313047 := by
    simpa [prefixWord, tailWord_2313047, baseEnd_2313047] using wordTrace_append hprefix tailTrace_2313047
  have hstable : (prefixWord ++ tailWord_2313047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313047).length < 2 ^ (prefixWord ++ tailWord_2313047).sum := by decide
  have hdescent : baseEnd_2313047 < baseStart_2313047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313060 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2313060 : Nat := 118140960795 + 2313060 * 2 ^ 59
def prefixEnd_2313060 : Nat := 4983230072969 + 3 ^ 40 * 2313060 * 2
def baseEnd_2313060 : Nat := 791807708459216917208291

theorem tailTrace_2313060 : CollatzResearch.WordTrace tailWord_2313060 prefixEnd_2313060 791807708459216917208291 := by
  unfold tailWord_2313060
  simp only [CollatzResearch.WordTrace]
  refine ⟨42182114500093067021216317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56242819333457422694955089 42182114500093067021216317)
  ·
    refine ⟨15818292937534900132956119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42182114500093067021216317 15818292937534900132956119)
    ·
      refine ⟨23727439406302350199434179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15818292937534900132956119 23727439406302350199434179)
      ·
        refine ⟨35591159109453525299151269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23727439406302350199434179 35591159109453525299151269)
        ·
          refine ⟨6673342333022535993590863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35591159109453525299151269 6673342333022535993590863)
          ·
            refine ⟨10010013499533803990386295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6673342333022535993590863 10010013499533803990386295)
            ·
              refine ⟨15015020249300705985579443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10010013499533803990386295 15015020249300705985579443)
              ·
                refine ⟨22522530373951058978369165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15015020249300705985579443 22522530373951058978369165)
                ·
                  refine ⟨8445948890231647116888437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22522530373951058978369165 8445948890231647116888437)
                  ·
                    refine ⟨791807708459216917208291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8445948890231647116888437 791807708459216917208291)
                    ·
                      rfl

theorem cell22_2313060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2313060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313060 prefixEnd_2313060 := by exact prefixLift 2313060
  have htrace : WordTrace (prefixWord ++ tailWord_2313060) baseStart_2313060 baseEnd_2313060 := by
    simpa [prefixWord, tailWord_2313060, baseEnd_2313060] using wordTrace_append hprefix tailTrace_2313060
  have hstable : (prefixWord ++ tailWord_2313060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313060).length < 2 ^ (prefixWord ++ tailWord_2313060).sum := by decide
  have hdescent : baseEnd_2313060 < baseStart_2313060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313064 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2313064 : Nat := 118140960795 + 2313064 * 2 ^ 59
def prefixEnd_2313064 : Nat := 4983230072969 + 3 ^ 40 * 2313064 * 2
def baseEnd_2313064 : Nat := 791809077740962240108279

theorem tailTrace_2313064 : CollatzResearch.WordTrace tailWord_2313064 prefixEnd_2313064 791809077740962240108279 := by
  unfold tailWord_2313064
  simp only [CollatzResearch.WordTrace]
  refine ⟨42182187446085821362789123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56242916594781095150385497 42182187446085821362789123)
  ·
    refine ⟨63273281169128732044183685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42182187446085821362789123 63273281169128732044183685)
    ·
      refine ⟨11863740219211637258284441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63273281169128732044183685 11863740219211637258284441)
      ·
        refine ⟨8897805164408727943713331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11863740219211637258284441 8897805164408727943713331)
        ·
          refine ⟨13346707746613091915569997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8897805164408727943713331 13346707746613091915569997)
          ·
            refine ⟨5005015404979909468338749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13346707746613091915569997 5005015404979909468338749)
            ·
              refine ⟨1876880776867466050627031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5005015404979909468338749 1876880776867466050627031)
              ·
                refine ⟨2815321165301199075940547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876880776867466050627031 2815321165301199075940547)
                ·
                  refine ⟨4222981747951798613910821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815321165301199075940547 4222981747951798613910821)
                  ·
                    refine ⟨791809077740962240108279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222981747951798613910821 791809077740962240108279)
                    ·
                      rfl

theorem cell22_2313064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2313064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313064 prefixEnd_2313064 := by exact prefixLift 2313064
  have htrace : WordTrace (prefixWord ++ tailWord_2313064) baseStart_2313064 baseEnd_2313064 := by
    simpa [prefixWord, tailWord_2313064, baseEnd_2313064] using wordTrace_append hprefix tailTrace_2313064
  have hstable : (prefixWord ++ tailWord_2313064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313064).length < 2 ^ (prefixWord ++ tailWord_2313064).sum := by decide
  have hdescent : baseEnd_2313064 < baseStart_2313064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313073 : List Nat := [1, 2, 2, 2, 1, 14]
def baseStart_2313073 : Nat := 118140960795 + 2313073 * 2 ^ 59
def prefixEnd_2313073 : Nat := 4983230072969 + 3 ^ 40 * 2313073 * 2
def baseEnd_2313073 : Nat := 9775458748455422427571

theorem tailTrace_2313073 : CollatzResearch.WordTrace tailWord_2313073 prefixEnd_2313073 9775458748455422427571 := by
  unfold tailWord_2313073
  simp only [CollatzResearch.WordTrace]
  refine ⟨84364703149139037262655873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56243135432759358175103915 84364703149139037262655873)
  ·
    refine ⟨63273527361854277946991905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84364703149139037262655873 63273527361854277946991905)
    ·
      refine ⟨47455145521390708460243929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63273527361854277946991905 47455145521390708460243929)
      ·
        refine ⟨35591359141043031345182947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47455145521390708460243929 35591359141043031345182947)
        ·
          refine ⟨53387038711564547017774421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35591359141043031345182947 53387038711564547017774421)
          ·
            refine ⟨9775458748455422427571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 53387038711564547017774421 9775458748455422427571)
            ·
              rfl

theorem cell22_2313073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 14].length) (baseStart_2313073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313073 prefixEnd_2313073 := by exact prefixLift 2313073
  have htrace : WordTrace (prefixWord ++ tailWord_2313073) baseStart_2313073 baseEnd_2313073 := by
    simpa [prefixWord, tailWord_2313073, baseEnd_2313073] using wordTrace_append hprefix tailTrace_2313073
  have hstable : (prefixWord ++ tailWord_2313073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313073).length < 2 ^ (prefixWord ++ tailWord_2313073).sum := by decide
  have hdescent : baseEnd_2313073 < baseStart_2313073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313075 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_2313075 : Nat := 118140960795 + 2313075 * 2 ^ 59
def prefixEnd_2313075 : Nat := 4983230072969 + 3 ^ 40 * 2313075 * 2
def baseEnd_2313075 : Nat := 791812843265761878083245

theorem tailTrace_2313075 : CollatzResearch.WordTrace tailWord_2313075 prefixEnd_2313075 791812843265761878083245 := by
  unfold tailWord_2313075
  simp only [CollatzResearch.WordTrace]
  refine ⟨84364776095131791604228679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56243184063421194402819119 84364776095131791604228679)
  ·
    refine ⟨126547164142697687406343019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84364776095131791604228679 126547164142697687406343019)
    ·
      refine ⟨189820746214046531109514529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126547164142697687406343019 189820746214046531109514529)
      ·
        refine ⟨142365559660534898332135897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189820746214046531109514529 142365559660534898332135897)
        ·
          refine ⟨106774169745401173749101923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142365559660534898332135897 106774169745401173749101923)
          ·
            refine ⟨160161254618101760623652885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106774169745401173749101923 160161254618101760623652885)
            ·
              refine ⟨7507558810223520029233729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160161254618101760623652885 7507558810223520029233729)
              ·
                refine ⟨5630669107667640021925297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7507558810223520029233729 5630669107667640021925297)
                ·
                  refine ⟨4223001830750730016443973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5630669107667640021925297 4223001830750730016443973)
                  ·
                    refine ⟨791812843265761878083245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223001830750730016443973 791812843265761878083245)
                    ·
                      rfl

theorem cell22_2313075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_2313075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313075 prefixEnd_2313075 := by exact prefixLift 2313075
  have htrace : WordTrace (prefixWord ++ tailWord_2313075) baseStart_2313075 baseEnd_2313075 := by
    simpa [prefixWord, tailWord_2313075, baseEnd_2313075] using wordTrace_append hprefix tailTrace_2313075
  have hstable : (prefixWord ++ tailWord_2313075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313075).length < 2 ^ (prefixWord ++ tailWord_2313075).sum := by decide
  have hdescent : baseEnd_2313075 < baseStart_2313075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313135 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 5]
def baseStart_2313135 : Nat := 118140960795 + 2313135 * 2 ^ 59
def prefixEnd_2313135 : Nat := 4983230072969 + 3 ^ 40 * 2313135 * 2
def baseEnd_2313135 : Nat := 263944460830647240527687

theorem tailTrace_2313135 : CollatzResearch.WordTrace tailWord_2313135 prefixEnd_2313135 263944460830647240527687 := by
  unfold tailWord_2313135
  simp only [CollatzResearch.WordTrace]
  refine ⟨84366964474914421851412859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56244642983276281234275239 84366964474914421851412859)
  ·
    refine ⟨126550446712371632777119289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84366964474914421851412859 126550446712371632777119289)
    ·
      refine ⟨94912835034278724582839467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126550446712371632777119289 94912835034278724582839467)
      ·
        refine ⟨142369252551418086874259201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94912835034278724582839467 142369252551418086874259201)
        ·
          refine ⟨106776939413563565155694401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142369252551418086874259201 106776939413563565155694401)
          ·
            refine ⟨80082704560172673866770801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106776939413563565155694401 80082704560172673866770801)
            ·
              refine ⟨60062028420129505400078101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80082704560172673866770801 60062028420129505400078101)
              ·
                refine ⟨2815407582193570565628661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60062028420129505400078101 2815407582193570565628661)
                ·
                  refine ⟨263944460830647240527687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2815407582193570565628661 263944460830647240527687)
                  ·
                    rfl

theorem cell22_2313135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 5].length) (baseStart_2313135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313135 prefixEnd_2313135 := by exact prefixLift 2313135
  have htrace : WordTrace (prefixWord ++ tailWord_2313135) baseStart_2313135 baseEnd_2313135 := by
    simpa [prefixWord, tailWord_2313135, baseEnd_2313135] using wordTrace_append hprefix tailTrace_2313135
  have hstable : (prefixWord ++ tailWord_2313135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313135).length < 2 ^ (prefixWord ++ tailWord_2313135).sum := by decide
  have hdescent : baseEnd_2313135 < baseStart_2313135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313158 : List Nat := [6, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2313158 : Nat := 118140960795 + 2313158 * 2 ^ 59
def prefixEnd_2313158 : Nat := 4983230072969 + 3 ^ 40 * 2313158 * 2
def baseEnd_2313158 : Nat := 87982361762441925361999

theorem tailTrace_2313158 : CollatzResearch.WordTrace tailWord_2313158 prefixEnd_2313158 87982361762441925361999 := by
  unfold tailWord_2313158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636493854807221774359379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56245202235887397853000085 2636493854807221774359379)
  ·
    refine ⟨3954740782210832661539069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2636493854807221774359379 3954740782210832661539069)
    ·
      refine ⟨1483027793329062248077151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3954740782210832661539069 1483027793329062248077151)
      ·
        refine ⟨2224541689993593372115727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483027793329062248077151 2224541689993593372115727)
        ·
          refine ⟨3336812534990390058173591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224541689993593372115727 3336812534990390058173591)
          ·
            refine ⟨5005218802485585087260387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336812534990390058173591 5005218802485585087260387)
            ·
              refine ⟨7507828203728377630890581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005218802485585087260387 7507828203728377630890581)
              ·
                refine ⟨87982361762441925361999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7507828203728377630890581 87982361762441925361999)
                ·
                  rfl

theorem cell22_2313158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2313158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313158 prefixEnd_2313158 := by exact prefixLift 2313158
  have htrace : WordTrace (prefixWord ++ tailWord_2313158) baseStart_2313158 baseEnd_2313158 := by
    simpa [prefixWord, tailWord_2313158, baseEnd_2313158] using wordTrace_append hprefix tailTrace_2313158
  have hstable : (prefixWord ++ tailWord_2313158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313158).length < 2 ^ (prefixWord ++ tailWord_2313158).sum := by decide
  have hdescent : baseEnd_2313158 < baseStart_2313158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313173 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_2313173 : Nat := 118140960795 + 2313173 * 2 ^ 59
def prefixEnd_2313173 : Nat := 4983230072969 + 3 ^ 40 * 2313173 * 2
def baseEnd_2313173 : Nat := 791846390668522289132945

theorem tailTrace_2313173 : CollatzResearch.WordTrace tailWord_2313173 prefixEnd_2313173 791846390668522289132945 := by
  unfold tailWord_2313173
  simp only [CollatzResearch.WordTrace]
  refine ⟨84368350448776754341296173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56245566965851169560864115 84368350448776754341296173)
  ·
    refine ⟨31638131418291282877986065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84368350448776754341296173 31638131418291282877986065)
    ·
      refine ⟨23728598563718462158489549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31638131418291282877986065 23728598563718462158489549)
      ·
        refine ⟨8898224461394423309433581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23728598563718462158489549 8898224461394423309433581)
        ·
          refine ⟨3336834173022908741037593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8898224461394423309433581 3336834173022908741037593)
          ·
            refine ⟨2502625629767181555778195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336834173022908741037593 2502625629767181555778195)
            ·
              refine ⟨3753938444650772333667293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502625629767181555778195 3753938444650772333667293)
              ·
                refine ⟨1407726916744039625125235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3753938444650772333667293 1407726916744039625125235)
                ·
                  refine ⟨2111590375116059437687853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407726916744039625125235 2111590375116059437687853)
                  ·
                    refine ⟨791846390668522289132945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111590375116059437687853 791846390668522289132945)
                    ·
                      rfl

theorem cell22_2313173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_2313173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313173 prefixEnd_2313173 := by exact prefixLift 2313173
  have htrace : WordTrace (prefixWord ++ tailWord_2313173) baseStart_2313173 baseEnd_2313173 := by
    simpa [prefixWord, tailWord_2313173, baseEnd_2313173] using wordTrace_append hprefix tailTrace_2313173
  have hstable : (prefixWord ++ tailWord_2313173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313173).length < 2 ^ (prefixWord ++ tailWord_2313173).sum := by decide
  have hdescent : baseEnd_2313173 < baseStart_2313173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313210 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_2313210 : Nat := 118140960795 + 2313210 * 2 ^ 59
def prefixEnd_2313210 : Nat := 4983230072969 + 3 ^ 40 * 2313210 * 2
def baseEnd_2313210 : Nat := 791859056524666525957831

theorem tailTrace_2313210 : CollatzResearch.WordTrace tailWord_2313210 prefixEnd_2313210 791859056524666525957831 := by
  unfold tailWord_2313210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21092424987410677415098271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56246466633095139773595389 21092424987410677415098271)
  ·
    refine ⟨31638637481116016122647407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21092424987410677415098271 31638637481116016122647407)
    ·
      refine ⟨47457956221674024183971111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31638637481116016122647407 47457956221674024183971111)
      ·
        refine ⟨71186934332511036275956667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47457956221674024183971111 71186934332511036275956667)
        ·
          refine ⟨106780401498766554413935001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71186934332511036275956667 106780401498766554413935001)
          ·
            refine ⟨80085301124074915810451251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106780401498766554413935001 80085301124074915810451251)
            ·
              refine ⟨120127951686112373715676877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80085301124074915810451251 120127951686112373715676877)
              ·
                refine ⟨45047981882292140143378829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120127951686112373715676877 45047981882292140143378829)
                ·
                  refine ⟨16892993205859552553767061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45047981882292140143378829 16892993205859552553767061)
                  ·
                    refine ⟨791859056524666525957831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16892993205859552553767061 791859056524666525957831)
                    ·
                      rfl

theorem cell22_2313210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_2313210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313210 prefixEnd_2313210 := by exact prefixLift 2313210
  have htrace : WordTrace (prefixWord ++ tailWord_2313210) baseStart_2313210 baseEnd_2313210 := by
    simpa [prefixWord, tailWord_2313210, baseEnd_2313210] using wordTrace_append hprefix tailTrace_2313210
  have hstable : (prefixWord ++ tailWord_2313210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313210).length < 2 ^ (prefixWord ++ tailWord_2313210).sum := by decide
  have hdescent : baseEnd_2313210 < baseStart_2313210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313227 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_2313227 : Nat := 118140960795 + 2313227 * 2 ^ 59
def prefixEnd_2313227 : Nat := 4983230072969 + 3 ^ 40 * 2313227 * 2
def baseEnd_2313227 : Nat := 791864875972084148282779

theorem tailTrace_2313227 : CollatzResearch.WordTrace tailWord_2313227 prefixEnd_2313227 791864875972084148282779 := by
  unfold tailWord_2313227
  simp only [CollatzResearch.WordTrace]
  refine ⟨84370319990581121563761935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56246879993720747709174623 84370319990581121563761935)
  ·
    refine ⟨126555479985871682345642903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84370319990581121563761935 126555479985871682345642903)
    ·
      refine ⟨189833219978807523518464355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126555479985871682345642903 189833219978807523518464355)
      ·
        refine ⟨284749829968211285277696533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189833219978807523518464355 284749829968211285277696533)
        ·
          refine ⟨13347648279759903997392025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 284749829968211285277696533 13347648279759903997392025)
          ·
            refine ⟨10010736209819927998044019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13347648279759903997392025 10010736209819927998044019)
            ·
              refine ⟨15016104314729891997066029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10010736209819927998044019 15016104314729891997066029)
              ·
                refine ⟨5631039118023709498899761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15016104314729891997066029 5631039118023709498899761)
                ·
                  refine ⟨4223279338517782124174821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5631039118023709498899761 4223279338517782124174821)
                  ·
                    refine ⟨791864875972084148282779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223279338517782124174821 791864875972084148282779)
                    ·
                      rfl

theorem cell22_2313227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_2313227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313227 prefixEnd_2313227 := by exact prefixLift 2313227
  have htrace : WordTrace (prefixWord ++ tailWord_2313227) baseStart_2313227 baseEnd_2313227 := by
    simpa [prefixWord, tailWord_2313227, baseEnd_2313227] using wordTrace_append hprefix tailTrace_2313227
  have hstable : (prefixWord ++ tailWord_2313227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313227).length < 2 ^ (prefixWord ++ tailWord_2313227).sum := by decide
  have hdescent : baseEnd_2313227 < baseStart_2313227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313347 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_2313347 : Nat := 118140960795 + 2313347 * 2 ^ 59
def prefixEnd_2313347 : Nat := 4983230072969 + 3 ^ 40 * 2313347 * 2
def baseEnd_2313347 : Nat := 791905954424443835282411

theorem tailTrace_2313347 : CollatzResearch.WordTrace tailWord_2313347 prefixEnd_2313347 791905954424443835282411 := by
  unfold tailWord_2313347
  simp only [CollatzResearch.WordTrace]
  refine ⟨84374696750146382058130295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56249797833430921372086863 84374696750146382058130295)
  ·
    refine ⟨126562045125219573087195443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84374696750146382058130295 126562045125219573087195443)
    ·
      refine ⟨189843067687829359630793165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126562045125219573087195443 189843067687829359630793165)
      ·
        refine ⟨71191150382936009861547437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189843067687829359630793165 71191150382936009861547437)
        ·
          refine ⟨26696681393601003698080289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71191150382936009861547437 26696681393601003698080289)
          ·
            refine ⟨20022511045200752773560217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26696681393601003698080289 20022511045200752773560217)
            ·
              refine ⟨15016883283900564580170163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20022511045200752773560217 15016883283900564580170163)
              ·
                refine ⟨22525324925850846870255245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15016883283900564580170163 22525324925850846870255245)
                ·
                  refine ⟨8446996847194067576345717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22525324925850846870255245 8446996847194067576345717)
                  ·
                    refine ⟨791905954424443835282411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8446996847194067576345717 791905954424443835282411)
                    ·
                      rfl

theorem cell22_2313347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_2313347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313347 prefixEnd_2313347 := by exact prefixLift 2313347
  have htrace : WordTrace (prefixWord ++ tailWord_2313347) baseStart_2313347 baseEnd_2313347 := by
    simpa [prefixWord, tailWord_2313347, baseEnd_2313347] using wordTrace_append hprefix tailTrace_2313347
  have hstable : (prefixWord ++ tailWord_2313347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313347).length < 2 ^ (prefixWord ++ tailWord_2313347).sum := by decide
  have hdescent : baseEnd_2313347 < baseStart_2313347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313381 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_2313381 : Nat := 118140960795 + 2313381 * 2 ^ 59
def prefixEnd_2313381 : Nat := 4983230072969 + 3 ^ 40 * 2313381 * 2
def baseEnd_2313381 : Nat := 791917593319279079932307

theorem tailTrace_2313381 : CollatzResearch.WordTrace tailWord_2313381 prefixEnd_2313381 791917593319279079932307 := by
  unfold tailWord_2313381
  simp only [CollatzResearch.WordTrace]
  refine ⟨84375936832023205864867997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56250624554682137243245331 84375936832023205864867997)
  ·
    refine ⟨31640976312008702199325499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84375936832023205864867997 31640976312008702199325499)
    ·
      refine ⟨47461464468013053298988249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31640976312008702199325499 47461464468013053298988249)
      ·
        refine ⟨35596098351009789974241187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47461464468013053298988249 35596098351009789974241187)
        ·
          refine ⟨53394147526514684961361781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35596098351009789974241187 53394147526514684961361781)
          ·
            refine ⟨5005701330610751715127667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53394147526514684961361781 5005701330610751715127667)
            ·
              refine ⟨7508551995916127572691501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005701330610751715127667 7508551995916127572691501)
              ·
                refine ⟨2815706998468547839759313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7508551995916127572691501 2815706998468547839759313)
                ·
                  refine ⟨2111780248851410879819485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2815706998468547839759313 2111780248851410879819485)
                  ·
                    refine ⟨791917593319279079932307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111780248851410879819485 791917593319279079932307)
                    ·
                      rfl

theorem cell22_2313381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_2313381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313381 prefixEnd_2313381 := by exact prefixLift 2313381
  have htrace : WordTrace (prefixWord ++ tailWord_2313381) baseStart_2313381 baseEnd_2313381 := by
    simpa [prefixWord, tailWord_2313381, baseEnd_2313381] using wordTrace_append hprefix tailTrace_2313381
  have hstable : (prefixWord ++ tailWord_2313381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313381).length < 2 ^ (prefixWord ++ tailWord_2313381).sum := by decide
  have hdescent : baseEnd_2313381 < baseStart_2313381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313426 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_2313426 : Nat := 118140960795 + 2313426 * 2 ^ 59
def prefixEnd_2313426 : Nat := 4983230072969 + 3 ^ 40 * 2313426 * 2
def baseEnd_2313426 : Nat := 791932997738913962557169

theorem tailTrace_2313426 : CollatzResearch.WordTrace tailWord_2313426 prefixEnd_2313426 791932997738913962557169 := by
  unfold tailWord_2313426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094394529215044637564033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56251718744573452366837421 21094394529215044637564033)
  ·
    refine ⟨15820795896911283478173025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21094394529215044637564033 15820795896911283478173025)
    ·
      refine ⟨11865596922683462608629769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15820795896911283478173025 11865596922683462608629769)
      ·
        refine ⟨8899197692012596956472327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11865596922683462608629769 8899197692012596956472327)
        ·
          refine ⟨13348796538018895434708491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8899197692012596956472327 13348796538018895434708491)
          ·
            refine ⟨20023194807028343152062737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13348796538018895434708491 20023194807028343152062737)
            ·
              refine ⟨15017396105271257364047053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20023194807028343152062737 15017396105271257364047053)
              ·
                refine ⟨5631523539476721511517645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15017396105271257364047053 5631523539476721511517645)
                ·
                  refine ⟨2111821327303770566819117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5631523539476721511517645 2111821327303770566819117)
                  ·
                    refine ⟨791932997738913962557169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111821327303770566819117 791932997738913962557169)
                    ·
                      rfl

theorem cell22_2313426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_2313426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313426 prefixEnd_2313426 := by exact prefixLift 2313426
  have htrace : WordTrace (prefixWord ++ tailWord_2313426) baseStart_2313426 baseEnd_2313426 := by
    simpa [prefixWord, tailWord_2313426, baseEnd_2313426] using wordTrace_append hprefix tailTrace_2313426
  have hstable : (prefixWord ++ tailWord_2313426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313426).length < 2 ^ (prefixWord ++ tailWord_2313426).sum := by decide
  have hdescent : baseEnd_2313426 < baseStart_2313426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313428 : List Nat := [2, 4, 1, 4, 1, 2, 1, 7]
def baseStart_2313428 : Nat := 118140960795 + 2313428 * 2 ^ 59
def prefixEnd_2313428 : Nat := 4983230072969 + 3 ^ 40 * 2313428 * 2
def baseEnd_2313428 : Nat := 87992631375531847111907

theorem tailTrace_2313428 : CollatzResearch.WordTrace tailWord_2313428 prefixEnd_2313428 87992631375531847111907 := by
  unfold tailWord_2313428
  simp only [CollatzResearch.WordTrace]
  refine ⟨42188825531426466445914469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56251767375235288594552625 42188825531426466445914469)
  ·
    refine ⟨7910404787142462458608963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42188825531426466445914469 7910404787142462458608963)
    ·
      refine ⟨11865607180713693687913445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7910404787142462458608963 11865607180713693687913445)
      ·
        refine ⟨2224801346383817566483771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11865607180713693687913445 2224801346383817566483771)
        ·
          refine ⟨3337202019575726349725657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224801346383817566483771 3337202019575726349725657)
          ·
            refine ⟨2502901514681794762294243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337202019575726349725657 2502901514681794762294243)
            ·
              refine ⟨3754352272022692143441365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502901514681794762294243 3754352272022692143441365)
              ·
                refine ⟨87992631375531847111907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3754352272022692143441365 87992631375531847111907)
                ·
                  rfl

theorem cell22_2313428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_2313428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313428 prefixEnd_2313428 := by exact prefixLift 2313428
  have htrace : WordTrace (prefixWord ++ tailWord_2313428) baseStart_2313428 baseEnd_2313428 := by
    simpa [prefixWord, tailWord_2313428, baseEnd_2313428] using wordTrace_append hprefix tailTrace_2313428
  have hstable : (prefixWord ++ tailWord_2313428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313428).length < 2 ^ (prefixWord ++ tailWord_2313428).sum := by decide
  have hdescent : baseEnd_2313428 < baseStart_2313428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313439 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 5]
def baseStart_2313439 : Nat := 118140960795 + 2313439 * 2 ^ 59
def prefixEnd_2313439 : Nat := 4983230072969 + 3 ^ 40 * 2313439 * 2
def baseEnd_2313439 : Nat := 263979149301528753994043

theorem tailTrace_2313439 : CollatzResearch.WordTrace tailWord_2313439 prefixEnd_2313439 263979149301528753994043 := by
  unfold tailWord_2313439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84378052265813081770479371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56252034843875387846986247 84378052265813081770479371)
  ·
    refine ⟨126567078398719622655719057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84378052265813081770479371 126567078398719622655719057)
    ·
      refine ⟨94925308799039716991789293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126567078398719622655719057 94925308799039716991789293)
      ·
        refine ⟨35596990799639893871920985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94925308799039716991789293 35596990799639893871920985)
        ·
          refine ⟨26697743099729920403940739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35596990799639893871920985 26697743099729920403940739)
          ·
            refine ⟨40046614649594880605911109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26697743099729920403940739 40046614649594880605911109)
            ·
              refine ⟨7508740246799040113608333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40046614649594880605911109 7508740246799040113608333)
              ·
                refine ⟨2815777592549640042603125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7508740246799040113608333 2815777592549640042603125)
                ·
                  refine ⟨263979149301528753994043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2815777592549640042603125 263979149301528753994043)
                  ·
                    rfl

theorem cell22_2313439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 5].length) (baseStart_2313439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313439 prefixEnd_2313439 := by exact prefixLift 2313439
  have htrace : WordTrace (prefixWord ++ tailWord_2313439) baseStart_2313439 baseEnd_2313439 := by
    simpa [prefixWord, tailWord_2313439, baseEnd_2313439] using wordTrace_append hprefix tailTrace_2313439
  have hstable : (prefixWord ++ tailWord_2313439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313439).length < 2 ^ (prefixWord ++ tailWord_2313439).sum := by decide
  have hdescent : baseEnd_2313439 < baseStart_2313439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313484 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_2313484 : Nat := 118140960795 + 2313484 * 2 ^ 59
def prefixEnd_2313484 : Nat := 4983230072969 + 3 ^ 40 * 2313484 * 2
def baseEnd_2313484 : Nat := 263984284108073714868997

theorem tailTrace_2313484 : CollatzResearch.WordTrace tailWord_2313484 prefixEnd_2313484 263984284108073714868997 := by
  unfold tailWord_2313484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42189846775325027227933753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56253129033766702970578337 42189846775325027227933753)
  ·
    refine ⟨31642385081493770420950315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42189846775325027227933753 31642385081493770420950315)
    ·
      refine ⟨47463577622240655631425473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31642385081493770420950315 47463577622240655631425473)
      ·
        refine ⟨35597683216680491723569105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47463577622240655631425473 35597683216680491723569105)
        ·
          refine ⟨26698262412510368792676829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35597683216680491723569105 26698262412510368792676829)
          ·
            refine ⟨10011848404691388297253811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26698262412510368792676829 10011848404691388297253811)
            ·
              refine ⟨15017772607037082445880717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10011848404691388297253811 15017772607037082445880717)
              ·
                refine ⟨5631664727638905917205269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15017772607037082445880717 5631664727638905917205269)
                ·
                  refine ⟨263984284108073714868997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5631664727638905917205269 263984284108073714868997)
                  ·
                    rfl

theorem cell22_2313484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_2313484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313484 prefixEnd_2313484 := by exact prefixLift 2313484
  have htrace : WordTrace (prefixWord ++ tailWord_2313484) baseStart_2313484 baseEnd_2313484 := by
    simpa [prefixWord, tailWord_2313484, baseEnd_2313484] using wordTrace_append hprefix tailTrace_2313484
  have hstable : (prefixWord ++ tailWord_2313484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313484).length < 2 ^ (prefixWord ++ tailWord_2313484).sum := by decide
  have hdescent : baseEnd_2313484 < baseStart_2313484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313501 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2313501 : Nat := 118140960795 + 2313501 * 2 ^ 59
def prefixEnd_2313501 : Nat := 4983230072969 + 3 ^ 40 * 2313501 * 2
def baseEnd_2313501 : Nat := 263986223923879588977313

theorem tailTrace_2313501 : CollatzResearch.WordTrace tailWord_2313501 prefixEnd_2313501 263986223923879588977313 := by
  unfold tailWord_2313501
  simp only [CollatzResearch.WordTrace]
  refine ⟨84380313591588466359236357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56253542394392310906157571 84380313591588466359236357)
  ·
    refine ⟨15821308798422837442356817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84380313591588466359236357 15821308798422837442356817)
    ·
      refine ⟨11865981598817128081767613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15821308798422837442356817 11865981598817128081767613)
      ·
        refine ⟨4449743099556423030662855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11865981598817128081767613 4449743099556423030662855)
        ·
          refine ⟨6674614649334634545994283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449743099556423030662855 6674614649334634545994283)
          ·
            refine ⟨10011921974001951818991425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6674614649334634545994283 10011921974001951818991425)
            ·
              refine ⟨7508941480501463864243569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10011921974001951818991425 7508941480501463864243569)
              ·
                refine ⟨5631706110376097898182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7508941480501463864243569 5631706110376097898182677)
                ·
                  refine ⟨263986223923879588977313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5631706110376097898182677 263986223923879588977313)
                  ·
                    rfl

theorem cell22_2313501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2313501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313501 prefixEnd_2313501 := by exact prefixLift 2313501
  have htrace : WordTrace (prefixWord ++ tailWord_2313501) baseStart_2313501 baseEnd_2313501 := by
    simpa [prefixWord, tailWord_2313501, baseEnd_2313501] using wordTrace_append hprefix tailTrace_2313501
  have hstable : (prefixWord ++ tailWord_2313501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313501).length < 2 ^ (prefixWord ++ tailWord_2313501).sum := by decide
  have hdescent : baseEnd_2313501 < baseStart_2313501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313503 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 1, 4]
def baseStart_2313503 : Nat := 118140960795 + 2313503 * 2 ^ 59
def prefixEnd_2313503 : Nat := 4983230072969 + 3 ^ 40 * 2313503 * 2
def baseEnd_2313503 : Nat := 791959356412511428381933

theorem tailTrace_2313503 : CollatzResearch.WordTrace tailWord_2313503 prefixEnd_2313503 791959356412511428381933 := by
  unfold tailWord_2313503
  simp only [CollatzResearch.WordTrace]
  refine ⟨84380386537581220700809163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56253591025054147133872775 84380386537581220700809163)
  ·
    refine ⟨126570579806371831051213745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84380386537581220700809163 126570579806371831051213745)
    ·
      refine ⟨94927934854778873288410309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126570579806371831051213745 94927934854778873288410309)
      ·
        refine ⟨17798987785271038741576933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94927934854778873288410309 17798987785271038741576933)
        ·
          refine ⟨3337310209738319764045675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17798987785271038741576933 3337310209738319764045675)
          ·
            refine ⟨5005965314607479646068513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337310209738319764045675 5005965314607479646068513)
            ·
              refine ⟨3754473985955609734551385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005965314607479646068513 3754473985955609734551385)
              ·
                refine ⟨2815855489466707300913539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754473985955609734551385 2815855489466707300913539)
                ·
                  refine ⟨4223783234200060951370309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815855489466707300913539 4223783234200060951370309)
                  ·
                    refine ⟨791959356412511428381933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223783234200060951370309 791959356412511428381933)
                    ·
                      rfl

theorem cell22_2313503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_2313503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313503 prefixEnd_2313503 := by exact prefixLift 2313503
  have htrace : WordTrace (prefixWord ++ tailWord_2313503) baseStart_2313503 baseEnd_2313503 := by
    simpa [prefixWord, tailWord_2313503, baseEnd_2313503] using wordTrace_append hprefix tailTrace_2313503
  have hstable : (prefixWord ++ tailWord_2313503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313503).length < 2 ^ (prefixWord ++ tailWord_2313503).sum := by decide
  have hdescent : baseEnd_2313503 < baseStart_2313503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313561 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_2313561 : Nat := 118140960795 + 2313561 * 2 ^ 59
def prefixEnd_2313561 : Nat := 4983230072969 + 3 ^ 40 * 2313561 * 2
def baseEnd_2313561 : Nat := 791979210997818610431755

theorem tailTrace_2313561 : CollatzResearch.WordTrace tailWord_2313561 prefixEnd_2313561 791979210997818610431755 := by
  unfold tailWord_2313561
  simp only [CollatzResearch.WordTrace]
  refine ⟨84382501971371096606420537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56255001314247397737613691 84382501971371096606420537)
  ·
    refine ⟨63286876478528322454815403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84382501971371096606420537 63286876478528322454815403)
    ·
      refine ⟨94930314717792483682223105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63286876478528322454815403 94930314717792483682223105)
      ·
        refine ⟨71197736038344362761667329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94930314717792483682223105 71197736038344362761667329)
        ·
          refine ⟨53398302028758272071250497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71197736038344362761667329 53398302028758272071250497)
          ·
            refine ⟨40048726521568704053437873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53398302028758272071250497 40048726521568704053437873)
            ·
              refine ⟨30036544891176528040078405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40048726521568704053437873 30036544891176528040078405)
              ·
                refine ⟨5631852167095599007514701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30036544891176528040078405 5631852167095599007514701)
                ·
                  refine ⟨2111944562660849627818013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5631852167095599007514701 2111944562660849627818013)
                  ·
                    refine ⟨791979210997818610431755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111944562660849627818013 791979210997818610431755)
                    ·
                      rfl

theorem cell22_2313561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_2313561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313561 prefixEnd_2313561 := by exact prefixLift 2313561
  have htrace : WordTrace (prefixWord ++ tailWord_2313561) baseStart_2313561 baseEnd_2313561 := by
    simpa [prefixWord, tailWord_2313561, baseEnd_2313561] using wordTrace_append hprefix tailTrace_2313561
  have hstable : (prefixWord ++ tailWord_2313561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313561).length < 2 ^ (prefixWord ++ tailWord_2313561).sum := by decide
  have hdescent : baseEnd_2313561 < baseStart_2313561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313591 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 5]
def baseStart_2313591 : Nat := 118140960795 + 2313591 * 2 ^ 59
def prefixEnd_2313591 : Nat := 4983230072969 + 3 ^ 40 * 2313591 * 2
def baseEnd_2313591 : Nat := 263996493536969510727221

theorem tailTrace_2313591 : CollatzResearch.WordTrace tailWord_2313591 prefixEnd_2313591 263996493536969510727221 := by
  unfold tailWord_2313591
  simp only [CollatzResearch.WordTrace]
  refine ⟨84383596161262411730012627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56255730774174941153341751 84383596161262411730012627)
  ·
    refine ⟨126575394241893617595018941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84383596161262411730012627 126575394241893617595018941)
    ·
      refine ⟨47465772840710106598132103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126575394241893617595018941 47465772840710106598132103)
      ·
        refine ⟨71198659261065159897198155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47465772840710106598132103 71198659261065159897198155)
        ·
          refine ⟨106797988891597739845797233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71198659261065159897198155 106797988891597739845797233)
          ·
            refine ⟨80098491668698304884347925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106797988891597739845797233 80098491668698304884347925)
            ·
              refine ⟨3754616796970233041453809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80098491668698304884347925 3754616796970233041453809)
              ·
                refine ⟨2815962597727674781090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754616796970233041453809 2815962597727674781090357)
                ·
                  refine ⟨263996493536969510727221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2815962597727674781090357 263996493536969510727221)
                  ·
                    rfl

theorem cell22_2313591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 5].length) (baseStart_2313591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313591 prefixEnd_2313591 := by exact prefixLift 2313591
  have htrace : WordTrace (prefixWord ++ tailWord_2313591) baseStart_2313591 baseEnd_2313591 := by
    simpa [prefixWord, tailWord_2313591, baseEnd_2313591] using wordTrace_append hprefix tailTrace_2313591
  have hstable : (prefixWord ++ tailWord_2313591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313591).length < 2 ^ (prefixWord ++ tailWord_2313591).sum := by decide
  have hdescent : baseEnd_2313591 < baseStart_2313591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313621 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2313621 : Nat := 118140960795 + 2313621 * 2 ^ 59
def prefixEnd_2313621 : Nat := 4983230072969 + 3 ^ 40 * 2313621 * 2
def baseEnd_2313621 : Nat := 791999750223998453931571

theorem tailTrace_2313621 : CollatzResearch.WordTrace tailWord_2313621 prefixEnd_2313621 791999750223998453931571 := by
  unfold tailWord_2313621
  simp only [CollatzResearch.WordTrace]
  refine ⟨84384690351153726853604717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56256460234102484569069811 84384690351153726853604717)
  ·
    refine ⟨31644258881682647570101769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84384690351153726853604717 31644258881682647570101769)
    ·
      refine ⟨23733194161261985677576327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31644258881682647570101769 23733194161261985677576327)
      ·
        refine ⟨35599791241892978516364491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23733194161261985677576327 35599791241892978516364491)
        ·
          refine ⟨53399686862839467774546737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35599791241892978516364491 53399686862839467774546737)
          ·
            refine ⟨40049765147129600830910053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53399686862839467774546737 40049765147129600830910053)
            ·
              refine ⟨7509330965086800155795635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40049765147129600830910053 7509330965086800155795635)
              ·
                refine ⟨11263996447630200233693453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7509330965086800155795635 11263996447630200233693453)
                ·
                  refine ⟨4223998667861325087635045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11263996447630200233693453 4223998667861325087635045)
                  ·
                    refine ⟨791999750223998453931571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223998667861325087635045 791999750223998453931571)
                    ·
                      rfl

theorem cell22_2313621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2313621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313621 prefixEnd_2313621 := by exact prefixLift 2313621
  have htrace : WordTrace (prefixWord ++ tailWord_2313621) baseStart_2313621 baseEnd_2313621 := by
    simpa [prefixWord, tailWord_2313621, baseEnd_2313621] using wordTrace_append hprefix tailTrace_2313621
  have hstable : (prefixWord ++ tailWord_2313621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313621).length < 2 ^ (prefixWord ++ tailWord_2313621).sum := by decide
  have hdescent : baseEnd_2313621 < baseStart_2313621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313653 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 6]
def baseStart_2313653 : Nat := 118140960795 + 2313653 * 2 ^ 59
def prefixEnd_2313653 : Nat := 4983230072969 + 3 ^ 40 * 2313653 * 2
def baseEnd_2313653 : Nat := 264003568159320345710491

theorem tailTrace_2313653 : CollatzResearch.WordTrace tailWord_2313653 prefixEnd_2313653 264003568159320345710491 := by
  unfold tailWord_2313653
  simp only [CollatzResearch.WordTrace]
  refine ⟨84385857487037796318769613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56257238324691864212513075 84385857487037796318769613)
  ·
    refine ⟨31644696557639173619538605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84385857487037796318769613 31644696557639173619538605)
    ·
      refine ⟨11866761209114690107326977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31644696557639173619538605 11866761209114690107326977)
      ·
        refine ⟨8900070906836017580495233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11866761209114690107326977 8900070906836017580495233)
        ·
          refine ⟨6675053180127013185371425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8900070906836017580495233 6675053180127013185371425)
          ·
            refine ⟨5006289885095259889028569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6675053180127013185371425 5006289885095259889028569)
            ·
              refine ⟨3754717413821444916771427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5006289885095259889028569 3754717413821444916771427)
              ·
                refine ⟨5632076120732167375157141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754717413821444916771427 5632076120732167375157141)
                ·
                  refine ⟨264003568159320345710491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5632076120732167375157141 264003568159320345710491)
                  ·
                    rfl

theorem cell22_2313653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_2313653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313653 prefixEnd_2313653 := by exact prefixLift 2313653
  have htrace : WordTrace (prefixWord ++ tailWord_2313653) baseStart_2313653 baseEnd_2313653 := by
    simpa [prefixWord, tailWord_2313653, baseEnd_2313653] using wordTrace_append hprefix tailTrace_2313653
  have hstable : (prefixWord ++ tailWord_2313653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313653).length < 2 ^ (prefixWord ++ tailWord_2313653).sum := by decide
  have hdescent : baseEnd_2313653 < baseStart_2313653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313760 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_2313760 : Nat := 118140960795 + 2313760 * 2 ^ 59
def prefixEnd_2313760 : Nat := 4983230072969 + 3 ^ 40 * 2313760 * 2
def baseEnd_2313760 : Nat := 264015777588216141568715

theorem tailTrace_2313760 : CollatzResearch.WordTrace tailWord_2313760 prefixEnd_2313760 264015777588216141568715 := by
  unfold tailWord_2313760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42194880048825076796457367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56259840065100102395276489 42194880048825076796457367)
  ·
    refine ⟨63292320073237615194686051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42194880048825076796457367 63292320073237615194686051)
    ·
      refine ⟨94938480109856422792029077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63292320073237615194686051 94938480109856422792029077)
      ·
        refine ⟨4450241255149519818376363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94938480109856422792029077 4450241255149519818376363)
        ·
          refine ⟨6675361882724279727564545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450241255149519818376363 6675361882724279727564545)
          ·
            refine ⟨5006521412043209795673409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6675361882724279727564545 5006521412043209795673409)
            ·
              refine ⟨3754891059032407346755057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5006521412043209795673409 3754891059032407346755057)
              ·
                refine ⟨2816168294274305510066293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754891059032407346755057 2816168294274305510066293)
                ·
                  refine ⟨264015777588216141568715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816168294274305510066293 264015777588216141568715)
                  ·
                    rfl

theorem cell22_2313760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_2313760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313760 prefixEnd_2313760 := by exact prefixLift 2313760
  have htrace : WordTrace (prefixWord ++ tailWord_2313760) baseStart_2313760 baseEnd_2313760 := by
    simpa [prefixWord, tailWord_2313760, baseEnd_2313760] using wordTrace_append hprefix tailTrace_2313760
  have hstable : (prefixWord ++ tailWord_2313760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313760).length < 2 ^ (prefixWord ++ tailWord_2313760).sum := by decide
  have hdescent : baseEnd_2313760 < baseStart_2313760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313803 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 4, 3]
def baseStart_2313803 : Nat := 118140960795 + 2313803 * 2 ^ 59
def prefixEnd_2313803 : Nat := 4983230072969 + 3 ^ 40 * 2313803 * 2
def baseEnd_2313803 : Nat := 792062052543410645881013

theorem tailTrace_2313803 : CollatzResearch.WordTrace tailWord_2313803 prefixEnd_2313803 792062052543410645881013 := by
  unfold tailWord_2313803
  simp only [CollatzResearch.WordTrace]
  refine ⟨84391328436494371936730063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56260885624329581291153375 84391328436494371936730063)
  ·
    refine ⟨126586992654741557905095095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84391328436494371936730063 126586992654741557905095095)
    ·
      refine ⟨189880488982112336857642643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126586992654741557905095095 189880488982112336857642643)
      ·
        refine ⟨284820733473168505286463965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189880488982112336857642643 284820733473168505286463965)
        ·
          refine ⟨106807775052438189482423987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284820733473168505286463965 106807775052438189482423987)
          ·
            refine ⟨160211662578657284223635981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106807775052438189482423987 160211662578657284223635981)
            ·
              refine ⟨60079373466996481583863493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160211662578657284223635981 60079373466996481583863493)
              ·
                refine ⟨11264882525061840296974405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60079373466996481583863493 11264882525061840296974405)
                ·
                  refine ⟨2112165473449095055682701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11264882525061840296974405 2112165473449095055682701)
                  ·
                    refine ⟨792062052543410645881013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112165473449095055682701 792062052543410645881013)
                    ·
                      rfl

theorem cell22_2313803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3].length) (baseStart_2313803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313803 prefixEnd_2313803 := by exact prefixLift 2313803
  have htrace : WordTrace (prefixWord ++ tailWord_2313803) baseStart_2313803 baseEnd_2313803 := by
    simpa [prefixWord, tailWord_2313803, baseEnd_2313803] using wordTrace_append hprefix tailTrace_2313803
  have hstable : (prefixWord ++ tailWord_2313803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313803).length < 2 ^ (prefixWord ++ tailWord_2313803).sum := by decide
  have hdescent : baseEnd_2313803 < baseStart_2313803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313818 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_2313818 : Nat := 118140960795 + 2313818 * 2 ^ 59
def prefixEnd_2313818 : Nat := 4983230072969 + 3 ^ 40 * 2313818 * 2
def baseEnd_2313818 : Nat := 792067187349955606755967

theorem tailTrace_2313818 : CollatzResearch.WordTrace tailWord_2313818 prefixEnd_2313818 792067187349955606755967 := by
  unfold tailWord_2313818
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097968882860007374631527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56261250354293352999017405 21097968882860007374631527)
  ·
    refine ⟨31646953324290011061947291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21097968882860007374631527 31646953324290011061947291)
    ·
      refine ⟨47470429986435016592920937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31646953324290011061947291 47470429986435016592920937)
      ·
        refine ⟨35602822489826262444690703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47470429986435016592920937 35602822489826262444690703)
        ·
          refine ⟨53404233734739393667036055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35602822489826262444690703 53404233734739393667036055)
          ·
            refine ⟨80106350602109090500554083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53404233734739393667036055 80106350602109090500554083)
            ·
              refine ⟨120159525903163635750831125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80106350602109090500554083 120159525903163635750831125)
              ·
                refine ⟨5632477776710795425820209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120159525903163635750831125 5632477776710795425820209)
                ·
                  refine ⟨4224358332533096569365157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632477776710795425820209 4224358332533096569365157)
                  ·
                    refine ⟨792067187349955606755967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4224358332533096569365157 792067187349955606755967)
                    ·
                      rfl

theorem cell22_2313818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_2313818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313818 prefixEnd_2313818 := by exact prefixLift 2313818
  have htrace : WordTrace (prefixWord ++ tailWord_2313818) baseStart_2313818 baseEnd_2313818 := by
    simpa [prefixWord, tailWord_2313818, baseEnd_2313818] using wordTrace_append hprefix tailTrace_2313818
  have hstable : (prefixWord ++ tailWord_2313818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313818).length < 2 ^ (prefixWord ++ tailWord_2313818).sum := by decide
  have hdescent : baseEnd_2313818 < baseStart_2313818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313837 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_2313837 : Nat := 118140960795 + 2313837 * 2 ^ 59
def prefixEnd_2313837 : Nat := 4983230072969 + 3 ^ 40 * 2313837 * 2
def baseEnd_2313837 : Nat := 792073691438245890530909

theorem tailTrace_2313837 : CollatzResearch.WordTrace tailWord_2313837 prefixEnd_2313837 792073691438245890530909 := by
  unfold tailWord_2313837
  simp only [CollatzResearch.WordTrace]
  refine ⟨84392568518371195743467765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56261712345580797162311843 84392568518371195743467765)
  ·
    refine ⟨7911803298597299600950103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84392568518371195743467765 7911803298597299600950103)
    ·
      refine ⟨11867704947895949401425155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7911803298597299600950103 11867704947895949401425155)
      ·
        refine ⟨17801557421843924102137733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11867704947895949401425155 17801557421843924102137733)
        ·
          refine ⟨3337792016595735769150825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17801557421843924102137733 3337792016595735769150825)
          ·
            refine ⟨2503344012446801826863119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337792016595735769150825 2503344012446801826863119)
            ·
              refine ⟨3755016018670202740294679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503344012446801826863119 3755016018670202740294679)
              ·
                refine ⟨5632524028005304110442019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3755016018670202740294679 5632524028005304110442019)
                ·
                  refine ⟨8448786042007956165663029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5632524028005304110442019 8448786042007956165663029)
                  ·
                    refine ⟨792073691438245890530909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8448786042007956165663029 792073691438245890530909)
                    ·
                      rfl

theorem cell22_2313837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_2313837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313837 prefixEnd_2313837 := by exact prefixLift 2313837
  have htrace : WordTrace (prefixWord ++ tailWord_2313837) baseStart_2313837 baseEnd_2313837 := by
    simpa [prefixWord, tailWord_2313837, baseEnd_2313837] using wordTrace_append hprefix tailTrace_2313837
  have hstable : (prefixWord ++ tailWord_2313837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313837).length < 2 ^ (prefixWord ++ tailWord_2313837).sum := by decide
  have hdescent : baseEnd_2313837 < baseStart_2313837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313893 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_2313893 : Nat := 118140960795 + 2313893 * 2 ^ 59
def prefixEnd_2313893 : Nat := 4983230072969 + 3 ^ 40 * 2313893 * 2
def baseEnd_2313893 : Nat := 792092861382680411130737

theorem tailTrace_2313893 : CollatzResearch.WordTrace tailWord_2313893 prefixEnd_2313893 792092861382680411130737 := by
  unfold tailWord_2313893
  simp only [CollatzResearch.WordTrace]
  refine ⟨84394611006168317307506333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56263074004112211538337555 84394611006168317307506333)
  ·
    refine ⟨31647979127313118990314875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84394611006168317307506333 31647979127313118990314875)
    ·
      refine ⟨47471968690969678485472313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31647979127313118990314875 47471968690969678485472313)
      ·
        refine ⟨35603976518227258864104235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47471968690969678485472313 35603976518227258864104235)
        ·
          refine ⟨53405964777340888296156353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35603976518227258864104235 53405964777340888296156353)
          ·
            refine ⟨40054473583005666222117265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53405964777340888296156353 40054473583005666222117265)
            ·
              refine ⟨30040855187254249666587949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40054473583005666222117265 30040855187254249666587949)
              ·
                refine ⟨11265320695220343624970481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30040855187254249666587949 11265320695220343624970481)
                ·
                  refine ⟨8448990521415257718727861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11265320695220343624970481 8448990521415257718727861)
                  ·
                    refine ⟨792092861382680411130737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8448990521415257718727861 792092861382680411130737)
                    ·
                      rfl

theorem cell22_2313893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_2313893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313893 prefixEnd_2313893 := by exact prefixLift 2313893
  have htrace : WordTrace (prefixWord ++ tailWord_2313893) baseStart_2313893 baseEnd_2313893 := by
    simpa [prefixWord, tailWord_2313893, baseEnd_2313893] using wordTrace_append hprefix tailTrace_2313893
  have hstable : (prefixWord ++ tailWord_2313893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313893).length < 2 ^ (prefixWord ++ tailWord_2313893).sum := by decide
  have hdescent : baseEnd_2313893 < baseStart_2313893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313933 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2313933 : Nat := 118140960795 + 2313933 * 2 ^ 59
def prefixEnd_2313933 : Nat := 4983230072969 + 3 ^ 40 * 2313933 * 2
def baseEnd_2313933 : Nat := 792106554200133640130615

theorem tailTrace_2313933 : CollatzResearch.WordTrace tailWord_2313933 prefixEnd_2313933 792106554200133640130615 := by
  unfold tailWord_2313933
  simp only [CollatzResearch.WordTrace]
  refine ⟨84396069926023404138962453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56264046617348936092641635 84396069926023404138962453)
  ·
    refine ⟨3956065777782347069013865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84396069926023404138962453 3956065777782347069013865)
    ·
      refine ⟨2967049333336760301760399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3956065777782347069013865 2967049333336760301760399)
      ·
        refine ⟨4450574000005140452640599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967049333336760301760399 4450574000005140452640599)
        ·
          refine ⟨6675861000007710678960899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450574000005140452640599 6675861000007710678960899)
          ·
            refine ⟨10013791500011566018441349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675861000007710678960899 10013791500011566018441349)
            ·
              refine ⟨1877585906252168628457753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10013791500011566018441349 1877585906252168628457753)
              ·
                refine ⟨1408189429689126471343315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877585906252168628457753 1408189429689126471343315)
                ·
                  refine ⟨2112284144533689707014973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408189429689126471343315 2112284144533689707014973)
                  ·
                    refine ⟨792106554200133640130615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112284144533689707014973 792106554200133640130615)
                    ·
                      rfl

theorem cell22_2313933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2313933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313933 prefixEnd_2313933 := by exact prefixLift 2313933
  have htrace : WordTrace (prefixWord ++ tailWord_2313933) baseStart_2313933 baseEnd_2313933 := by
    simpa [prefixWord, tailWord_2313933, baseEnd_2313933] using wordTrace_append hprefix tailTrace_2313933
  have hstable : (prefixWord ++ tailWord_2313933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313933).length < 2 ^ (prefixWord ++ tailWord_2313933).sum := by decide
  have hdescent : baseEnd_2313933 < baseStart_2313933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313970 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2313970 : Nat := 118140960795 + 2313970 * 2 ^ 59
def prefixEnd_2313970 : Nat := 4983230072969 + 3 ^ 40 * 2313970 * 2
def baseEnd_2313970 : Nat := 792119220056277876955501

theorem tailTrace_2313970 : CollatzResearch.WordTrace tailWord_2313970 prefixEnd_2313970 792119220056277876955501 := by
  unfold tailWord_2313970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21099354856722339864514841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56264946284592906305372909 21099354856722339864514841)
  ·
    refine ⟨15824516142541754898386131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21099354856722339864514841 15824516142541754898386131)
    ·
      refine ⟨23736774213812632347579197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15824516142541754898386131 23736774213812632347579197)
      ·
        refine ⟨8901290330179737130342199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23736774213812632347579197 8901290330179737130342199)
        ·
          refine ⟨13351935495269605695513299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8901290330179737130342199 13351935495269605695513299)
          ·
            refine ⟨20027903242904408543269949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13351935495269605695513299 20027903242904408543269949)
            ·
              refine ⟨7510463716089153203726231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20027903242904408543269949 7510463716089153203726231)
              ·
                refine ⟨11265695574133729805589347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510463716089153203726231 11265695574133729805589347)
                ·
                  refine ⟨16898543361200594708384021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11265695574133729805589347 16898543361200594708384021)
                  ·
                    refine ⟨792119220056277876955501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16898543361200594708384021 792119220056277876955501)
                    ·
                      rfl

theorem cell22_2313970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2313970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313970 prefixEnd_2313970 := by exact prefixLift 2313970
  have htrace : WordTrace (prefixWord ++ tailWord_2313970) baseStart_2313970 baseEnd_2313970 := by
    simpa [prefixWord, tailWord_2313970, baseEnd_2313970] using wordTrace_append hprefix tailTrace_2313970
  have hstable : (prefixWord ++ tailWord_2313970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313970).length < 2 ^ (prefixWord ++ tailWord_2313970).sum := by decide
  have hdescent : baseEnd_2313970 < baseStart_2313970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2313974 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_2313974 : Nat := 118140960795 + 2313974 * 2 ^ 59
def prefixEnd_2313974 : Nat := 4983230072969 + 3 ^ 40 * 2313974 * 2
def baseEnd_2313974 : Nat := 264040196446007733285163

theorem tailTrace_2313974 : CollatzResearch.WordTrace tailWord_2313974 prefixEnd_2313974 264040196446007733285163 := by
  unfold tailWord_2313974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274847832429679258825311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56265043545916578760803317 5274847832429679258825311)
  ·
    refine ⟨7912271748644518888237967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5274847832429679258825311 7912271748644518888237967)
    ·
      refine ⟨11868407622966778332356951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7912271748644518888237967 11868407622966778332356951)
      ·
        refine ⟨17802611434450167498535427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11868407622966778332356951 17802611434450167498535427)
        ·
          refine ⟨26703917151675251247803141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17802611434450167498535427 26703917151675251247803141)
          ·
            refine ⟨5006984465939109608963089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26703917151675251247803141 5006984465939109608963089)
            ·
              refine ⟨3755238349454332206722317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5006984465939109608963089 3755238349454332206722317)
              ·
                refine ⟨1408214381045374577520869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3755238349454332206722317 1408214381045374577520869)
                ·
                  refine ⟨264040196446007733285163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408214381045374577520869 264040196446007733285163)
                  ·
                    rfl

theorem cell22_2313974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_2313974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2313974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2313974 prefixEnd_2313974 := by exact prefixLift 2313974
  have htrace : WordTrace (prefixWord ++ tailWord_2313974) baseStart_2313974 baseEnd_2313974 := by
    simpa [prefixWord, tailWord_2313974, baseEnd_2313974] using wordTrace_append hprefix tailTrace_2313974
  have hstable : (prefixWord ++ tailWord_2313974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2313974).length < 2 ^ (prefixWord ++ tailWord_2313974).sum := by decide
  have hdescent : baseEnd_2313974 < baseStart_2313974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2313974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314017 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2314017 : Nat := 118140960795 + 2314017 * 2 ^ 59
def prefixEnd_2314017 : Nat := 4983230072969 + 3 ^ 40 * 2314017 * 2
def baseEnd_2314017 : Nat := 792135309116785421030357

theorem tailTrace_2314017 : CollatzResearch.WordTrace tailWord_2314017 prefixEnd_2314017 792135309116785421030357 := by
  unfold tailWord_2314017
  simp only [CollatzResearch.WordTrace]
  refine ⟨84399133657719086485020305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56266089105146057656680203 84399133657719086485020305)
  ·
    refine ⟨63299350243289314863765229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84399133657719086485020305 63299350243289314863765229)
    ·
      refine ⟨23737256341233493073911961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63299350243289314863765229 23737256341233493073911961)
      ·
        refine ⟨17802942255925119805433971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23737256341233493073911961 17802942255925119805433971)
        ·
          refine ⟨26704413383887679708150957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17802942255925119805433971 26704413383887679708150957)
          ·
            refine ⟨10014155018957879890556609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26704413383887679708150957 10014155018957879890556609)
            ·
              refine ⟨7510616264218409917917457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10014155018957879890556609 7510616264218409917917457)
              ·
                refine ⟨5632962198163807438438093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7510616264218409917917457 5632962198163807438438093)
                ·
                  refine ⟨2112360824311427789414285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5632962198163807438438093 2112360824311427789414285)
                  ·
                    refine ⟨792135309116785421030357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112360824311427789414285 792135309116785421030357)
                    ·
                      rfl

theorem cell22_2314017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2314017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314017 prefixEnd_2314017 := by exact prefixLift 2314017
  have htrace : WordTrace (prefixWord ++ tailWord_2314017) baseStart_2314017 baseEnd_2314017 := by
    simpa [prefixWord, tailWord_2314017, baseEnd_2314017] using wordTrace_append hprefix tailTrace_2314017
  have hstable : (prefixWord ++ tailWord_2314017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314017).length < 2 ^ (prefixWord ++ tailWord_2314017).sum := by decide
  have hdescent : baseEnd_2314017 < baseStart_2314017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314051 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 1, 3]
def baseStart_2314051 : Nat := 118140960795 + 2314051 * 2 ^ 59
def prefixEnd_2314051 : Nat := 4983230072969 + 3 ^ 40 * 2314051 * 2
def baseEnd_2314051 : Nat := 792146948011620665680253

theorem tailTrace_2314051 : CollatzResearch.WordTrace tailWord_2314051 prefixEnd_2314051 792146948011620665680253 := by
  unfold tailWord_2314051
  simp only [CollatzResearch.WordTrace]
  refine ⟨84400373739595910291758007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56266915826397273527838671 84400373739595910291758007)
  ·
    refine ⟨126600560609393865437637011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84400373739595910291758007 126600560609393865437637011)
    ·
      refine ⟨189900840914090798156455517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126600560609393865437637011 189900840914090798156455517)
      ·
        refine ⟨71212815342784049308670819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189900840914090798156455517 71212815342784049308670819)
        ·
          refine ⟨106819223014176073963006229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71212815342784049308670819 106819223014176073963006229)
          ·
            refine ⟨5007151078789503467015917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106819223014176073963006229 5007151078789503467015917)
            ·
              refine ⟨1877681654546063800130969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5007151078789503467015917 1877681654546063800130969)
              ·
                refine ⟨1408261240909547850098227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877681654546063800130969 1408261240909547850098227)
                ·
                  refine ⟨2112391861364321775147341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408261240909547850098227 2112391861364321775147341)
                  ·
                    refine ⟨792146948011620665680253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112391861364321775147341 792146948011620665680253)
                    ·
                      rfl

theorem cell22_2314051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 3].length) (baseStart_2314051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314051 prefixEnd_2314051 := by exact prefixLift 2314051
  have htrace : WordTrace (prefixWord ++ tailWord_2314051) baseStart_2314051 baseEnd_2314051 := by
    simpa [prefixWord, tailWord_2314051, baseEnd_2314051] using wordTrace_append hprefix tailTrace_2314051
  have hstable : (prefixWord ++ tailWord_2314051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314051).length < 2 ^ (prefixWord ++ tailWord_2314051).sum := by decide
  have hdescent : baseEnd_2314051 < baseStart_2314051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314102 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2314102 : Nat := 118140960795 + 2314102 * 2 ^ 59
def prefixEnd_2314102 : Nat := 4983230072969 + 3 ^ 40 * 2314102 * 2
def baseEnd_2314102 : Nat := 792164406353873532655097

theorem tailTrace_2314102 : CollatzResearch.WordTrace tailWord_2314102 prefixEnd_2314102 792164406353873532655097 := by
  unfold tailWord_2314102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275139616400696625116535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56268155908274097334576373 5275139616400696625116535)
  ·
    refine ⟨7912709424601044937674803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5275139616400696625116535 7912709424601044937674803)
    ·
      refine ⟨11869064136901567406512205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7912709424601044937674803 11869064136901567406512205)
      ·
        refine ⟨4450899051338087777442077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11869064136901567406512205 4450899051338087777442077)
        ·
          refine ⟨1669087144251782916540779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4450899051338087777442077 1669087144251782916540779)
          ·
            refine ⟨2503630716377674374811169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669087144251782916540779 2503630716377674374811169)
            ·
              refine ⟨1877723037283255781108377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503630716377674374811169 1877723037283255781108377)
              ·
                refine ⟨1408292277962441835831283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877723037283255781108377 1408292277962441835831283)
                ·
                  refine ⟨2112438416943662753746925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408292277962441835831283 2112438416943662753746925)
                  ·
                    refine ⟨792164406353873532655097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112438416943662753746925 792164406353873532655097)
                    ·
                      rfl

theorem cell22_2314102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2314102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314102 prefixEnd_2314102 := by exact prefixLift 2314102
  have htrace : WordTrace (prefixWord ++ tailWord_2314102) baseStart_2314102 baseEnd_2314102 := by
    simpa [prefixWord, tailWord_2314102, baseEnd_2314102] using wordTrace_append hprefix tailTrace_2314102
  have hstable : (prefixWord ++ tailWord_2314102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314102).length < 2 ^ (prefixWord ++ tailWord_2314102).sum := by decide
  have hdescent : baseEnd_2314102 < baseStart_2314102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314169 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_2314169 : Nat := 118140960795 + 2314169 * 2 ^ 59
def prefixEnd_2314169 : Nat := 4983230072969 + 3 ^ 40 * 2314169 * 2
def baseEnd_2314169 : Nat := 792187341823107691229891

theorem tailTrace_2314169 : CollatzResearch.WordTrace tailWord_2314169 prefixEnd_2314169 792187341823107691229891 := by
  unfold tailWord_2314169
  simp only [CollatzResearch.WordTrace]
  refine ⟨84404677553168416444553561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56269785035445610963035707 84404677553168416444553561)
  ·
    refine ⟨63303508164876312333415171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84404677553168416444553561 63303508164876312333415171)
    ·
      refine ⟨94955262247314468500122757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63303508164876312333415171 94955262247314468500122757)
      ·
        refine ⟨17804111671371462843773017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94955262247314468500122757 17804111671371462843773017)
        ·
          refine ⟨13353083753528597132829763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17804111671371462843773017 13353083753528597132829763)
          ·
            refine ⟨20029625630292895699244645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13353083753528597132829763 20029625630292895699244645)
            ·
              refine ⟨3755554805679917943608371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20029625630292895699244645 3755554805679917943608371)
              ·
                refine ⟨5633332208519876915412557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3755554805679917943608371 5633332208519876915412557)
                ·
                  refine ⟨2112499578194953843279709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5633332208519876915412557 2112499578194953843279709)
                  ·
                    refine ⟨792187341823107691229891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112499578194953843279709 792187341823107691229891)
                    ·
                      rfl

theorem cell22_2314169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_2314169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314169 prefixEnd_2314169 := by exact prefixLift 2314169
  have htrace : WordTrace (prefixWord ++ tailWord_2314169) baseStart_2314169 baseEnd_2314169 := by
    simpa [prefixWord, tailWord_2314169, baseEnd_2314169] using wordTrace_append hprefix tailTrace_2314169
  have hstable : (prefixWord ++ tailWord_2314169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314169).length < 2 ^ (prefixWord ++ tailWord_2314169).sum := by decide
  have hdescent : baseEnd_2314169 < baseStart_2314169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314263 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 1, 4]
def baseStart_2314263 : Nat := 118140960795 + 2314263 * 2 ^ 59
def prefixEnd_2314263 : Nat := 4983230072969 + 3 ^ 40 * 2314263 * 2
def baseEnd_2314263 : Nat := 792219519944122779379603

theorem tailTrace_2314263 : CollatzResearch.WordTrace tailWord_2314263 prefixEnd_2314263 792219519944122779379603 := by
  unfold tailWord_2314263
  simp only [CollatzResearch.WordTrace]
  refine ⟨84408106014827870498475443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56272070676551913665650295 84408106014827870498475443)
  ·
    refine ⟨126612159022241805747713165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84408106014827870498475443 126612159022241805747713165)
    ·
      refine ⟨47479559633340677155392437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126612159022241805747713165 47479559633340677155392437)
      ·
        refine ⟨4451208715625688483318041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47479559633340677155392437 4451208715625688483318041)
        ·
          refine ⟨3338406536719266362488531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4451208715625688483318041 3338406536719266362488531)
          ·
            refine ⟨5007609805078899543732797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338406536719266362488531 5007609805078899543732797)
            ·
              refine ⟨1877853676904587328899799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5007609805078899543732797 1877853676904587328899799)
              ·
                refine ⟨2816780515356880993349699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877853676904587328899799 2816780515356880993349699)
                ·
                  refine ⟨4225170773035321490024549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816780515356880993349699 4225170773035321490024549)
                  ·
                    refine ⟨792219519944122779379603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225170773035321490024549 792219519944122779379603)
                    ·
                      rfl

theorem cell22_2314263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_2314263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314263 prefixEnd_2314263 := by exact prefixLift 2314263
  have htrace : WordTrace (prefixWord ++ tailWord_2314263) baseStart_2314263 baseEnd_2314263 := by
    simpa [prefixWord, tailWord_2314263, baseEnd_2314263] using wordTrace_append hprefix tailTrace_2314263
  have hstable : (prefixWord ++ tailWord_2314263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314263).length < 2 ^ (prefixWord ++ tailWord_2314263).sum := by decide
  have hdescent : baseEnd_2314263 < baseStart_2314263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314274 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2314274 : Nat := 118140960795 + 2314274 * 2 ^ 59
def prefixEnd_2314274 : Nat := 4983230072969 + 3 ^ 40 * 2314274 * 2
def baseEnd_2314274 : Nat := 792223285468922417354569

theorem tailTrace_2314274 : CollatzResearch.WordTrace tailWord_2314274 prefixEnd_2314274 792223285468922417354569 := by
  unfold tailWord_2314274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21102126804447004844281469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56272338145192012918083917 21102126804447004844281469)
  ·
    refine ⟨7913297551667626816605551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21102126804447004844281469 7913297551667626816605551)
    ·
      refine ⟨11869946327501440224908327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7913297551667626816605551 11869946327501440224908327)
      ·
        refine ⟨17804919491252160337362491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11869946327501440224908327 17804919491252160337362491)
        ·
          refine ⟨26707379236878240506043737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17804919491252160337362491 26707379236878240506043737)
          ·
            refine ⟨20030534427658680379532803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26707379236878240506043737 20030534427658680379532803)
            ·
              refine ⟨30045801641488020569299205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20030534427658680379532803 30045801641488020569299205)
              ·
                refine ⟨5633587807779003856743601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30045801641488020569299205 5633587807779003856743601)
                ·
                  refine ⟨4225190855834252892557701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5633587807779003856743601 4225190855834252892557701)
                  ·
                    refine ⟨792223285468922417354569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225190855834252892557701 792223285468922417354569)
                    ·
                      rfl

theorem cell22_2314274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2314274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314274 prefixEnd_2314274 := by exact prefixLift 2314274
  have htrace : WordTrace (prefixWord ++ tailWord_2314274) baseStart_2314274 baseEnd_2314274 := by
    simpa [prefixWord, tailWord_2314274, baseEnd_2314274] using wordTrace_append hprefix tailTrace_2314274
  have hstable : (prefixWord ++ tailWord_2314274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314274).length < 2 ^ (prefixWord ++ tailWord_2314274).sum := by decide
  have hdescent : baseEnd_2314274 < baseStart_2314274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314289 : List Nat := [1, 2, 2, 3, 1, 5, 1, 7]
def baseStart_2314289 : Nat := 118140960795 + 2314289 * 2 ^ 59
def prefixEnd_2314289 : Nat := 4983230072969 + 3 ^ 40 * 2314289 * 2
def baseEnd_2314289 : Nat := 88025380030607486469947

theorem tailTrace_2314289 : CollatzResearch.WordTrace tailWord_2314289 prefixEnd_2314289 88025380030607486469947 := by
  unfold tailWord_2314289
  simp only [CollatzResearch.WordTrace]
  refine ⟨84409054312733676938921921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56272702875155784625947947 84409054312733676938921921)
  ·
    refine ⟨63306790734550257704191441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84409054312733676938921921 63306790734550257704191441)
    ·
      refine ⟨47480093050912693278143581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63306790734550257704191441 47480093050912693278143581)
      ·
        refine ⟨17805034894092259979303843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47480093050912693278143581 17805034894092259979303843)
        ·
          refine ⟨26707552341138389968955765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17805034894092259979303843 26707552341138389968955765)
          ·
            refine ⟨2503833031981724059589603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26707552341138389968955765 2503833031981724059589603)
            ·
              refine ⟨3755749547972586089384405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503833031981724059589603 3755749547972586089384405)
              ·
                refine ⟨88025380030607486469947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3755749547972586089384405 88025380030607486469947)
                ·
                  rfl

theorem cell22_2314289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 7].length) (baseStart_2314289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314289 prefixEnd_2314289 := by exact prefixLift 2314289
  have htrace : WordTrace (prefixWord ++ tailWord_2314289) baseStart_2314289 baseEnd_2314289 := by
    simpa [prefixWord, tailWord_2314289, baseEnd_2314289] using wordTrace_append hprefix tailTrace_2314289
  have hstable : (prefixWord ++ tailWord_2314289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314289).length < 2 ^ (prefixWord ++ tailWord_2314289).sum := by decide
  have hdescent : baseEnd_2314289 < baseStart_2314289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314304 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_2314304 : Nat := 118140960795 + 2314304 * 2 ^ 59
def prefixEnd_2314304 : Nat := 4983230072969 + 3 ^ 40 * 2314304 * 2
def baseEnd_2314304 : Nat := 792233555082012339104477

theorem tailTrace_2314304 : CollatzResearch.WordTrace tailWord_2314304 prefixEnd_2314304 792233555082012339104477 := by
  unfold tailWord_2314304
  simp only [CollatzResearch.WordTrace]
  refine ⟨42204800703839667250358983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56273067605119556333811977 42204800703839667250358983)
  ·
    refine ⟨63307201055759500875538475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42204800703839667250358983 63307201055759500875538475)
    ·
      refine ⟨94960801583639251313307713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63307201055759500875538475 94960801583639251313307713)
      ·
        refine ⟨71220601187729438484980785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94960801583639251313307713 71220601187729438484980785)
        ·
          refine ⟨53415450890797078863735589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71220601187729438484980785 53415450890797078863735589)
          ·
            refine ⟨10015397042024452286950423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53415450890797078863735589 10015397042024452286950423)
            ·
              refine ⟨15023095563036678430425635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10015397042024452286950423 15023095563036678430425635)
              ·
                refine ⟨22534643344555017645638453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15023095563036678430425635 22534643344555017645638453)
                ·
                  refine ⟨2112622813552032904278605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22534643344555017645638453 2112622813552032904278605)
                  ·
                    refine ⟨792233555082012339104477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112622813552032904278605 792233555082012339104477)
                    ·
                      rfl

theorem cell22_2314304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_2314304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314304 prefixEnd_2314304 := by exact prefixLift 2314304
  have htrace : WordTrace (prefixWord ++ tailWord_2314304) baseStart_2314304 baseEnd_2314304 := by
    simpa [prefixWord, tailWord_2314304, baseEnd_2314304] using wordTrace_append hprefix tailTrace_2314304
  have hstable : (prefixWord ++ tailWord_2314304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314304).length < 2 ^ (prefixWord ++ tailWord_2314304).sum := by decide
  have hdescent : baseEnd_2314304 < baseStart_2314304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314349 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2314349 : Nat := 118140960795 + 2314349 * 2 ^ 59
def prefixEnd_2314349 : Nat := 4983230072969 + 3 ^ 40 * 2314349 * 2
def baseEnd_2314349 : Nat := 792248959501647221729339

theorem tailTrace_2314349 : CollatzResearch.WordTrace tailWord_2314349 prefixEnd_2314349 792248959501647221729339 := by
  unfold tailWord_2314349
  simp only [CollatzResearch.WordTrace]
  refine ⟨84411242692516307186106101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56274161795010871457404067 84411242692516307186106101)
  ·
    refine ⟨7913554002423403798697447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84411242692516307186106101 7913554002423403798697447)
    ·
      refine ⟨11870331003635105698046171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7913554002423403798697447 11870331003635105698046171)
      ·
        refine ⟨17805496505452658547069257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11870331003635105698046171 17805496505452658547069257)
        ·
          refine ⟨13354122379089493910301943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17805496505452658547069257 13354122379089493910301943)
          ·
            refine ⟨20031183568634240865452915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13354122379089493910301943 20031183568634240865452915)
            ·
              refine ⟨30046775352951361298179373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20031183568634240865452915 30046775352951361298179373)
              ·
                refine ⟨11267540757356760486817265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30046775352951361298179373 11267540757356760486817265)
                ·
                  refine ⟨8450655568017570365112949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11267540757356760486817265 8450655568017570365112949)
                  ·
                    refine ⟨792248959501647221729339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8450655568017570365112949 792248959501647221729339)
                    ·
                      rfl

theorem cell22_2314349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2314349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314349 prefixEnd_2314349 := by exact prefixLift 2314349
  have htrace : WordTrace (prefixWord ++ tailWord_2314349) baseStart_2314349 baseEnd_2314349 := by
    simpa [prefixWord, tailWord_2314349, baseEnd_2314349] using wordTrace_append hprefix tailTrace_2314349
  have hstable : (prefixWord ++ tailWord_2314349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314349).length < 2 ^ (prefixWord ++ tailWord_2314349).sum := by decide
  have hdescent : baseEnd_2314349 < baseStart_2314349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314351 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 5]
def baseStart_2314351 : Nat := 118140960795 + 2314351 * 2 ^ 59
def prefixEnd_2314351 : Nat := 4983230072969 + 3 ^ 40 * 2314351 * 2
def baseEnd_2314351 : Nat := 264083214714173294393111

theorem tailTrace_2314351 : CollatzResearch.WordTrace tailWord_2314351 prefixEnd_2314351 264083214714173294393111 := by
  unfold tailWord_2314351
  simp only [CollatzResearch.WordTrace]
  refine ⟨84411315638509061527678907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56274210425672707685119271 84411315638509061527678907)
  ·
    refine ⟨126616973457763592291518361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84411315638509061527678907 126616973457763592291518361)
    ·
      refine ⟨94962730093322694218638771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126616973457763592291518361 94962730093322694218638771)
      ·
        refine ⟨142444095139984041327958157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94962730093322694218638771 142444095139984041327958157)
        ·
          refine ⟨53416535677494015497984309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142444095139984041327958157 53416535677494015497984309)
          ·
            refine ⟨5007800219765063952936029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53416535677494015497984309 5007800219765063952936029)
            ·
              refine ⟨1877925082411898982351011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5007800219765063952936029 1877925082411898982351011)
              ·
                refine ⟨2816887623617848473526517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877925082411898982351011 2816887623617848473526517)
                ·
                  refine ⟨264083214714173294393111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816887623617848473526517 264083214714173294393111)
                  ·
                    rfl

theorem cell22_2314351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 5].length) (baseStart_2314351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314351 prefixEnd_2314351 := by exact prefixLift 2314351
  have htrace : WordTrace (prefixWord ++ tailWord_2314351) baseStart_2314351 baseEnd_2314351 := by
    simpa [prefixWord, tailWord_2314351, baseEnd_2314351] using wordTrace_append hprefix tailTrace_2314351
  have hstable : (prefixWord ++ tailWord_2314351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314351).length < 2 ^ (prefixWord ++ tailWord_2314351).sum := by decide
  have hdescent : baseEnd_2314351 < baseStart_2314351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314490 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_2314490 : Nat := 118140960795 + 2314490 * 2 ^ 59
def prefixEnd_2314490 : Nat := 4983230072969 + 3 ^ 40 * 2314490 * 2
def baseEnd_2314490 : Nat := 792297226683169853953907

theorem tailTrace_2314490 : CollatzResearch.WordTrace tailWord_2314490 prefixEnd_2314490 792297226683169853953907 := by
  unfold tailWord_2314490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21104096346251372066747231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56277590256670325511325949 21104096346251372066747231)
  ·
    refine ⟨31656144519377058100120847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21104096346251372066747231 31656144519377058100120847)
    ·
      refine ⟨47484216779065587150181271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31656144519377058100120847 47484216779065587150181271)
      ·
        refine ⟨71226325168598380725271907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47484216779065587150181271 71226325168598380725271907)
        ·
          refine ⟨106839487752897571087907861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71226325168598380725271907 106839487752897571087907861)
          ·
            refine ⟨5008100988417073644745681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106839487752897571087907861 5008100988417073644745681)
            ·
              refine ⟨3756075741312805233559261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008100988417073644745681 3756075741312805233559261)
              ·
                refine ⟨1408528402992301962584723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3756075741312805233559261 1408528402992301962584723)
                ·
                  refine ⟨2112792604488452943877085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408528402992301962584723 2112792604488452943877085)
                  ·
                    refine ⟨792297226683169853953907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112792604488452943877085 792297226683169853953907)
                    ·
                      rfl

theorem cell22_2314490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_2314490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314490 prefixEnd_2314490 := by exact prefixLift 2314490
  have htrace : WordTrace (prefixWord ++ tailWord_2314490) baseStart_2314490 baseEnd_2314490 := by
    simpa [prefixWord, tailWord_2314490, baseEnd_2314490] using wordTrace_append hprefix tailTrace_2314490
  have hstable : (prefixWord ++ tailWord_2314490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314490).length < 2 ^ (prefixWord ++ tailWord_2314490).sum := by decide
  have hdescent : baseEnd_2314490 < baseStart_2314490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314503 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 7]
def baseStart_2314503 : Nat := 118140960795 + 2314503 * 2 ^ 59
def prefixEnd_2314503 : Nat := 4983230072969 + 3 ^ 40 * 2314503 * 2
def baseEnd_2314503 : Nat := 264100558949614051126289

theorem tailTrace_2314503 : CollatzResearch.WordTrace tailWord_2314503 prefixEnd_2314503 264100558949614051126289 := by
  unfold tailWord_2314503
  simp only [CollatzResearch.WordTrace]
  refine ⟨84416859533958391487212163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56277906355972260991474775 84416859533958391487212163)
  ·
    refine ⟨126625289300937587230818245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84416859533958391487212163 126625289300937587230818245)
    ·
      refine ⟨23742241743925797605778421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126625289300937587230818245 23742241743925797605778421)
      ·
        refine ⟨2225835163493043525541727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23742241743925797605778421 2225835163493043525541727)
        ·
          refine ⟨3338752745239565288312591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225835163493043525541727 3338752745239565288312591)
          ·
            refine ⟨5008129117859347932468887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338752745239565288312591 5008129117859347932468887)
            ·
              refine ⟨7512193676789021898703331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008129117859347932468887 7512193676789021898703331)
              ·
                refine ⟨11268290515183532848054997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512193676789021898703331 11268290515183532848054997)
                ·
                  refine ⟨264100558949614051126289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11268290515183532848054997 264100558949614051126289)
                  ·
                    rfl

theorem cell22_2314503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 7].length) (baseStart_2314503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314503 prefixEnd_2314503 := by exact prefixLift 2314503
  have htrace : WordTrace (prefixWord ++ tailWord_2314503) baseStart_2314503 baseEnd_2314503 := by
    simpa [prefixWord, tailWord_2314503, baseEnd_2314503] using wordTrace_append hprefix tailTrace_2314503
  have hstable : (prefixWord ++ tailWord_2314503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314503).length < 2 ^ (prefixWord ++ tailWord_2314503).sum := by decide
  have hdescent : baseEnd_2314503 < baseStart_2314503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314541 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2314541 : Nat := 118140960795 + 2314541 * 2 ^ 59
def prefixEnd_2314541 : Nat := 4983230072969 + 3 ^ 40 * 2314541 * 2
def baseEnd_2314541 : Nat := 792314685025422720928751

theorem tailTrace_2314541 : CollatzResearch.WordTrace tailWord_2314541 prefixEnd_2314541 792314685025422720928751 := by
  unfold tailWord_2314541
  simp only [CollatzResearch.WordTrace]
  refine ⟨84418245507820723977095477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56278830338547149318063651 84418245507820723977095477)
  ·
    refine ⟨7914210516358192872852701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84418245507820723977095477 7914210516358192872852701)
    ·
      refine ⟨2967828943634322327319763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7914210516358192872852701 2967828943634322327319763)
      ·
        refine ⟨4451743415451483490979645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967828943634322327319763 4451743415451483490979645)
        ·
          refine ⟨1669403780794306309117367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4451743415451483490979645 1669403780794306309117367)
          ·
            refine ⟨2504105671191459463676051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669403780794306309117367 2504105671191459463676051)
            ·
              refine ⟨3756158506787189195514077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504105671191459463676051 3756158506787189195514077)
              ·
                refine ⟨1408559440045195948317779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3756158506787189195514077 1408559440045195948317779)
                ·
                  refine ⟨2112839160067793922476669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408559440045195948317779 2112839160067793922476669)
                  ·
                    refine ⟨792314685025422720928751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112839160067793922476669 792314685025422720928751)
                    ·
                      rfl

theorem cell22_2314541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2314541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314541 prefixEnd_2314541 := by exact prefixLift 2314541
  have htrace : WordTrace (prefixWord ++ tailWord_2314541) baseStart_2314541 baseEnd_2314541 := by
    simpa [prefixWord, tailWord_2314541, baseEnd_2314541] using wordTrace_append hprefix tailTrace_2314541
  have hstable : (prefixWord ++ tailWord_2314541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314541).length < 2 ^ (prefixWord ++ tailWord_2314541).sum := by decide
  have hdescent : baseEnd_2314541 < baseStart_2314541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314576 : List Nat := [2, 1, 1, 1, 1, 7, 2, 7]
def baseStart_2314576 : Nat := 118140960795 + 2314576 * 2 ^ 59
def prefixEnd_2314576 : Nat := 4983230072969 + 3 ^ 40 * 2314576 * 2
def baseEnd_2314576 : Nat := 88036296248966032922627

theorem tailTrace_2314576 : CollatzResearch.WordTrace tailWord_2314576 prefixEnd_2314576 88036296248966032922627 := by
  unfold tailWord_2314576
  simp only [CollatzResearch.WordTrace]
  refine ⟨42209761031346962477309791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56279681375129283303079721 42209761031346962477309791)
  ·
    refine ⟨63314641547020443715964687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42209761031346962477309791 63314641547020443715964687)
    ·
      refine ⟨94971962320530665573947031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63314641547020443715964687 94971962320530665573947031)
      ·
        refine ⟨142457943480795998360920547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94971962320530665573947031 142457943480795998360920547)
        ·
          refine ⟨213686915221193997541380821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142457943480795998360920547 213686915221193997541380821)
          ·
            refine ⟨5008287075496734317376113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 213686915221193997541380821 5008287075496734317376113)
            ·
              refine ⟨3756215306622550738032085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008287075496734317376113 3756215306622550738032085)
              ·
                refine ⟨88036296248966032922627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3756215306622550738032085 88036296248966032922627)
                ·
                  rfl

theorem cell22_2314576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_2314576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314576 prefixEnd_2314576 := by exact prefixLift 2314576
  have htrace : WordTrace (prefixWord ++ tailWord_2314576) baseStart_2314576 baseEnd_2314576 := by
    simpa [prefixWord, tailWord_2314576, baseEnd_2314576] using wordTrace_append hprefix tailTrace_2314576
  have hstable : (prefixWord ++ tailWord_2314576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314576).length < 2 ^ (prefixWord ++ tailWord_2314576).sum := by decide
  have hdescent : baseEnd_2314576 < baseStart_2314576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314580 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2314580 : Nat := 118140960795 + 2314580 * 2 ^ 59
def prefixEnd_2314580 : Nat := 4983230072969 + 3 ^ 40 * 2314580 * 2
def baseEnd_2314580 : Nat := 792328035522439619203631

theorem tailTrace_2314580 : CollatzResearch.WordTrace tailWord_2314580 prefixEnd_2314580 792328035522439619203631 := by
  unfold tailWord_2314580
  simp only [CollatzResearch.WordTrace]
  refine ⟨42209833977339716818882597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56279778636452955758510129 42209833977339716818882597)
  ·
    refine ⟨7914343870751196903540487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42209833977339716818882597 7914343870751196903540487)
    ·
      refine ⟨11871515806126795355310731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7914343870751196903540487 11871515806126795355310731)
      ·
        refine ⟨17807273709190193032966097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11871515806126795355310731 17807273709190193032966097)
        ·
          refine ⟨13355455281892644774724573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17807273709190193032966097 13355455281892644774724573)
          ·
            refine ⟨5008295730709741790521715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13355455281892644774724573 5008295730709741790521715)
            ·
              refine ⟨7512443596064612685782573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008295730709741790521715 7512443596064612685782573)
              ·
                refine ⟨2817166348524229757168465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7512443596064612685782573 2817166348524229757168465)
                ·
                  refine ⟨2112874761393172317876349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817166348524229757168465 2112874761393172317876349)
                  ·
                    refine ⟨792328035522439619203631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112874761393172317876349 792328035522439619203631)
                    ·
                      rfl

theorem cell22_2314580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2314580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314580 prefixEnd_2314580 := by exact prefixLift 2314580
  have htrace : WordTrace (prefixWord ++ tailWord_2314580) baseStart_2314580 baseEnd_2314580 := by
    simpa [prefixWord, tailWord_2314580, baseEnd_2314580] using wordTrace_append hprefix tailTrace_2314580
  have hstable : (prefixWord ++ tailWord_2314580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314580).length < 2 ^ (prefixWord ++ tailWord_2314580).sum := by decide
  have hdescent : baseEnd_2314580 < baseStart_2314580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314614 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_2314614 : Nat := 118140960795 + 2314614 * 2 ^ 59
def prefixEnd_2314614 : Nat := 4983230072969 + 3 ^ 40 * 2314614 * 2
def baseEnd_2314614 : Nat := 792339674417274863853527

theorem tailTrace_2314614 : CollatzResearch.WordTrace tailWord_2314614 prefixEnd_2314614 792339674417274863853527 := by
  unfold tailWord_2314614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276306752284766090281431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56280605357704171629668597 5276306752284766090281431)
  ·
    refine ⟨7914460128427149135422147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5276306752284766090281431 7914460128427149135422147)
    ·
      refine ⟨11871690192640723703133221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7914460128427149135422147 11871690192640723703133221)
      ·
        refine ⟨2225941911120135694337479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11871690192640723703133221 2225941911120135694337479)
        ·
          refine ⟨3338912866680203541506219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225941911120135694337479 3338912866680203541506219)
          ·
            refine ⟨5008369300020305312259329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338912866680203541506219 5008369300020305312259329)
            ·
              refine ⟨3756276975015228984194497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008369300020305312259329 3756276975015228984194497)
              ·
                refine ⟨2817207731261421738145873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756276975015228984194497 2817207731261421738145873)
                ·
                  refine ⟨2112905798446066303609405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817207731261421738145873 2112905798446066303609405)
                  ·
                    refine ⟨792339674417274863853527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112905798446066303609405 792339674417274863853527)
                    ·
                      rfl

theorem cell22_2314614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_2314614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314614 prefixEnd_2314614 := by exact prefixLift 2314614
  have htrace : WordTrace (prefixWord ++ tailWord_2314614) baseStart_2314614 baseEnd_2314614 := by
    simpa [prefixWord, tailWord_2314614, baseEnd_2314614] using wordTrace_append hprefix tailTrace_2314614
  have hstable : (prefixWord ++ tailWord_2314614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314614).length < 2 ^ (prefixWord ++ tailWord_2314614).sum := by decide
  have hdescent : baseEnd_2314614 < baseStart_2314614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314636 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_2314636 : Nat := 118140960795 + 2314636 * 2 ^ 59
def prefixEnd_2314636 : Nat := 4983230072969 + 3 ^ 40 * 2314636 * 2
def baseEnd_2314636 : Nat := 792347205466874139803459

theorem tailTrace_2314636 : CollatzResearch.WordTrace tailWord_2314636 prefixEnd_2314636 792347205466874139803459 := by
  unfold tailWord_2314636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42210855221238277600901881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56281140294984370134535841 42210855221238277600901881)
  ·
    refine ⟨31658141415928708200676411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42210855221238277600901881 31658141415928708200676411)
    ·
      refine ⟨47487212123893062301014617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31658141415928708200676411 47487212123893062301014617)
      ·
        refine ⟨35615409092919796725760963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47487212123893062301014617 35615409092919796725760963)
        ·
          refine ⟨53423113639379695088641445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35615409092919796725760963 53423113639379695088641445)
          ·
            refine ⟨10016833807383692829120271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53423113639379695088641445 10016833807383692829120271)
            ·
              refine ⟨15025250711075539243680407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10016833807383692829120271 15025250711075539243680407)
              ·
                refine ⟨22537876066613308865520611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15025250711075539243680407 22537876066613308865520611)
                ·
                  refine ⟨33806814099919963298280917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22537876066613308865520611 33806814099919963298280917)
                  ·
                    refine ⟨792347205466874139803459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33806814099919963298280917 792347205466874139803459)
                    ·
                      rfl

theorem cell22_2314636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_2314636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314636 prefixEnd_2314636 := by exact prefixLift 2314636
  have htrace : WordTrace (prefixWord ++ tailWord_2314636) baseStart_2314636 baseEnd_2314636 := by
    simpa [prefixWord, tailWord_2314636, baseEnd_2314636] using wordTrace_append hprefix tailTrace_2314636
  have hstable : (prefixWord ++ tailWord_2314636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314636).length < 2 ^ (prefixWord ++ tailWord_2314636).sum := by decide
  have hdescent : baseEnd_2314636 < baseStart_2314636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314646 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2314646 : Nat := 118140960795 + 2314646 * 2 ^ 59
def prefixEnd_2314646 : Nat := 4983230072969 + 3 ^ 40 * 2314646 * 2
def baseEnd_2314646 : Nat := 792350628671237447053429

theorem tailTrace_2314646 : CollatzResearch.WordTrace tailWord_2314646 prefixEnd_2314646 792350628671237447053429 := by
  unfold tailWord_2314646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276379698277520431854237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56281383448293551273111861 5276379698277520431854237)
  ·
    refine ⟨1978642386854070161945339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5276379698277520431854237 1978642386854070161945339)
    ·
      refine ⟨2967963580281105242918009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978642386854070161945339 2967963580281105242918009)
      ·
        refine ⟨2225972685210828932188507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2967963580281105242918009 2225972685210828932188507)
        ·
          refine ⟨3338959027816243398282761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225972685210828932188507 3338959027816243398282761)
          ·
            refine ⟨2504219270862182548712071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3338959027816243398282761 2504219270862182548712071)
            ·
              refine ⟨3756328906293273823068107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504219270862182548712071 3756328906293273823068107)
              ·
                refine ⟨5634493359439910734602161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756328906293273823068107 5634493359439910734602161)
                ·
                  refine ⟨4225870019579933050951621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634493359439910734602161 4225870019579933050951621)
                  ·
                    refine ⟨792350628671237447053429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225870019579933050951621 792350628671237447053429)
                    ·
                      rfl

theorem cell22_2314646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2314646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314646 prefixEnd_2314646 := by exact prefixLift 2314646
  have htrace : WordTrace (prefixWord ++ tailWord_2314646) baseStart_2314646 baseEnd_2314646 := by
    simpa [prefixWord, tailWord_2314646, baseEnd_2314646] using wordTrace_append hprefix tailTrace_2314646
  have hstable : (prefixWord ++ tailWord_2314646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314646).length < 2 ^ (prefixWord ++ tailWord_2314646).sum := by decide
  have hdescent : baseEnd_2314646 < baseStart_2314646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314713 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_2314713 : Nat := 118140960795 + 2314713 * 2 ^ 59
def prefixEnd_2314713 : Nat := 4983230072969 + 3 ^ 40 * 2314713 * 2
def baseEnd_2314713 : Nat := 792373564140471605628223

theorem tailTrace_2314713 : CollatzResearch.WordTrace tailWord_2314713 prefixEnd_2314713 792373564140471605628223 := by
  unfold tailWord_2314713
  simp only [CollatzResearch.WordTrace]
  refine ⟨84424518863197597352356793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56283012575465064901571195 84424518863197597352356793)
  ·
    refine ⟨63318389147398198014267595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84424518863197597352356793 63318389147398198014267595)
    ·
      refine ⟨94977583721097297021401393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63318389147398198014267595 94977583721097297021401393)
      ·
        refine ⟨71233187790822972766051045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94977583721097297021401393 71233187790822972766051045)
        ·
          refine ⟨13356222710779307393634571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71233187790822972766051045 13356222710779307393634571)
          ·
            refine ⟨20034334066168961090451857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13356222710779307393634571 20034334066168961090451857)
            ·
              refine ⟨15025750549626720817838893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20034334066168961090451857 15025750549626720817838893)
              ·
                refine ⟨5634656456110020306689585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15025750549626720817838893 5634656456110020306689585)
                ·
                  refine ⟨4225992342082515230017189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634656456110020306689585 4225992342082515230017189)
                  ·
                    refine ⟨792373564140471605628223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225992342082515230017189 792373564140471605628223)
                    ·
                      rfl

theorem cell22_2314713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_2314713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314713 prefixEnd_2314713 := by exact prefixLift 2314713
  have htrace : WordTrace (prefixWord ++ tailWord_2314713) baseStart_2314713 baseEnd_2314713 := by
    simpa [prefixWord, tailWord_2314713, baseEnd_2314713] using wordTrace_append hprefix tailTrace_2314713
  have hstable : (prefixWord ++ tailWord_2314713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314713).length < 2 ^ (prefixWord ++ tailWord_2314713).sum := by decide
  have hdescent : baseEnd_2314713 < baseStart_2314713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314728 : List Nat := [2, 1, 4, 1, 1, 5, 8]
def baseStart_2314728 : Nat := 118140960795 + 2314728 * 2 ^ 59
def prefixEnd_2314728 : Nat := 4983230072969 + 3 ^ 40 * 2314728 * 2
def baseEnd_2314728 : Nat := 29347359220259872833451

theorem tailTrace_2314728 : CollatzResearch.WordTrace tailWord_2314728 prefixEnd_2314728 29347359220259872833451 := by
  unfold tailWord_2314728
  simp only [CollatzResearch.WordTrace]
  refine ⟨42212532979071627457076419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56283377305428836609435225 42212532979071627457076419)
  ·
    refine ⟨63318799468607441185614629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42212532979071627457076419 63318799468607441185614629)
    ·
      refine ⟨11872274900363895222302743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63318799468607441185614629 11872274900363895222302743)
      ·
        refine ⟨17808412350545842833454115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11872274900363895222302743 17808412350545842833454115)
        ·
          refine ⟨26712618525818764250181173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17808412350545842833454115 26712618525818764250181173)
          ·
            refine ⟨2504307986795509148454485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26712618525818764250181173 2504307986795509148454485)
            ·
              refine ⟨29347359220259872833451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2504307986795509148454485 29347359220259872833451)
              ·
                rfl

theorem cell22_2314728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 8].length) (baseStart_2314728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314728 prefixEnd_2314728 := by exact prefixLift 2314728
  have htrace : WordTrace (prefixWord ++ tailWord_2314728) baseStart_2314728 baseEnd_2314728 := by
    simpa [prefixWord, tailWord_2314728, baseEnd_2314728] using wordTrace_append hprefix tailTrace_2314728
  have hstable : (prefixWord ++ tailWord_2314728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314728).length < 2 ^ (prefixWord ++ tailWord_2314728).sum := by decide
  have hdescent : baseEnd_2314728 < baseStart_2314728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314730 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2314730 : Nat := 118140960795 + 2314730 * 2 ^ 59
def prefixEnd_2314730 : Nat := 4983230072969 + 3 ^ 40 * 2314730 * 2
def baseEnd_2314730 : Nat := 792379383587889227953171

theorem tailTrace_2314730 : CollatzResearch.WordTrace tailWord_2314730 prefixEnd_2314730 792379383587889227953171 := by
  unfold tailWord_2314730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21106284726034002313931411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56283425936090672837150429 21106284726034002313931411)
  ·
    refine ⟨31659427089051003470897117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21106284726034002313931411 31659427089051003470897117)
    ·
      refine ⟨11872285158394126301586419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31659427089051003470897117 11872285158394126301586419)
      ·
        refine ⟨17808427737591189452379629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11872285158394126301586419 17808427737591189452379629)
        ·
          refine ⟨6678160401596696044642361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17808427737591189452379629 6678160401596696044642361)
          ·
            refine ⟨5008620301197522033481771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6678160401596696044642361 5008620301197522033481771)
            ·
              refine ⟨7512930451796283050222657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008620301197522033481771 7512930451796283050222657)
              ·
                refine ⟨5634697838847212287666993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7512930451796283050222657 5634697838847212287666993)
                ·
                  refine ⟨4226023379135409215750245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634697838847212287666993 4226023379135409215750245)
                  ·
                    refine ⟨792379383587889227953171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226023379135409215750245 792379383587889227953171)
                    ·
                      rfl

theorem cell22_2314730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2314730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314730 prefixEnd_2314730 := by exact prefixLift 2314730
  have htrace : WordTrace (prefixWord ++ tailWord_2314730) baseStart_2314730 baseEnd_2314730 := by
    simpa [prefixWord, tailWord_2314730, baseEnd_2314730] using wordTrace_append hprefix tailTrace_2314730
  have hstable : (prefixWord ++ tailWord_2314730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314730).length < 2 ^ (prefixWord ++ tailWord_2314730).sum := by decide
  have hdescent : baseEnd_2314730 < baseStart_2314730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314794 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2314794 : Nat := 118140960795 + 2314794 * 2 ^ 59
def prefixEnd_2314794 : Nat := 4983230072969 + 3 ^ 40 * 2314794 * 2
def baseEnd_2314794 : Nat := 792401292095814394352975

theorem tailTrace_2314794 : CollatzResearch.WordTrace tailWord_2314794 prefixEnd_2314794 792401292095814394352975 := by
  unfold tailWord_2314794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21106868293976037046513859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56284982117269432124036957 21106868293976037046513859)
  ·
    refine ⟨31660302440964055569770789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21106868293976037046513859 31660302440964055569770789)
    ·
      refine ⟨5936306707680760419332023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31660302440964055569770789 5936306707680760419332023)
      ·
        refine ⟨8904460061521140628998035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936306707680760419332023 8904460061521140628998035)
        ·
          refine ⟨13356690092281710943497053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8904460061521140628998035 13356690092281710943497053)
          ·
            refine ⟨5008758784605641603811395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13356690092281710943497053 5008758784605641603811395)
            ·
              refine ⟨7513138176908462405717093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008758784605641603811395 7513138176908462405717093)
              ·
                refine ⟨1408713408170336701071955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7513138176908462405717093 1408713408170336701071955)
                ·
                  refine ⟨2113070112255505051607933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408713408170336701071955 2113070112255505051607933)
                  ·
                    refine ⟨792401292095814394352975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113070112255505051607933 792401292095814394352975)
                    ·
                      rfl

theorem cell22_2314794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2314794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314794 prefixEnd_2314794 := by exact prefixLift 2314794
  have htrace : WordTrace (prefixWord ++ tailWord_2314794) baseStart_2314794 baseEnd_2314794 := by
    simpa [prefixWord, tailWord_2314794, baseEnd_2314794] using wordTrace_append hprefix tailTrace_2314794
  have hstable : (prefixWord ++ tailWord_2314794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314794).length < 2 ^ (prefixWord ++ tailWord_2314794).sum := by decide
  have hdescent : baseEnd_2314794 < baseStart_2314794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314803 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_2314803 : Nat := 118140960795 + 2314803 * 2 ^ 59
def prefixEnd_2314803 : Nat := 4983230072969 + 3 ^ 40 * 2314803 * 2
def baseEnd_2314803 : Nat := 792404372979741370877947

theorem tailTrace_2314803 : CollatzResearch.WordTrace tailWord_2314803 prefixEnd_2314803 792404372979741370877947 := by
  unfold tailWord_2314803
  simp only [CollatzResearch.WordTrace]
  refine ⟨84427801432871542723133063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56285200955247695148755375 84427801432871542723133063)
  ·
    refine ⟨126641702149307314084699595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84427801432871542723133063 126641702149307314084699595)
    ·
      refine ⟨189962553223960971127049393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126641702149307314084699595 189962553223960971127049393)
      ·
        refine ⟨142471914917970728345287045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189962553223960971127049393 142471914917970728345287045)
        ·
          refine ⟨26713484047119511564741321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142471914917970728345287045 26713484047119511564741321)
          ·
            refine ⟨20035113035339633673555991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26713484047119511564741321 20035113035339633673555991)
            ·
              refine ⟨30052669553009450510333987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20035113035339633673555991 30052669553009450510333987)
              ·
                refine ⟨45079004329514175765500981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30052669553009450510333987 45079004329514175765500981)
                ·
                  refine ⟨4226156655891953978015717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45079004329514175765500981 4226156655891953978015717)
                  ·
                    refine ⟨792404372979741370877947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226156655891953978015717 792404372979741370877947)
                    ·
                      rfl

theorem cell22_2314803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_2314803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314803 prefixEnd_2314803 := by exact prefixLift 2314803
  have htrace : WordTrace (prefixWord ++ tailWord_2314803) baseStart_2314803 baseEnd_2314803 := by
    simpa [prefixWord, tailWord_2314803, baseEnd_2314803] using wordTrace_append hprefix tailTrace_2314803
  have hstable : (prefixWord ++ tailWord_2314803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314803).length < 2 ^ (prefixWord ++ tailWord_2314803).sum := by decide
  have hdescent : baseEnd_2314803 < baseStart_2314803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314837 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2314837 : Nat := 118140960795 + 2314837 * 2 ^ 59
def prefixEnd_2314837 : Nat := 4983230072969 + 3 ^ 40 * 2314837 * 2
def baseEnd_2314837 : Nat := 792416011874576615527843

theorem tailTrace_2314837 : CollatzResearch.WordTrace tailWord_2314837 prefixEnd_2314837 792416011874576615527843 := by
  unfold tailWord_2314837
  simp only [CollatzResearch.WordTrace]
  refine ⟨84429041514748366529870765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56286027676498911019913843 84429041514748366529870765)
  ·
    refine ⟨31660890568030637448701537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84429041514748366529870765 31660890568030637448701537)
    ·
      refine ⟨23745667926022978086526153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31660890568030637448701537 23745667926022978086526153)
      ·
        refine ⟨17809250944517233564894615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23745667926022978086526153 17809250944517233564894615)
        ·
          refine ⟨26713876416775850347341923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17809250944517233564894615 26713876416775850347341923)
          ·
            refine ⟨40070814625163775521012885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26713876416775850347341923 40070814625163775521012885)
            ·
              refine ⟨1878319435554551977547479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40070814625163775521012885 1878319435554551977547479)
              ·
                refine ⟨2817479153331827966321219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878319435554551977547479 2817479153331827966321219)
                ·
                  refine ⟨4226218729997741949481829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817479153331827966321219 4226218729997741949481829)
                  ·
                    refine ⟨792416011874576615527843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226218729997741949481829 792416011874576615527843)
                    ·
                      rfl

theorem cell22_2314837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2314837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314837 prefixEnd_2314837 := by exact prefixLift 2314837
  have htrace : WordTrace (prefixWord ++ tailWord_2314837) baseStart_2314837 baseEnd_2314837 := by
    simpa [prefixWord, tailWord_2314837, baseEnd_2314837] using wordTrace_append hprefix tailTrace_2314837
  have hstable : (prefixWord ++ tailWord_2314837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314837).length < 2 ^ (prefixWord ++ tailWord_2314837).sum := by decide
  have hdescent : baseEnd_2314837 < baseStart_2314837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314880 : List Nat := [2, 1, 1, 2, 1, 5, 4, 6]
def baseStart_2314880 : Nat := 118140960795 + 2314880 * 2 ^ 59
def prefixEnd_2314880 : Nat := 4983230072969 + 3 ^ 40 * 2314880 * 2
def baseEnd_2314880 : Nat := 88047859072593204078079

theorem tailTrace_2314880 : CollatzResearch.WordTrace tailWord_2314880 prefixEnd_2314880 88047859072593204078079 := by
  unfold tailWord_2314880
  simp only [CollatzResearch.WordTrace]
  refine ⟨42215304926796292436843047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56287073235728389915790729 42215304926796292436843047)
  ·
    refine ⟨63322957390194438655264571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42215304926796292436843047 63322957390194438655264571)
    ·
      refine ⟨94984436085291657982896857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63322957390194438655264571 94984436085291657982896857)
      ·
        refine ⟨71238327063968743487172643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94984436085291657982896857 71238327063968743487172643)
        ·
          refine ⟨106857490595953115230758965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71238327063968743487172643 106857490595953115230758965)
          ·
            refine ⟨10017889743370604552883653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106857490595953115230758965 10017889743370604552883653)
            ·
              refine ⟨1878354326881988353665685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10017889743370604552883653 1878354326881988353665685)
              ·
                refine ⟨88047859072593204078079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1878354326881988353665685 88047859072593204078079)
                ·
                  rfl

theorem cell22_2314880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_2314880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314880 prefixEnd_2314880 := by exact prefixLift 2314880
  have htrace : WordTrace (prefixWord ++ tailWord_2314880) baseStart_2314880 baseEnd_2314880 := by
    simpa [prefixWord, tailWord_2314880, baseEnd_2314880] using wordTrace_append hprefix tailTrace_2314880
  have hstable : (prefixWord ++ tailWord_2314880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314880).length < 2 ^ (prefixWord ++ tailWord_2314880).sum := by decide
  have hdescent : baseEnd_2314880 < baseStart_2314880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314970 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_2314970 : Nat := 118140960795 + 2314970 * 2 ^ 59
def prefixEnd_2314970 : Nat := 4983230072969 + 3 ^ 40 * 2314970 * 2
def baseEnd_2314970 : Nat := 264153846830869533984145

theorem tailTrace_2314970 : CollatzResearch.WordTrace tailWord_2314970 prefixEnd_2314970 264153846830869533984145 := by
  unfold tailWord_2314970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21108473105816632561115591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56289261615511020162974909 21108473105816632561115591)
  ·
    refine ⟨31662709658724948841673387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21108473105816632561115591 31662709658724948841673387)
    ·
      refine ⟨47494064488087423262510081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31662709658724948841673387 47494064488087423262510081)
      ·
        refine ⟨35620548366065567446882561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47494064488087423262510081 35620548366065567446882561)
        ·
          refine ⟨26715411274549175585161921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35620548366065567446882561 26715411274549175585161921)
          ·
            refine ⟨20036558455911881688871441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26715411274549175585161921 20036558455911881688871441)
            ·
              refine ⟨15027418841933911266653581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20036558455911881688871441 15027418841933911266653581)
              ·
                refine ⟨5635282065725216724995093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15027418841933911266653581 5635282065725216724995093)
                ·
                  refine ⟨264153846830869533984145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5635282065725216724995093 264153846830869533984145)
                  ·
                    rfl

theorem cell22_2314970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_2314970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314970 prefixEnd_2314970 := by exact prefixLift 2314970
  have htrace : WordTrace (prefixWord ++ tailWord_2314970) baseStart_2314970 baseEnd_2314970 := by
    simpa [prefixWord, tailWord_2314970, baseEnd_2314970] using wordTrace_append hprefix tailTrace_2314970
  have hstable : (prefixWord ++ tailWord_2314970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314970).length < 2 ^ (prefixWord ++ tailWord_2314970).sum := by decide
  have hdescent : baseEnd_2314970 < baseStart_2314970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2314985 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_2314985 : Nat := 118140960795 + 2314985 * 2 ^ 59
def prefixEnd_2314985 : Nat := 4983230072969 + 3 ^ 40 * 2314985 * 2
def baseEnd_2314985 : Nat := 792466675299153562827389

theorem tailTrace_2314985 : CollatzResearch.WordTrace tailWord_2314985 prefixEnd_2314985 792466675299153562827389 := by
  unfold tailWord_2314985
  simp only [CollatzResearch.WordTrace]
  refine ⟨84434439518212187806258409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56289626345474791870838939 84434439518212187806258409)
  ·
    refine ⟨63325829638659140854693807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84434439518212187806258409 63325829638659140854693807)
    ·
      refine ⟨94988744457988711282040711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63325829638659140854693807 94988744457988711282040711)
      ·
        refine ⟨142483116686983066923061067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94988744457988711282040711 142483116686983066923061067)
        ·
          refine ⟨213724675030474600384591601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142483116686983066923061067 213724675030474600384591601)
          ·
            refine ⟨160293506272855950288443701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213724675030474600384591601 160293506272855950288443701)
            ·
              refine ⟨15027516213080245339541597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160293506272855950288443701 15027516213080245339541597)
              ·
                refine ⟨5635318579905092002328099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15027516213080245339541597 5635318579905092002328099)
                ·
                  refine ⟨8452977869857638003492149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635318579905092002328099 8452977869857638003492149)
                  ·
                    refine ⟨792466675299153562827389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8452977869857638003492149 792466675299153562827389)
                    ·
                      rfl

theorem cell22_2314985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_2314985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2314985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2314985 prefixEnd_2314985 := by exact prefixLift 2314985
  have htrace : WordTrace (prefixWord ++ tailWord_2314985) baseStart_2314985 baseEnd_2314985 := by
    simpa [prefixWord, tailWord_2314985, baseEnd_2314985] using wordTrace_append hprefix tailTrace_2314985
  have hstable : (prefixWord ++ tailWord_2314985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2314985).length < 2 ^ (prefixWord ++ tailWord_2314985).sum := by decide
  have hdescent : baseEnd_2314985 < baseStart_2314985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2314985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315000 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_2315000 : Nat := 118140960795 + 2315000 * 2 ^ 59
def prefixEnd_2315000 : Nat := 4983230072969 + 3 ^ 40 * 2315000 * 2
def baseEnd_2315000 : Nat := 792471810105698523702343

theorem tailTrace_2315000 : CollatzResearch.WordTrace tailWord_2315000 prefixEnd_2315000 792471810105698523702343 := by
  unfold tailWord_2315000
  simp only [CollatzResearch.WordTrace]
  refine ⟨42217493306578922684027227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56289991075438563578702969 42217493306578922684027227)
  ·
    refine ⟨63326239959868384026040841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42217493306578922684027227 63326239959868384026040841)
    ·
      refine ⟨47494679969901288019530631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63326239959868384026040841 47494679969901288019530631)
      ·
        refine ⟨71242019954851932029295947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47494679969901288019530631 71242019954851932029295947)
        ·
          refine ⟨106863029932277898043943921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71242019954851932029295947 106863029932277898043943921)
          ·
            refine ⟨80147272449208423532957941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106863029932277898043943921 80147272449208423532957941)
            ·
              refine ⟨7513806792113289706214807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80147272449208423532957941 7513806792113289706214807)
              ·
                refine ⟨11270710188169934559322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513806792113289706214807 11270710188169934559322211)
                ·
                  refine ⟨16906065282254901838983317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11270710188169934559322211 16906065282254901838983317)
                  ·
                    refine ⟨792471810105698523702343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16906065282254901838983317 792471810105698523702343)
                    ·
                      rfl

theorem cell22_2315000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_2315000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315000 prefixEnd_2315000 := by exact prefixLift 2315000
  have htrace : WordTrace (prefixWord ++ tailWord_2315000) baseStart_2315000 baseEnd_2315000 := by
    simpa [prefixWord, tailWord_2315000, baseEnd_2315000] using wordTrace_append hprefix tailTrace_2315000
  have hstable : (prefixWord ++ tailWord_2315000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315000).length < 2 ^ (prefixWord ++ tailWord_2315000).sum := by decide
  have hdescent : baseEnd_2315000 < baseStart_2315000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315004 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_2315004 : Nat := 118140960795 + 2315004 * 2 ^ 59
def prefixEnd_2315004 : Nat := 4983230072969 + 3 ^ 40 * 2315004 * 2
def baseEnd_2315004 : Nat := 264157726462481282200777

theorem tailTrace_2315004 : CollatzResearch.WordTrace tailWord_2315004 prefixEnd_2315004 264157726462481282200777 := by
  unfold tailWord_2315004
  simp only [CollatzResearch.WordTrace]
  refine ⟨42217566252571677025600033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56290088336762236034133377 42217566252571677025600033)
  ·
    refine ⟨31663174689428757769200025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42217566252571677025600033 31663174689428757769200025)
    ·
      refine ⟨23747381017071568326900019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31663174689428757769200025 23747381017071568326900019)
      ·
        refine ⟨35621071525607352490350029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23747381017071568326900019 35621071525607352490350029)
        ·
          refine ⟨13357901822102757183881261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35621071525607352490350029 13357901822102757183881261)
          ·
            refine ⟨5009213183288533943955473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13357901822102757183881261 5009213183288533943955473)
            ·
              refine ⟨3756909887466400457966605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5009213183288533943955473 3756909887466400457966605)
              ·
                refine ⟨1408841207799900171737477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3756909887466400457966605 1408841207799900171737477)
                ·
                  refine ⟨264157726462481282200777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408841207799900171737477 264157726462481282200777)
                  ·
                    rfl

theorem cell22_2315004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_2315004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315004 prefixEnd_2315004 := by exact prefixLift 2315004
  have htrace : WordTrace (prefixWord ++ tailWord_2315004) baseStart_2315004 baseEnd_2315004 := by
    simpa [prefixWord, tailWord_2315004, baseEnd_2315004] using wordTrace_append hprefix tailTrace_2315004
  have hstable : (prefixWord ++ tailWord_2315004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315004).length < 2 ^ (prefixWord ++ tailWord_2315004).sum := by decide
  have hdescent : baseEnd_2315004 < baseStart_2315004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315006 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2315006 : Nat := 118140960795 + 2315006 * 2 ^ 59
def prefixEnd_2315006 : Nat := 4983230072969 + 3 ^ 40 * 2315006 * 2
def baseEnd_2315006 : Nat := 792473864028316508052325

theorem tailTrace_2315006 : CollatzResearch.WordTrace tailWord_2315006 prefixEnd_2315006 792473864028316508052325 := by
  unfold tailWord_2315006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554400681392013549096609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56290136967424072261848581 10554400681392013549096609)
  ·
    refine ⟨7915800511044010161822457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10554400681392013549096609 7915800511044010161822457)
    ·
      refine ⟨5936850383283007621366843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7915800511044010161822457 5936850383283007621366843)
      ·
        refine ⟨8905275574924511432050265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936850383283007621366843 8905275574924511432050265)
        ·
          refine ⟨6678956681193383574037699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8905275574924511432050265 6678956681193383574037699)
          ·
            refine ⟨10018435021790075361056549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678956681193383574037699 10018435021790075361056549)
            ·
              refine ⟨1878456566585639130198103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10018435021790075361056549 1878456566585639130198103)
              ·
                refine ⟨2817684849878458695297155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878456566585639130198103 2817684849878458695297155)
                ·
                  refine ⟨4226527274817688042945733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817684849878458695297155 4226527274817688042945733)
                  ·
                    refine ⟨792473864028316508052325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226527274817688042945733 792473864028316508052325)
                    ·
                      rfl

theorem cell22_2315006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2315006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315006 prefixEnd_2315006 := by exact prefixLift 2315006
  have htrace : WordTrace (prefixWord ++ tailWord_2315006) baseStart_2315006 baseEnd_2315006 := by
    simpa [prefixWord, tailWord_2315006, baseEnd_2315006] using wordTrace_append hprefix tailTrace_2315006
  have hstable : (prefixWord ++ tailWord_2315006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315006).length < 2 ^ (prefixWord ++ tailWord_2315006).sum := by decide
  have hdescent : baseEnd_2315006 < baseStart_2315006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315036 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2315036 : Nat := 118140960795 + 2315036 * 2 ^ 59
def prefixEnd_2315036 : Nat := 4983230072969 + 3 ^ 40 * 2315036 * 2
def baseEnd_2315036 : Nat := 792484133641406429802233

theorem tailTrace_2315036 : CollatzResearch.WordTrace tailWord_2315036 prefixEnd_2315036 792484133641406429802233 := by
  unfold tailWord_2315036
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218149820513711758182481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56290866427351615677576641 42218149820513711758182481)
  ·
    refine ⟨31663612365385283818636861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42218149820513711758182481 31663612365385283818636861)
    ·
      refine ⟨11873854637019481431988823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31663612365385283818636861 11873854637019481431988823)
      ·
        refine ⟨17810781955529222147983235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11873854637019481431988823 17810781955529222147983235)
        ·
          refine ⟨26716172933293833221974853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17810781955529222147983235 26716172933293833221974853)
          ·
            refine ⟨5009282424992593729120285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26716172933293833221974853 5009282424992593729120285)
            ·
              refine ⟨1878480909372222648420107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5009282424992593729120285 1878480909372222648420107)
              ·
                refine ⟨2817721364058333972630161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878480909372222648420107 2817721364058333972630161)
                ·
                  refine ⟨2113291023043750479472621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817721364058333972630161 2113291023043750479472621)
                  ·
                    refine ⟨792484133641406429802233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113291023043750479472621 792484133641406429802233)
                    ·
                      rfl

theorem cell22_2315036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2315036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315036 prefixEnd_2315036 := by exact prefixLift 2315036
  have htrace : WordTrace (prefixWord ++ tailWord_2315036) baseStart_2315036 baseEnd_2315036 := by
    simpa [prefixWord, tailWord_2315036, baseEnd_2315036] using wordTrace_append hprefix tailTrace_2315036
  have hstable : (prefixWord ++ tailWord_2315036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315036).length < 2 ^ (prefixWord ++ tailWord_2315036).sum := by decide
  have hdescent : baseEnd_2315036 < baseStart_2315036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315139 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 4]
def baseStart_2315139 : Nat := 118140960795 + 2315139 * 2 ^ 59
def prefixEnd_2315139 : Nat := 4983230072969 + 3 ^ 40 * 2315139 * 2
def baseEnd_2315139 : Nat := 264173130882116164825639

theorem tailTrace_2315139 : CollatzResearch.WordTrace tailWord_2315139 prefixEnd_2315139 264173130882116164825639 := by
  unfold tailWord_2315139
  simp only [CollatzResearch.WordTrace]
  refine ⟨84440056359654272107364471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56293370906436181404909647 84440056359654272107364471)
  ·
    refine ⟨126660084539481408161046707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84440056359654272107364471 126660084539481408161046707)
    ·
      refine ⟨189990126809222112241570061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126660084539481408161046707 189990126809222112241570061)
      ·
        refine ⟨71246297553458292090588773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189990126809222112241570061 71246297553458292090588773)
        ·
          refine ⟨13358680791273429766985395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71246297553458292090588773 13358680791273429766985395)
          ·
            refine ⟨20038021186910144650478093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13358680791273429766985395 20038021186910144650478093)
            ·
              refine ⟨7514257945091304243929285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20038021186910144650478093 7514257945091304243929285)
              ·
                refine ⟨1408923364704619545736741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7514257945091304243929285 1408923364704619545736741)
                ·
                  refine ⟨264173130882116164825639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1408923364704619545736741 264173130882116164825639)
                  ·
                    rfl

theorem cell22_2315139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 4].length) (baseStart_2315139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315139 prefixEnd_2315139 := by exact prefixLift 2315139
  have htrace : WordTrace (prefixWord ++ tailWord_2315139) baseStart_2315139 baseEnd_2315139 := by
    simpa [prefixWord, tailWord_2315139, baseEnd_2315139] using wordTrace_append hprefix tailTrace_2315139
  have hstable : (prefixWord ++ tailWord_2315139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315139).length < 2 ^ (prefixWord ++ tailWord_2315139).sum := by decide
  have hdescent : baseEnd_2315139 < baseStart_2315139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315158 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2315158 : Nat := 118140960795 + 2315158 * 2 ^ 59
def prefixEnd_2315158 : Nat := 4983230072969 + 3 ^ 40 * 2315158 * 2
def baseEnd_2315158 : Nat := 792525896734638778251859

theorem tailTrace_2315158 : CollatzResearch.WordTrace tailWord_2315158 prefixEnd_2315158 792525896734638778251859 := by
  unfold tailWord_2315158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277546834161589897019133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56293832897723625568204085 5277546834161589897019133)
  ·
    refine ⟨1979080062810596211382175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5277546834161589897019133 1979080062810596211382175)
    ·
      refine ⟨2968620094215894317073263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1979080062810596211382175 2968620094215894317073263)
      ·
        refine ⟨4452930141323841475609895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968620094215894317073263 4452930141323841475609895)
        ·
          refine ⟨6679395211985762213414843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452930141323841475609895 6679395211985762213414843)
          ·
            refine ⟨10019092817978643320122265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6679395211985762213414843 10019092817978643320122265)
            ·
              refine ⟨7514319613483982490091699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10019092817978643320122265 7514319613483982490091699)
              ·
                refine ⟨11271479420225973735137549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7514319613483982490091699 11271479420225973735137549)
                ·
                  refine ⟨4226804782584740150676581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11271479420225973735137549 4226804782584740150676581)
                  ·
                    refine ⟨792525896734638778251859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226804782584740150676581 792525896734638778251859)
                    ·
                      rfl

theorem cell22_2315158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2315158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315158 prefixEnd_2315158 := by exact prefixLift 2315158
  have htrace : WordTrace (prefixWord ++ tailWord_2315158) baseStart_2315158 baseEnd_2315158 := by
    simpa [prefixWord, tailWord_2315158, baseEnd_2315158] using wordTrace_append hprefix tailTrace_2315158
  have hstable : (prefixWord ++ tailWord_2315158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315158).length < 2 ^ (prefixWord ++ tailWord_2315158).sum := by decide
  have hdescent : baseEnd_2315158 < baseStart_2315158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315169 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2315169 : Nat := 118140960795 + 2315169 * 2 ^ 59
def prefixEnd_2315169 : Nat := 4983230072969 + 3 ^ 40 * 2315169 * 2
def baseEnd_2315169 : Nat := 792529662259438416226825

theorem tailTrace_2315169 : CollatzResearch.WordTrace tailWord_2315169 prefixEnd_2315169 792529662259438416226825 := by
  unfold tailWord_2315169
  simp only [CollatzResearch.WordTrace]
  refine ⟨84441150549545587230956561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56294100366363724820637707 84441150549545587230956561)
  ·
    refine ⟨63330862912159190423217421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84441150549545587230956561 63330862912159190423217421)
    ·
      refine ⟨23749073592059696408706533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63330862912159190423217421 23749073592059696408706533)
      ·
        refine ⟨4452951298511193076632475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23749073592059696408706533 4452951298511193076632475)
        ·
          refine ⟨6679426947766789614948713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452951298511193076632475 6679426947766789614948713)
          ·
            refine ⟨5009570210825092211211535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679426947766789614948713 5009570210825092211211535)
            ·
              refine ⟨7514355316237638316817303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009570210825092211211535 7514355316237638316817303)
              ·
                refine ⟨11271532974356457475225955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7514355316237638316817303 11271532974356457475225955)
                ·
                  refine ⟨16907299461534686212838933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11271532974356457475225955 16907299461534686212838933)
                  ·
                    refine ⟨792529662259438416226825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16907299461534686212838933 792529662259438416226825)
                    ·
                      rfl

theorem cell22_2315169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2315169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315169 prefixEnd_2315169 := by exact prefixLift 2315169
  have htrace : WordTrace (prefixWord ++ tailWord_2315169) baseStart_2315169 baseEnd_2315169 := by
    simpa [prefixWord, tailWord_2315169, baseEnd_2315169] using wordTrace_append hprefix tailTrace_2315169
  have hstable : (prefixWord ++ tailWord_2315169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315169).length < 2 ^ (prefixWord ++ tailWord_2315169).sum := by decide
  have hdescent : baseEnd_2315169 < baseStart_2315169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315175 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2315175 : Nat := 118140960795 + 2315175 * 2 ^ 59
def prefixEnd_2315175 : Nat := 4983230072969 + 3 ^ 40 * 2315175 * 2
def baseEnd_2315175 : Nat := 792531716182056400576807

theorem tailTrace_2315175 : CollatzResearch.WordTrace tailWord_2315175 prefixEnd_2315175 792531716182056400576807 := by
  unfold tailWord_2315175
  simp only [CollatzResearch.WordTrace]
  refine ⟨84441369387523850255674979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56294246258349233503783319 84441369387523850255674979)
  ·
    refine ⟨126662054081285775383512469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84441369387523850255674979 126662054081285775383512469)
    ·
      refine ⟨5937283785060270721102147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126662054081285775383512469 5937283785060270721102147)
      ·
        refine ⟨8905925677590406081653221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937283785060270721102147 8905925677590406081653221)
        ·
          refine ⟨1669861064548201140309979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8905925677590406081653221 1669861064548201140309979)
          ·
            refine ⟨2504791596822301710464969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669861064548201140309979 2504791596822301710464969)
            ·
              refine ⟨1878593697616726282848727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504791596822301710464969 1878593697616726282848727)
              ·
                refine ⟨2817890546425089424273091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878593697616726282848727 2817890546425089424273091)
                ·
                  refine ⟨4226835819637634136409637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817890546425089424273091 4226835819637634136409637)
                  ·
                    refine ⟨792531716182056400576807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226835819637634136409637 792531716182056400576807)
                    ·
                      rfl

theorem cell22_2315175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2315175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315175 prefixEnd_2315175 := by exact prefixLift 2315175
  have htrace : WordTrace (prefixWord ++ tailWord_2315175) baseStart_2315175 baseEnd_2315175 := by
    simpa [prefixWord, tailWord_2315175, baseEnd_2315175] using wordTrace_append hprefix tailTrace_2315175
  have hstable : (prefixWord ++ tailWord_2315175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315175).length < 2 ^ (prefixWord ++ tailWord_2315175).sum := by decide
  have hdescent : baseEnd_2315175 < baseStart_2315175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315188 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2315188 : Nat := 118140960795 + 2315188 * 2 ^ 59
def prefixEnd_2315188 : Nat := 4983230072969 + 3 ^ 40 * 2315188 * 2
def baseEnd_2315188 : Nat := 792536166347728700001767

theorem tailTrace_2315188 : CollatzResearch.WordTrace tailWord_2315188 prefixEnd_2315188 792536166347728700001767 := by
  unfold tailWord_2315188
  simp only [CollatzResearch.WordTrace]
  refine ⟨42220921768238376737949109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56294562357651168983932145 42220921768238376737949109)
  ·
    refine ⟨3958211415772347819182729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42220921768238376737949109 3958211415772347819182729)
    ·
      refine ⟨2968658561829260864387047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3958211415772347819182729 2968658561829260864387047)
      ·
        refine ⟨4452987842743891296580571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968658561829260864387047 4452987842743891296580571)
        ·
          refine ⟨6679481764115836944870857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452987842743891296580571 6679481764115836944870857)
          ·
            refine ⟨5009611323086877708653143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679481764115836944870857 5009611323086877708653143)
            ·
              refine ⟨7514416984630316562979715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009611323086877708653143 7514416984630316562979715)
              ·
                refine ⟨11271625476945474844469573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7514416984630316562979715 11271625476945474844469573)
                ·
                  refine ⟨2113429776927276533338045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11271625476945474844469573 2113429776927276533338045)
                  ·
                    refine ⟨792536166347728700001767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113429776927276533338045 792536166347728700001767)
                    ·
                      rfl

theorem cell22_2315188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2315188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315188 prefixEnd_2315188 := by exact prefixLift 2315188
  have htrace : WordTrace (prefixWord ++ tailWord_2315188) baseStart_2315188 baseEnd_2315188 := by
    simpa [prefixWord, tailWord_2315188, baseEnd_2315188] using wordTrace_append hprefix tailTrace_2315188
  have hstable : (prefixWord ++ tailWord_2315188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315188).length < 2 ^ (prefixWord ++ tailWord_2315188).sum := by decide
  have hdescent : baseEnd_2315188 < baseStart_2315188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315190 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_2315190 : Nat := 118140960795 + 2315190 * 2 ^ 59
def prefixEnd_2315190 : Nat := 4983230072969 + 3 ^ 40 * 2315190 * 2
def baseEnd_2315190 : Nat := 264178950329533787150587

theorem tailTrace_2315190 : CollatzResearch.WordTrace tailWord_2315190 prefixEnd_2315190 264178950329533787150587 := by
  unfold tailWord_2315190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277619780154344238591939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56294610988313005211647349 5277619780154344238591939)
  ·
    refine ⟨7916429670231516357887909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5277619780154344238591939 7916429670231516357887909)
    ·
      refine ⟨1484330563168409317103983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7916429670231516357887909 1484330563168409317103983)
      ·
        refine ⟨2226495844752613975655975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484330563168409317103983 2226495844752613975655975)
        ·
          refine ⟨3339743767128920963483963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226495844752613975655975 3339743767128920963483963)
          ·
            refine ⟨5009615650693381445225945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339743767128920963483963 5009615650693381445225945)
            ·
              refine ⟨3757211738020036083919459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5009615650693381445225945 3757211738020036083919459)
              ·
                refine ⟨5635817607030054125879189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757211738020036083919459 5635817607030054125879189)
                ·
                  refine ⟨264178950329533787150587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5635817607030054125879189 264178950329533787150587)
                  ·
                    rfl

theorem cell22_2315190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_2315190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315190 prefixEnd_2315190 := by exact prefixLift 2315190
  have htrace : WordTrace (prefixWord ++ tailWord_2315190) baseStart_2315190 baseEnd_2315190 := by
    simpa [prefixWord, tailWord_2315190, baseEnd_2315190] using wordTrace_append hprefix tailTrace_2315190
  have hstable : (prefixWord ++ tailWord_2315190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315190).length < 2 ^ (prefixWord ++ tailWord_2315190).sum := by decide
  have hdescent : baseEnd_2315190 < baseStart_2315190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315229 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 7]
def baseStart_2315229 : Nat := 118140960795 + 2315229 * 2 ^ 59
def prefixEnd_2315229 : Nat := 4983230072969 + 3 ^ 40 * 2315229 * 2
def baseEnd_2315229 : Nat := 264183400495206086575547

theorem tailTrace_2315229 : CollatzResearch.WordTrace tailWord_2315229 prefixEnd_2315229 264183400495206086575547 := by
  unfold tailWord_2315229
  simp only [CollatzResearch.WordTrace]
  refine ⟨84443338929328217478140741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56295559286218811652093827 84443338929328217478140741)
  ·
    refine ⟨15833126049249040777151389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84443338929328217478140741 15833126049249040777151389)
    ·
      refine ⟨5937422268468390291431771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15833126049249040777151389 5937422268468390291431771)
      ·
        refine ⟨8906133402702585437147657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937422268468390291431771 8906133402702585437147657)
        ·
          refine ⟨6679600052026939077860743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8906133402702585437147657 6679600052026939077860743)
          ·
            refine ⟨10019400078040408616791115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6679600052026939077860743 10019400078040408616791115)
            ·
              refine ⟨15029100117060612925186673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10019400078040408616791115 15029100117060612925186673)
              ·
                refine ⟨11271825087795459693890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15029100117060612925186673 11271825087795459693890005)
                ·
                  refine ⟨264183400495206086575547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11271825087795459693890005 264183400495206086575547)
                  ·
                    rfl

theorem cell22_2315229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_2315229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315229 prefixEnd_2315229 := by exact prefixLift 2315229
  have htrace : WordTrace (prefixWord ++ tailWord_2315229) baseStart_2315229 baseEnd_2315229 := by
    simpa [prefixWord, tailWord_2315229, baseEnd_2315229] using wordTrace_append hprefix tailTrace_2315229
  have hstable : (prefixWord ++ tailWord_2315229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315229).length < 2 ^ (prefixWord ++ tailWord_2315229).sum := by decide
  have hdescent : baseEnd_2315229 < baseStart_2315229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315250 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_2315250 : Nat := 118140960795 + 2315250 * 2 ^ 59
def prefixEnd_2315250 : Nat := 4983230072969 + 3 ^ 40 * 2315250 * 2
def baseEnd_2315250 : Nat := 792557390214781204951577

theorem tailTrace_2315250 : CollatzResearch.WordTrace tailWord_2315250 prefixEnd_2315250 792557390214781204951577 := by
  unfold tailWord_2315250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111026215563034516163801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56296069908168092043103469 21111026215563034516163801)
  ·
    refine ⟨15833269661672275887122851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21111026215563034516163801 15833269661672275887122851)
    ·
      refine ⟨23749904492508413830684277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15833269661672275887122851 23749904492508413830684277)
      ·
        refine ⟨2226553546172663796626651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23749904492508413830684277 2226553546172663796626651)
        ·
          refine ⟨3339830319258995694939977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226553546172663796626651 3339830319258995694939977)
          ·
            refine ⟨2504872739444246771204983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3339830319258995694939977 2504872739444246771204983)
            ·
              refine ⟨3757309109166370156807475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504872739444246771204983 3757309109166370156807475)
              ·
                refine ⟨5635963663749555235211213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757309109166370156807475 5635963663749555235211213)
                ·
                  refine ⟨2113486373906083213204205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5635963663749555235211213 2113486373906083213204205)
                  ·
                    refine ⟨792557390214781204951577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113486373906083213204205 792557390214781204951577)
                    ·
                      rfl

theorem cell22_2315250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_2315250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315250 prefixEnd_2315250 := by exact prefixLift 2315250
  have htrace : WordTrace (prefixWord ++ tailWord_2315250) baseStart_2315250 baseEnd_2315250 := by
    simpa [prefixWord, tailWord_2315250, baseEnd_2315250] using wordTrace_append hprefix tailTrace_2315250
  have hstable : (prefixWord ++ tailWord_2315250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315250).length < 2 ^ (prefixWord ++ tailWord_2315250).sum := by decide
  have hdescent : baseEnd_2315250 < baseStart_2315250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315276 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_2315276 : Nat := 118140960795 + 2315276 * 2 ^ 59
def prefixEnd_2315276 : Nat := 4983230072969 + 3 ^ 40 * 2315276 * 2
def baseEnd_2315276 : Nat := 792566290546125803801497

theorem tailTrace_2315276 : CollatzResearch.WordTrace tailWord_2315276 prefixEnd_2315276 792566290546125803801497 := by
  unfold tailWord_2315276
  simp only [CollatzResearch.WordTrace]
  refine ⟨42222526580078972252550841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56296702106771963003401121 42222526580078972252550841)
  ·
    refine ⟨31666894935059229189413131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42222526580078972252550841 31666894935059229189413131)
    ·
      refine ⟨47500342402588843784119697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31666894935059229189413131 47500342402588843784119697)
      ·
        refine ⟨35625256801941632838089773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47500342402588843784119697 35625256801941632838089773)
        ·
          refine ⟨13359471300728112314283665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35625256801941632838089773 13359471300728112314283665)
          ·
            refine ⟨10019603475546084235712749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13359471300728112314283665 10019603475546084235712749)
            ·
              refine ⟨3757351303329781588392281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10019603475546084235712749 3757351303329781588392281)
              ·
                refine ⟨2818013477497336191294211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757351303329781588392281 2818013477497336191294211)
                ·
                  refine ⟨4227020216246004286941317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818013477497336191294211 4227020216246004286941317)
                  ·
                    refine ⟨792566290546125803801497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227020216246004286941317 792566290546125803801497)
                    ·
                      rfl

theorem cell22_2315276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_2315276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315276 prefixEnd_2315276 := by exact prefixLift 2315276
  have htrace : WordTrace (prefixWord ++ tailWord_2315276) baseStart_2315276 baseEnd_2315276 := by
    simpa [prefixWord, tailWord_2315276, baseEnd_2315276] using wordTrace_append hprefix tailTrace_2315276
  have hstable : (prefixWord ++ tailWord_2315276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315276).length < 2 ^ (prefixWord ++ tailWord_2315276).sum := by decide
  have hdescent : baseEnd_2315276 < baseStart_2315276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315289 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_2315289 : Nat := 118140960795 + 2315289 * 2 ^ 59
def prefixEnd_2315289 : Nat := 4983230072969 + 3 ^ 40 * 2315289 * 2
def baseEnd_2315289 : Nat := 792570740711798103226457

theorem tailTrace_2315289 : CollatzResearch.WordTrace tailWord_2315289 prefixEnd_2315289 792570740711798103226457 := by
  unfold tailWord_2315289
  simp only [CollatzResearch.WordTrace]
  refine ⟨84445527309110847725324921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56297018206073898483549947 84445527309110847725324921)
  ·
    refine ⟨63334145481833135793993691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84445527309110847725324921 63334145481833135793993691)
    ·
      refine ⟨95001218222749703690990537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63334145481833135793993691 95001218222749703690990537)
      ·
        refine ⟨71250913667062277768242903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95001218222749703690990537 71250913667062277768242903)
        ·
          refine ⟨106876370500593416652364355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71250913667062277768242903 106876370500593416652364355)
          ·
            refine ⟨160314555750890124978546533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106876370500593416652364355 160314555750890124978546533)
            ·
              refine ⟨30058979203291898433477475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160314555750890124978546533 30058979203291898433477475)
              ·
                refine ⟨45088468804937847650216213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30058979203291898433477475 45088468804937847650216213)
                ·
                  refine ⟨2113521975231461608603885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45088468804937847650216213 2113521975231461608603885)
                  ·
                    refine ⟨792570740711798103226457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113521975231461608603885 792570740711798103226457)
                    ·
                      rfl

theorem cell22_2315289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_2315289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315289 prefixEnd_2315289 := by exact prefixLift 2315289
  have htrace : WordTrace (prefixWord ++ tailWord_2315289) baseStart_2315289 baseEnd_2315289 := by
    simpa [prefixWord, tailWord_2315289, baseEnd_2315289] using wordTrace_append hprefix tailTrace_2315289
  have hstable : (prefixWord ++ tailWord_2315289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315289).length < 2 ^ (prefixWord ++ tailWord_2315289).sum := by decide
  have hdescent : baseEnd_2315289 < baseStart_2315289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315357 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2315357 : Nat := 118140960795 + 2315357 * 2 ^ 59
def prefixEnd_2315357 : Nat := 4983230072969 + 3 ^ 40 * 2315357 * 2
def baseEnd_2315357 : Nat := 792594018501468592526249

theorem tailTrace_2315357 : CollatzResearch.WordTrace tailWord_2315357 prefixEnd_2315357 792594018501468592526249 := by
  unfold tailWord_2315357
  simp only [CollatzResearch.WordTrace]
  refine ⟨84448007472864495338800325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56298671648576330225866883 84448007472864495338800325)
  ·
    refine ⟨15834001401162092876025061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84448007472864495338800325 15834001401162092876025061)
    ·
      refine ⟨2968875262717892414254699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15834001401162092876025061 2968875262717892414254699)
      ·
        refine ⟨4453312894076838621382049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2968875262717892414254699 4453312894076838621382049)
        ·
          refine ⟨3339984670557628966036537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4453312894076838621382049 3339984670557628966036537)
          ·
            refine ⟨2504988502918221724527403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3339984670557628966036537 2504988502918221724527403)
            ·
              refine ⟨3757482754377332586791105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504988502918221724527403 3757482754377332586791105)
              ·
                refine ⟨2818112065782999440093329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757482754377332586791105 2818112065782999440093329)
                ·
                  refine ⟨2113584049337249580069997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2818112065782999440093329 2113584049337249580069997)
                  ·
                    refine ⟨792594018501468592526249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113584049337249580069997 792594018501468592526249)
                    ·
                      rfl

theorem cell22_2315357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2315357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315357 prefixEnd_2315357 := by exact prefixLift 2315357
  have htrace : WordTrace (prefixWord ++ tailWord_2315357) baseStart_2315357 baseEnd_2315357 := by
    simpa [prefixWord, tailWord_2315357, baseEnd_2315357] using wordTrace_append hprefix tailTrace_2315357
  have hstable : (prefixWord ++ tailWord_2315357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315357).length < 2 ^ (prefixWord ++ tailWord_2315357).sum := by decide
  have hdescent : baseEnd_2315357 < baseStart_2315357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315411 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 1, 4]
def baseStart_2315411 : Nat := 118140960795 + 2315411 * 2 ^ 59
def prefixEnd_2315411 : Nat := 4983230072969 + 3 ^ 40 * 2315411 * 2
def baseEnd_2315411 : Nat := 792612503805030451676083

theorem tailTrace_2315411 : CollatzResearch.WordTrace tailWord_2315411 prefixEnd_2315411 792612503805030451676083 := by
  unfold tailWord_2315411
  simp only [CollatzResearch.WordTrace]
  refine ⟨84449977014668862561266087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56299984676445908374177391 84449977014668862561266087)
  ·
    refine ⟨126674965522003293841899131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84449977014668862561266087 126674965522003293841899131)
    ·
      refine ⟨190012448283004940762848697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126674965522003293841899131 190012448283004940762848697)
      ·
        refine ⟨142509336212253705572136523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190012448283004940762848697 142509336212253705572136523)
        ·
          refine ⟨213764004318380558358204785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142509336212253705572136523 213764004318380558358204785)
          ·
            refine ⟨160323003238785418768653589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213764004318380558358204785 160323003238785418768653589)
            ·
              refine ⟨7515140776818066504780637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160323003238785418768653589 7515140776818066504780637)
              ·
                refine ⟨2818177791306774939292739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7515140776818066504780637 2818177791306774939292739)
                ·
                  refine ⟨4227266686960162408939109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818177791306774939292739 4227266686960162408939109)
                  ·
                    refine ⟨792612503805030451676083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227266686960162408939109 792612503805030451676083)
                    ·
                      rfl

theorem cell22_2315411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4].length) (baseStart_2315411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315411 prefixEnd_2315411 := by exact prefixLift 2315411
  have htrace : WordTrace (prefixWord ++ tailWord_2315411) baseStart_2315411 baseEnd_2315411 := by
    simpa [prefixWord, tailWord_2315411, baseEnd_2315411] using wordTrace_append hprefix tailTrace_2315411
  have hstable : (prefixWord ++ tailWord_2315411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315411).length < 2 ^ (prefixWord ++ tailWord_2315411).sum := by decide
  have hdescent : baseEnd_2315411 < baseStart_2315411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315439 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_2315439 : Nat := 118140960795 + 2315439 * 2 ^ 59
def prefixEnd_2315439 : Nat := 4983230072969 + 3 ^ 40 * 2315439 * 2
def baseEnd_2315439 : Nat := 792622088777247711975997

theorem tailTrace_2315439 : CollatzResearch.WordTrace tailWord_2315439 prefixEnd_2315439 792622088777247711975997 := by
  unfold tailWord_2315439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84450998258567423343285371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56300665505711615562190247 84450998258567423343285371)
  ·
    refine ⟨126676497387851135014928057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84450998258567423343285371 126676497387851135014928057)
    ·
      refine ⟨95007373040888351261196043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126676497387851135014928057 95007373040888351261196043)
      ·
        refine ⟨142511059561332526891794065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95007373040888351261196043 142511059561332526891794065)
        ·
          refine ⟨106883294670999395168845549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142511059561332526891794065 106883294670999395168845549)
          ·
            refine ⟨40081235501624773188317081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106883294670999395168845549 40081235501624773188317081)
            ·
              refine ⟨30060926626218579891237811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40081235501624773188317081 30060926626218579891237811)
              ·
                refine ⟨45091389939327869836856717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30060926626218579891237811 45091389939327869836856717)
                ·
                  refine ⟨16909271227247951188821269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45091389939327869836856717 16909271227247951188821269)
                  ·
                    refine ⟨792622088777247711975997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16909271227247951188821269 792622088777247711975997)
                    ·
                      rfl

theorem cell22_2315439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_2315439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315439 prefixEnd_2315439 := by exact prefixLift 2315439
  have htrace : WordTrace (prefixWord ++ tailWord_2315439) baseStart_2315439 baseEnd_2315439 := by
    simpa [prefixWord, tailWord_2315439, baseEnd_2315439] using wordTrace_append hprefix tailTrace_2315439
  have hstable : (prefixWord ++ tailWord_2315439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315439).length < 2 ^ (prefixWord ++ tailWord_2315439).sum := by decide
  have hdescent : baseEnd_2315439 < baseStart_2315439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315477 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 4]
def baseStart_2315477 : Nat := 118140960795 + 2315477 * 2 ^ 59
def prefixEnd_2315477 : Nat := 4983230072969 + 3 ^ 40 * 2315477 * 2
def baseEnd_2315477 : Nat := 264211698984609426508627

theorem tailTrace_2315477 : CollatzResearch.WordTrace tailWord_2315477 prefixEnd_2315477 264211698984609426508627 := by
  unfold tailWord_2315477
  simp only [CollatzResearch.WordTrace]
  refine ⟨84452384232429755833168685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56301589488286503888779123 84452384232429755833168685)
  ·
    refine ⟨31669644087161158437438257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84452384232429755833168685 31669644087161158437438257)
    ·
      refine ⟨23752233065370868828078693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31669644087161158437438257 23752233065370868828078693)
      ·
        refine ⟨4453543699757037905264755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23752233065370868828078693 4453543699757037905264755)
        ·
          refine ⟨6680315549635556857897133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453543699757037905264755 6680315549635556857897133)
          ·
            refine ⟨2505118331113333821711425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6680315549635556857897133 2505118331113333821711425)
            ·
              refine ⟨1878838748335000366283569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505118331113333821711425 1878838748335000366283569)
              ·
                refine ⟨1409129061251250274712677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878838748335000366283569 1409129061251250274712677)
                ·
                  refine ⟨264211698984609426508627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409129061251250274712677 264211698984609426508627)
                  ·
                    rfl

theorem cell22_2315477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_2315477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315477 prefixEnd_2315477 := by exact prefixLift 2315477
  have htrace : WordTrace (prefixWord ++ tailWord_2315477) baseStart_2315477 baseEnd_2315477 := by
    simpa [prefixWord, tailWord_2315477, baseEnd_2315477] using wordTrace_append hprefix tailTrace_2315477
  have hstable : (prefixWord ++ tailWord_2315477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315477).length < 2 ^ (prefixWord ++ tailWord_2315477).sum := by decide
  have hdescent : baseEnd_2315477 < baseStart_2315477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315531 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_2315531 : Nat := 118140960795 + 2315531 * 2 ^ 59
def prefixEnd_2315531 : Nat := 4983230072969 + 3 ^ 40 * 2315531 * 2
def baseEnd_2315531 : Nat := 792653582257390138675715

theorem tailTrace_2315531 : CollatzResearch.WordTrace tailWord_2315531 prefixEnd_2315531 792653582257390138675715 := by
  unfold tailWord_2315531
  simp only [CollatzResearch.WordTrace]
  refine ⟨84454353774234123055634447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56302902516156082037089631 84454353774234123055634447)
  ·
    refine ⟨126681530661351184583451671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84454353774234123055634447 126681530661351184583451671)
    ·
      refine ⟨190022295992026776875177507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126681530661351184583451671 190022295992026776875177507)
      ·
        refine ⟨285033443988040165312766261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190022295992026776875177507 285033443988040165312766261)
        ·
          refine ⟨26721885373878765498071837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285033443988040165312766261 26721885373878765498071837)
          ·
            refine ⟨10020707015204537061776939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26721885373878765498071837 10020707015204537061776939)
            ·
              refine ⟨15031060522806805592665409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10020707015204537061776939 15031060522806805592665409)
              ·
                refine ⟨11273295392105104194499057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15031060522806805592665409 11273295392105104194499057)
                ·
                  refine ⟨8454971544078828145874293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11273295392105104194499057 8454971544078828145874293)
                  ·
                    refine ⟨792653582257390138675715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8454971544078828145874293 792653582257390138675715)
                    ·
                      rfl

theorem cell22_2315531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_2315531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315531 prefixEnd_2315531 := by exact prefixLift 2315531
  have htrace : WordTrace (prefixWord ++ tailWord_2315531) baseStart_2315531 baseEnd_2315531 := by
    simpa [prefixWord, tailWord_2315531, baseEnd_2315531] using wordTrace_append hprefix tailTrace_2315531
  have hstable : (prefixWord ++ tailWord_2315531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315531).length < 2 ^ (prefixWord ++ tailWord_2315531).sum := by decide
  have hdescent : baseEnd_2315531 < baseStart_2315531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315576 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2315576 : Nat := 118140960795 + 2315576 * 2 ^ 59
def prefixEnd_2315576 : Nat := 4983230072969 + 3 ^ 40 * 2315576 * 2
def baseEnd_2315576 : Nat := 792668986677025021300577

theorem tailTrace_2315576 : CollatzResearch.WordTrace tailWord_2315576 prefixEnd_2315576 792668986677025021300577 := by
  unfold tailWord_2315576
  simp only [CollatzResearch.WordTrace]
  refine ⟨42227997529535547870511291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56303996706047397160681721 42227997529535547870511291)
  ·
    refine ⟨63341996294303321805766937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42227997529535547870511291 63341996294303321805766937)
    ·
      refine ⟨47506497220727491354325203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63341996294303321805766937 47506497220727491354325203)
      ·
        refine ⟨71259745831091237031487805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47506497220727491354325203 71259745831091237031487805)
        ·
          refine ⟨26722404686659213886807927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71259745831091237031487805 26722404686659213886807927)
          ·
            refine ⟨40083607029988820830211891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26722404686659213886807927 40083607029988820830211891)
            ·
              refine ⟨60125410544983231245317837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40083607029988820830211891 60125410544983231245317837)
              ·
                refine ⟨22547028954368711716994189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60125410544983231245317837 22547028954368711716994189)
                ·
                  refine ⟨8455135857888266893872821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22547028954368711716994189 8455135857888266893872821)
                  ·
                    refine ⟨792668986677025021300577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8455135857888266893872821 792668986677025021300577)
                    ·
                      rfl

theorem cell22_2315576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2315576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315576 prefixEnd_2315576 := by exact prefixLift 2315576
  have htrace : WordTrace (prefixWord ++ tailWord_2315576) baseStart_2315576 baseEnd_2315576 := by
    simpa [prefixWord, tailWord_2315576, baseEnd_2315576] using wordTrace_append hprefix tailTrace_2315576
  have hstable : (prefixWord ++ tailWord_2315576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315576).length < 2 ^ (prefixWord ++ tailWord_2315576).sum := by decide
  have hdescent : baseEnd_2315576 < baseStart_2315576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315593 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_2315593 : Nat := 118140960795 + 2315593 * 2 ^ 59
def prefixEnd_2315593 : Nat := 4983230072969 + 3 ^ 40 * 2315593 * 2
def baseEnd_2315593 : Nat := 792674806124442643625525

theorem tailTrace_2315593 : CollatzResearch.WordTrace tailWord_2315593 prefixEnd_2315593 792674806124442643625525 := by
  unfold tailWord_2315593
  simp only [CollatzResearch.WordTrace]
  refine ⟨84456615100009507644391433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56304410066673005096260955 84456615100009507644391433)
  ·
    refine ⟨63342461325007130733293575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84456615100009507644391433 63342461325007130733293575)
    ·
      refine ⟨95013691987510696099940363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63342461325007130733293575 95013691987510696099940363)
      ·
        refine ⟨142520537981266044149910545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95013691987510696099940363 142520537981266044149910545)
        ·
          refine ⟨106890403485949533112432909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142520537981266044149910545 106890403485949533112432909)
          ·
            refine ⟨40083901307231074917162341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106890403485949533112432909 40083901307231074917162341)
            ·
              refine ⟨7515731495105826546967939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40083901307231074917162341 7515731495105826546967939)
              ·
                refine ⟨11273597242658739820451909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515731495105826546967939 11273597242658739820451909)
                ·
                  refine ⟨2113799482998513716334733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11273597242658739820451909 2113799482998513716334733)
                  ·
                    refine ⟨792674806124442643625525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113799482998513716334733 792674806124442643625525)
                    ·
                      rfl

theorem cell22_2315593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_2315593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315593 prefixEnd_2315593 := by exact prefixLift 2315593
  have htrace : WordTrace (prefixWord ++ tailWord_2315593) baseStart_2315593 baseEnd_2315593 := by
    simpa [prefixWord, tailWord_2315593, baseEnd_2315593] using wordTrace_append hprefix tailTrace_2315593
  have hstable : (prefixWord ++ tailWord_2315593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315593).length < 2 ^ (prefixWord ++ tailWord_2315593).sum := by decide
  have hdescent : baseEnd_2315593 < baseStart_2315593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315672 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_2315672 : Nat := 118140960795 + 2315672 * 2 ^ 59
def prefixEnd_2315672 : Nat := 4983230072969 + 3 ^ 40 * 2315672 * 2
def baseEnd_2315672 : Nat := 792701849438912770900283

theorem tailTrace_2315672 : CollatzResearch.WordTrace tailWord_2315672 prefixEnd_2315672 792701849438912770900283 := by
  unfold tailWord_2315672
  simp only [CollatzResearch.WordTrace]
  refine ⟨42229748233361652068258635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56306330977815536091011513 42229748233361652068258635)
  ·
    refine ⟨63344622350042478102387953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42229748233361652068258635 63344622350042478102387953)
    ·
      refine ⟨47508466762531858576790965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63344622350042478102387953 47508466762531858576790965)
      ·
        refine ⟨4453918758987361741574153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47508466762531858576790965 4453918758987361741574153)
        ·
          refine ⟨3340439069240521306180615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4453918758987361741574153 3340439069240521306180615)
          ·
            refine ⟨5010658603860781959270923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340439069240521306180615 5010658603860781959270923)
            ·
              refine ⟨7515987905791172938906385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010658603860781959270923 7515987905791172938906385)
              ·
                refine ⟨5636990929343379704179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7515987905791172938906385 5636990929343379704179789)
                ·
                  refine ⟨2113871598503767389067421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5636990929343379704179789 2113871598503767389067421)
                  ·
                    refine ⟨792701849438912770900283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113871598503767389067421 792701849438912770900283)
                    ·
                      rfl

theorem cell22_2315672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_2315672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315672 prefixEnd_2315672 := by exact prefixLift 2315672
  have htrace : WordTrace (prefixWord ++ tailWord_2315672) baseStart_2315672 baseEnd_2315672 := by
    simpa [prefixWord, tailWord_2315672, baseEnd_2315672] using wordTrace_append hprefix tailTrace_2315672
  have hstable : (prefixWord ++ tailWord_2315672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315672).length < 2 ^ (prefixWord ++ tailWord_2315672).sum := by decide
  have hdescent : baseEnd_2315672 < baseStart_2315672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2315698 : Nat := 118140960795 + 2315698 * 2 ^ 59
def prefixEnd_2315698 : Nat := 4983230072969 + 3 ^ 40 * 2315698 * 2
def baseEnd_2315698 : Nat := 792710749770257369750203

theorem tailTrace_2315698 : CollatzResearch.WordTrace tailWord_2315698 prefixEnd_2315698 792710749770257369750203 := by
  unfold tailWord_2315698
  simp only [CollatzResearch.WordTrace]
  refine ⟨21115111191157277644240937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56306963176419407051309165 21115111191157277644240937)
  ·
    refine ⟨15836333393367958233180703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21115111191157277644240937 15836333393367958233180703)
    ·
      refine ⟨23754500090051937349771055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15836333393367958233180703 23754500090051937349771055)
      ·
        refine ⟨35631750135077906024656583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23754500090051937349771055 35631750135077906024656583)
        ·
          refine ⟨53447625202616859036984875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35631750135077906024656583 53447625202616859036984875)
          ·
            refine ⟨80171437803925288555477313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53447625202616859036984875 80171437803925288555477313)
            ·
              refine ⟨60128578352943966416607985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80171437803925288555477313 60128578352943966416607985)
              ·
                refine ⟨45096433764707974812455989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60128578352943966416607985 45096433764707974812455989)
                ·
                  refine ⟨4227790665441372638667749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45096433764707974812455989 4227790665441372638667749)
                  ·
                    refine ⟨792710749770257369750203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227790665441372638667749 792710749770257369750203)
                    ·
                      rfl

theorem cell22_2315698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2315698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315698 prefixEnd_2315698 := by exact prefixLift 2315698
  have htrace : WordTrace (prefixWord ++ tailWord_2315698) baseStart_2315698 baseEnd_2315698 := by
    simpa [prefixWord, tailWord_2315698, baseEnd_2315698] using wordTrace_append hprefix tailTrace_2315698
  have hstable : (prefixWord ++ tailWord_2315698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315698).length < 2 ^ (prefixWord ++ tailWord_2315698).sum := by decide
  have hdescent : baseEnd_2315698 < baseStart_2315698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315743 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_2315743 : Nat := 118140960795 + 2315743 * 2 ^ 59
def prefixEnd_2315743 : Nat := 4983230072969 + 3 ^ 40 * 2315743 * 2
def baseEnd_2315743 : Nat := 792726154189892252375065

theorem tailTrace_2315743 : CollatzResearch.WordTrace tailWord_2315743 prefixEnd_2315743 792726154189892252375065 := by
  unfold tailWord_2315743
  simp only [CollatzResearch.WordTrace]
  refine ⟨84462086049466083262351883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56308057366310722174901255 84462086049466083262351883)
  ·
    refine ⟨126693129074199124893527825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84462086049466083262351883 126693129074199124893527825)
    ·
      refine ⟨95019846805649343670145869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126693129074199124893527825 95019846805649343670145869)
      ·
        refine ⟨35632442552118503876304701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95019846805649343670145869 35632442552118503876304701)
        ·
          refine ⟨13362165957044438953614263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35632442552118503876304701 13362165957044438953614263)
          ·
            refine ⟨20043248935566658430421395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13362165957044438953614263 20043248935566658430421395)
            ·
              refine ⟨30064873403349987645632093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20043248935566658430421395 30064873403349987645632093)
              ·
                refine ⟨11274327526256245367112035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30064873403349987645632093 11274327526256245367112035)
                ·
                  refine ⟨16911491289384368050668053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11274327526256245367112035 16911491289384368050668053)
                  ·
                    refine ⟨792726154189892252375065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16911491289384368050668053 792726154189892252375065)
                    ·
                      rfl

theorem cell22_2315743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_2315743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315743 prefixEnd_2315743 := by exact prefixLift 2315743
  have htrace : WordTrace (prefixWord ++ tailWord_2315743) baseStart_2315743 baseEnd_2315743 := by
    simpa [prefixWord, tailWord_2315743, baseEnd_2315743] using wordTrace_append hprefix tailTrace_2315743
  have hstable : (prefixWord ++ tailWord_2315743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315743).length < 2 ^ (prefixWord ++ tailWord_2315743).sum := by decide
  have hdescent : baseEnd_2315743 < baseStart_2315743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315745 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2315745 : Nat := 118140960795 + 2315745 * 2 ^ 59
def prefixEnd_2315745 : Nat := 4983230072969 + 3 ^ 40 * 2315745 * 2
def baseEnd_2315745 : Nat := 792726838830764913825059

theorem tailTrace_2315745 : CollatzResearch.WordTrace tailWord_2315745 prefixEnd_2315745 792726838830764913825059 := by
  unfold tailWord_2315745
  simp only [CollatzResearch.WordTrace]
  refine ⟨84462158995458837603924689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56308105996972558402616459 84462158995458837603924689)
  ·
    refine ⟨63346619246594128202943517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84462158995458837603924689 63346619246594128202943517)
    ·
      refine ⟨23754982217472798076103819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63346619246594128202943517 23754982217472798076103819)
      ·
        refine ⟨35632473326209197114155729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23754982217472798076103819 35632473326209197114155729)
        ·
          refine ⟨26724354994656897835616797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35632473326209197114155729 26724354994656897835616797)
          ·
            refine ⟨10021633122996336688356299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26724354994656897835616797 10021633122996336688356299)
            ·
              refine ⟨15032449684494505032534449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10021633122996336688356299 15032449684494505032534449)
              ·
                refine ⟨11274337263370878774400837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15032449684494505032534449 11274337263370878774400837)
                ·
                  refine ⟨2113938236882039770200157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11274337263370878774400837 2113938236882039770200157)
                  ·
                    refine ⟨792726838830764913825059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113938236882039770200157 792726838830764913825059)
                    ·
                      rfl

theorem cell22_2315745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2315745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315745 prefixEnd_2315745 := by exact prefixLift 2315745
  have htrace : WordTrace (prefixWord ++ tailWord_2315745) baseStart_2315745 baseEnd_2315745 := by
    simpa [prefixWord, tailWord_2315745, baseEnd_2315745] using wordTrace_append hprefix tailTrace_2315745
  have hstable : (prefixWord ++ tailWord_2315745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315745).length < 2 ^ (prefixWord ++ tailWord_2315745).sum := by decide
  have hdescent : baseEnd_2315745 < baseStart_2315745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315747 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 4]
def baseStart_2315747 : Nat := 118140960795 + 2315747 * 2 ^ 59
def prefixEnd_2315747 : Nat := 4983230072969 + 3 ^ 40 * 2315747 * 2
def baseEnd_2315747 : Nat := 264242507823879191758351

theorem tailTrace_2315747 : CollatzResearch.WordTrace tailWord_2315747 prefixEnd_2315747 264242507823879191758351 := by
  unfold tailWord_2315747
  simp only [CollatzResearch.WordTrace]
  refine ⟨84462231941451591945497495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56308154627634394630331663 84462231941451591945497495)
  ·
    refine ⟨126693347912177387918246243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84462231941451591945497495 126693347912177387918246243)
    ·
      refine ⟨190040021868266081877369365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126693347912177387918246243 190040021868266081877369365)
      ·
        refine ⟨8908126025074972588001689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190040021868266081877369365 8908126025074972588001689)
        ·
          refine ⟨6681094518806229441001267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8908126025074972588001689 6681094518806229441001267)
          ·
            refine ⟨10021641778209344161501901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6681094518806229441001267 10021641778209344161501901)
            ·
              refine ⟨3758115666828504060563213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10021641778209344161501901 3758115666828504060563213)
              ·
                refine ⟨1409293375060689022711205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3758115666828504060563213 1409293375060689022711205)
                ·
                  refine ⟨264242507823879191758351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409293375060689022711205 264242507823879191758351)
                  ·
                    rfl

theorem cell22_2315747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 4].length) (baseStart_2315747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315747 prefixEnd_2315747 := by exact prefixLift 2315747
  have htrace : WordTrace (prefixWord ++ tailWord_2315747) baseStart_2315747 baseEnd_2315747 := by
    simpa [prefixWord, tailWord_2315747, baseEnd_2315747] using wordTrace_append hprefix tailTrace_2315747
  have hstable : (prefixWord ++ tailWord_2315747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315747).length < 2 ^ (prefixWord ++ tailWord_2315747).sum := by decide
  have hdescent : baseEnd_2315747 < baseStart_2315747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315760 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_2315760 : Nat := 118140960795 + 2315760 * 2 ^ 59
def prefixEnd_2315760 : Nat := 4983230072969 + 3 ^ 40 * 2315760 * 2
def baseEnd_2315760 : Nat := 792731973637309874700013

theorem tailTrace_2315760 : CollatzResearch.WordTrace tailWord_2315760 prefixEnd_2315760 792731973637309874700013 := by
  unfold tailWord_2315760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42231353045202247582860367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56308470726936330110480489 42231353045202247582860367)
  ·
    refine ⟨63347029567803371374290551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42231353045202247582860367 63347029567803371374290551)
    ·
      refine ⟨95020544351705057061435827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63347029567803371374290551 95020544351705057061435827)
      ·
        refine ⟨142530816527557585592153741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95020544351705057061435827 142530816527557585592153741)
        ·
          refine ⟨53449056197834094597057653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142530816527557585592153741 53449056197834094597057653)
          ·
            refine ⟨5010849018546946368474155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53449056197834094597057653 5010849018546946368474155)
            ·
              refine ⟨7516273527820419552711233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010849018546946368474155 7516273527820419552711233)
              ·
                refine ⟨5637205145865314664533425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7516273527820419552711233 5637205145865314664533425)
                ·
                  refine ⟨4227903859398985998400069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5637205145865314664533425 4227903859398985998400069)
                  ·
                    refine ⟨792731973637309874700013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227903859398985998400069 792731973637309874700013)
                    ·
                      rfl

theorem cell22_2315760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_2315760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315760 prefixEnd_2315760 := by exact prefixLift 2315760
  have htrace : WordTrace (prefixWord ++ tailWord_2315760) baseStart_2315760 baseEnd_2315760 := by
    simpa [prefixWord, tailWord_2315760, baseEnd_2315760] using wordTrace_append hprefix tailTrace_2315760
  have hstable : (prefixWord ++ tailWord_2315760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315760).length < 2 ^ (prefixWord ++ tailWord_2315760).sum := by decide
  have hdescent : baseEnd_2315760 < baseStart_2315760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315762 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_2315762 : Nat := 118140960795 + 2315762 * 2 ^ 59
def prefixEnd_2315762 : Nat := 4983230072969 + 3 ^ 40 * 2315762 * 2
def baseEnd_2315762 : Nat := 792732658278182536150007

theorem tailTrace_2315762 : CollatzResearch.WordTrace tailWord_2315762 prefixEnd_2315762 792732658278182536150007 := by
  unfold tailWord_2315762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21115694759099312376823385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56308519357598166338195693 21115694759099312376823385)
  ·
    refine ⟨15836771069324484282617539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21115694759099312376823385 15836771069324484282617539)
    ·
      refine ⟨23755156603986726423926309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15836771069324484282617539 23755156603986726423926309)
      ·
        refine ⟨4454091863247511204486183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23755156603986726423926309 4454091863247511204486183)
        ·
          refine ⟨6681137794871266806729275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454091863247511204486183 6681137794871266806729275)
          ·
            refine ⟨10021706692306900210093913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6681137794871266806729275 10021706692306900210093913)
            ·
              refine ⟨7516280019230175157570435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10021706692306900210093913 7516280019230175157570435)
              ·
                refine ⟨11274420028845262736355653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516280019230175157570435 11274420028845262736355653)
                ·
                  refine ⟨2113953755408486763066685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11274420028845262736355653 2113953755408486763066685)
                  ·
                    refine ⟨792732658278182536150007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113953755408486763066685 792732658278182536150007)
                    ·
                      rfl

theorem cell22_2315762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_2315762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315762 prefixEnd_2315762 := by exact prefixLift 2315762
  have htrace : WordTrace (prefixWord ++ tailWord_2315762) baseStart_2315762 baseEnd_2315762 := by
    simpa [prefixWord, tailWord_2315762, baseEnd_2315762] using wordTrace_append hprefix tailTrace_2315762
  have hstable : (prefixWord ++ tailWord_2315762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315762).length < 2 ^ (prefixWord ++ tailWord_2315762).sum := by decide
  have hdescent : baseEnd_2315762 < baseStart_2315762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315850 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_2315850 : Nat := 118140960795 + 2315850 * 2 ^ 59
def prefixEnd_2315850 : Nat := 4983230072969 + 3 ^ 40 * 2315850 * 2
def baseEnd_2315850 : Nat := 792762782476579639949737

theorem tailTrace_2315850 : CollatzResearch.WordTrace tailWord_2315850 prefixEnd_2315850 792762782476579639949737 := by
  unfold tailWord_2315850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116497165019610134124251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56310659106718960357664669 21116497165019610134124251)
  ·
    refine ⟨31674745747529415201186377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21116497165019610134124251 31674745747529415201186377)
    ·
      refine ⟨23756059310647061400889783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31674745747529415201186377 23756059310647061400889783)
      ·
        refine ⟨35634088965970592101334675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23756059310647061400889783 35634088965970592101334675)
        ·
          refine ⟨53451133448955888152002013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35634088965970592101334675 53451133448955888152002013)
          ·
            refine ⟨20044175043358458057000755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53451133448955888152002013 20044175043358458057000755)
            ·
              refine ⟨30066262565037687085501133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20044175043358458057000755 30066262565037687085501133)
              ·
                refine ⟨11274848461889132657062925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30066262565037687085501133 11274848461889132657062925)
                ·
                  refine ⟨4228068173208424746398597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11274848461889132657062925 4228068173208424746398597)
                  ·
                    refine ⟨792762782476579639949737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228068173208424746398597 792762782476579639949737)
                    ·
                      rfl

theorem cell22_2315850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_2315850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315850 prefixEnd_2315850 := by exact prefixLift 2315850
  have htrace : WordTrace (prefixWord ++ tailWord_2315850) baseStart_2315850 baseEnd_2315850 := by
    simpa [prefixWord, tailWord_2315850, baseEnd_2315850] using wordTrace_append hprefix tailTrace_2315850
  have hstable : (prefixWord ++ tailWord_2315850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315850).length < 2 ^ (prefixWord ++ tailWord_2315850).sum := by decide
  have hdescent : baseEnd_2315850 < baseStart_2315850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315882 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_2315882 : Nat := 118140960795 + 2315882 * 2 ^ 59
def prefixEnd_2315882 : Nat := 4983230072969 + 3 ^ 40 * 2315882 * 2
def baseEnd_2315882 : Nat := 264257912243514074383213

theorem tailTrace_2315882 : CollatzResearch.WordTrace tailWord_2315882 prefixEnd_2315882 264257912243514074383213 := by
  unfold tailWord_2315882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116788948990627500415475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56311437197308340001107933 21116788948990627500415475)
  ·
    refine ⟨31675183423485941250623213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21116788948990627500415475 31675183423485941250623213)
    ·
      refine ⟨11878193783807227968983705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31675183423485941250623213 11878193783807227968983705)
      ·
        refine ⟨8908645337855420976737779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11878193783807227968983705 8908645337855420976737779)
        ·
          refine ⟨13362968006783131465106669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8908645337855420976737779 13362968006783131465106669)
          ·
            refine ⟨5011113002543674299415001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13362968006783131465106669 5011113002543674299415001)
            ·
              refine ⟨3758334751907755724561251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011113002543674299415001 3758334751907755724561251)
              ·
                refine ⟨5637502127861633586841877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3758334751907755724561251 5637502127861633586841877)
                ·
                  refine ⟨264257912243514074383213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5637502127861633586841877 264257912243514074383213)
                  ·
                    rfl

theorem cell22_2315882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_2315882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315882 prefixEnd_2315882 := by exact prefixLift 2315882
  have htrace : WordTrace (prefixWord ++ tailWord_2315882) baseStart_2315882 baseEnd_2315882 := by
    simpa [prefixWord, tailWord_2315882, baseEnd_2315882] using wordTrace_append hprefix tailTrace_2315882
  have hstable : (prefixWord ++ tailWord_2315882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315882).length < 2 ^ (prefixWord ++ tailWord_2315882).sum := by decide
  have hdescent : baseEnd_2315882 < baseStart_2315882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2315993 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 1, 3]
def baseStart_2315993 : Nat := 118140960795 + 2315993 * 2 ^ 59
def prefixEnd_2315993 : Nat := 4983230072969 + 3 ^ 40 * 2315993 * 2
def baseEnd_2315993 : Nat := 792811734298974933624299

theorem tailTrace_2315993 : CollatzResearch.WordTrace tailWord_2315993 prefixEnd_2315993 792811734298974933624299 := by
  unfold tailWord_2315993
  simp only [CollatzResearch.WordTrace]
  refine ⟨84471204298560375958952633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56314136199040250639301755 84471204298560375958952633)
  ·
    refine ⟨63353403223920281969214475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84471204298560375958952633 63353403223920281969214475)
    ·
      refine ⟨95030104835880422953821713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63353403223920281969214475 95030104835880422953821713)
      ·
        refine ⟨71272578626910317215366285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95030104835880422953821713 71272578626910317215366285)
        ·
          refine ⟨26727216985091368955762357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71272578626910317215366285 26727216985091368955762357)
          ·
            refine ⟨2505676592352315839602721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26727216985091368955762357 2505676592352315839602721)
            ·
              refine ⟨1879257444264236879702041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505676592352315839602721 1879257444264236879702041)
              ·
                refine ⟨1409443083198177659776531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879257444264236879702041 1409443083198177659776531)
                ·
                  refine ⟨2114164624797266489664797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409443083198177659776531 2114164624797266489664797)
                  ·
                    refine ⟨792811734298974933624299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2114164624797266489664797 792811734298974933624299)
                    ·
                      rfl

theorem cell22_2315993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_2315993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2315993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2315993 prefixEnd_2315993 := by exact prefixLift 2315993
  have htrace : WordTrace (prefixWord ++ tailWord_2315993) baseStart_2315993 baseEnd_2315993 := by
    simpa [prefixWord, tailWord_2315993, baseEnd_2315993] using wordTrace_append hprefix tailTrace_2315993
  have hstable : (prefixWord ++ tailWord_2315993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2315993).length < 2 ^ (prefixWord ++ tailWord_2315993).sum := by decide
  have hdescent : baseEnd_2315993 < baseStart_2315993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2315993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316017 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 6]
def baseStart_2316017 : Nat := 118140960795 + 2316017 * 2 ^ 59
def prefixEnd_2316017 : Nat := 4983230072969 + 3 ^ 40 * 2316017 * 2
def baseEnd_2316017 : Nat := 264273316663148957008075

theorem tailTrace_2316017 : CollatzResearch.WordTrace tailWord_2316017 prefixEnd_2316017 264273316663148957008075 := by
  unfold tailWord_2316017
  simp only [CollatzResearch.WordTrace]
  refine ⟨84472079650473428057826305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56314719766982285371884203 84472079650473428057826305)
  ·
    refine ⟨63354059737855071043369729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84472079650473428057826305 63354059737855071043369729)
    ·
      refine ⟨47515544803391303282527297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63354059737855071043369729 47515544803391303282527297)
      ·
        refine ⟨35636658602543477461895473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47515544803391303282527297 35636658602543477461895473)
        ·
          refine ⟨26727493951907608096421605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35636658602543477461895473 26727493951907608096421605)
          ·
            refine ⟨5011405115982676518079051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26727493951907608096421605 5011405115982676518079051)
            ·
              refine ⟨7517107673974014777118577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011405115982676518079051 7517107673974014777118577)
              ·
                refine ⟨5637830755480511082838933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517107673974014777118577 5637830755480511082838933)
                ·
                  refine ⟨264273316663148957008075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5637830755480511082838933 264273316663148957008075)
                  ·
                    rfl

theorem cell22_2316017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_2316017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316017 prefixEnd_2316017 := by exact prefixLift 2316017
  have htrace : WordTrace (prefixWord ++ tailWord_2316017) baseStart_2316017 baseEnd_2316017 := by
    simpa [prefixWord, tailWord_2316017, baseEnd_2316017] using wordTrace_append hprefix tailTrace_2316017
  have hstable : (prefixWord ++ tailWord_2316017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316017).length < 2 ^ (prefixWord ++ tailWord_2316017).sum := by decide
  have hdescent : baseEnd_2316017 < baseStart_2316017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316032 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_2316032 : Nat := 118140960795 + 2316032 * 2 ^ 59
def prefixEnd_2316032 : Nat := 4983230072969 + 3 ^ 40 * 2316032 * 2
def baseEnd_2316032 : Nat := 792825084795991831899179

theorem tailTrace_2316032 : CollatzResearch.WordTrace tailWord_2316032 prefixEnd_2316032 792825084795991831899179 := by
  unfold tailWord_2316032
  simp only [CollatzResearch.WordTrace]
  refine ⟨42236313372709542809811175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56315084496946057079748233 42236313372709542809811175)
  ·
    refine ⟨63354470059064314214716763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42236313372709542809811175 63354470059064314214716763)
    ·
      refine ⟨95031705088596471322075145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63354470059064314214716763 95031705088596471322075145)
      ·
        refine ⟨71273778816447353491556359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95031705088596471322075145 71273778816447353491556359)
        ·
          refine ⟨106910668224671030237334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71273778816447353491556359 106910668224671030237334539)
          ·
            refine ⟨160366002337006545356001809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106910668224671030237334539 160366002337006545356001809)
            ·
              refine ⟨120274501752754909017001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160366002337006545356001809 120274501752754909017001357)
              ·
                refine ⟨45102938157283090881375509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120274501752754909017001357 45102938157283090881375509)
                ·
                  refine ⟨2114200226122644885064477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45102938157283090881375509 2114200226122644885064477)
                  ·
                    refine ⟨792825084795991831899179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2114200226122644885064477 792825084795991831899179)
                    ·
                      rfl

theorem cell22_2316032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_2316032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316032 prefixEnd_2316032 := by exact prefixLift 2316032
  have htrace : WordTrace (prefixWord ++ tailWord_2316032) baseStart_2316032 baseEnd_2316032 := by
    simpa [prefixWord, tailWord_2316032, baseEnd_2316032] using wordTrace_append hprefix tailTrace_2316032
  have hstable : (prefixWord ++ tailWord_2316032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316032).length < 2 ^ (prefixWord ++ tailWord_2316032).sum := by decide
  have hdescent : baseEnd_2316032 < baseStart_2316032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316036 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_2316036 : Nat := 118140960795 + 2316036 * 2 ^ 59
def prefixEnd_2316036 : Nat := 4983230072969 + 3 ^ 40 * 2316036 * 2
def baseEnd_2316036 : Nat := 792826454077737154799167

theorem tailTrace_2316036 : CollatzResearch.WordTrace tailWord_2316036 prefixEnd_2316036 792826454077737154799167 := by
  unfold tailWord_2316036
  simp only [CollatzResearch.WordTrace]
  refine ⟨42236386318702297151383981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56315181758269729535178641 42236386318702297151383981)
  ·
    refine ⟨15838644869513361431768993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42236386318702297151383981 15838644869513361431768993)
    ·
      refine ⟨11878983652135021073826745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15838644869513361431768993 11878983652135021073826745)
      ·
        refine ⟨8909237739101265805370059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11878983652135021073826745 8909237739101265805370059)
        ·
          refine ⟨13363856608651898708055089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8909237739101265805370059 13363856608651898708055089)
          ·
            refine ⟨10022892456488924031041317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13363856608651898708055089 10022892456488924031041317)
            ·
              refine ⟨1879292335591673255820247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10022892456488924031041317 1879292335591673255820247)
              ·
                refine ⟨2818938503387509883730371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879292335591673255820247 2818938503387509883730371)
                ·
                  refine ⟨4228407755081264825595557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818938503387509883730371 4228407755081264825595557)
                  ·
                    refine ⟨792826454077737154799167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228407755081264825595557 792826454077737154799167)
                    ·
                      rfl

theorem cell22_2316036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_2316036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316036 prefixEnd_2316036 := by exact prefixLift 2316036
  have htrace : WordTrace (prefixWord ++ tailWord_2316036) baseStart_2316036 baseEnd_2316036 := by
    simpa [prefixWord, tailWord_2316036, baseEnd_2316036] using wordTrace_append hprefix tailTrace_2316036
  have hstable : (prefixWord ++ tailWord_2316036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316036).length < 2 ^ (prefixWord ++ tailWord_2316036).sum := by decide
  have hdescent : baseEnd_2316036 < baseStart_2316036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316122 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_2316122 : Nat := 118140960795 + 2316122 * 2 ^ 59
def prefixEnd_2316122 : Nat := 4983230072969 + 3 ^ 40 * 2316122 * 2
def baseEnd_2316122 : Nat := 792855893635261597148903

theorem tailTrace_2316122 : CollatzResearch.WordTrace tailWord_2316122 prefixEnd_2316122 792855893635261597148903 := by
  unfold tailWord_2316122
  simp only [CollatzResearch.WordTrace]
  refine ⟨21118977328773257747599655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56317272876728687326932413 21118977328773257747599655)
  ·
    refine ⟨31678465993159886621399483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21118977328773257747599655 31678465993159886621399483)
    ·
      refine ⟨47517698989739829932099225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31678465993159886621399483 47517698989739829932099225)
      ·
        refine ⟨35638274242304872449074419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47517698989739829932099225 35638274242304872449074419)
        ·
          refine ⟨53457411363457308673611629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35638274242304872449074419 53457411363457308673611629)
          ·
            refine ⟨20046529261296490752604361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53457411363457308673611629 20046529261296490752604361)
            ·
              refine ⟨15034896945972368064453271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20046529261296490752604361 15034896945972368064453271)
              ·
                refine ⟨22552345418958552096679907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15034896945972368064453271 22552345418958552096679907)
                ·
                  refine ⟨33828518128437828145019861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22552345418958552096679907 33828518128437828145019861)
                  ·
                    refine ⟨792855893635261597148903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33828518128437828145019861 792855893635261597148903)
                    ·
                      rfl

theorem cell22_2316122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_2316122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316122 prefixEnd_2316122 := by exact prefixLift 2316122
  have htrace : WordTrace (prefixWord ++ tailWord_2316122) baseStart_2316122 baseEnd_2316122 := by
    simpa [prefixWord, tailWord_2316122, baseEnd_2316122] using wordTrace_append hprefix tailTrace_2316122
  have hstable : (prefixWord ++ tailWord_2316122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316122).length < 2 ^ (prefixWord ++ tailWord_2316122).sum := by decide
  have hdescent : baseEnd_2316122 < baseStart_2316122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316154 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_2316154 : Nat := 118140960795 + 2316154 * 2 ^ 59
def prefixEnd_2316154 : Nat := 4983230072969 + 3 ^ 40 * 2316154 * 2
def baseEnd_2316154 : Nat := 792866847889224180348805

theorem tailTrace_2316154 : CollatzResearch.WordTrace tailWord_2316154 prefixEnd_2316154 792866847889224180348805 := by
  unfold tailWord_2316154
  simp only [CollatzResearch.WordTrace]
  refine ⟨21119269112744275113890879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56318050967318066970375677 21119269112744275113890879)
  ·
    refine ⟨31678903669116412670836319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21119269112744275113890879 31678903669116412670836319)
    ·
      refine ⟨47518355503674619006254479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31678903669116412670836319 47518355503674619006254479)
      ·
        refine ⟨71277533255511928509381719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47518355503674619006254479 71277533255511928509381719)
        ·
          refine ⟨106916299883267892764072579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71277533255511928509381719 106916299883267892764072579)
          ·
            refine ⟨160374449824901839146108869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106916299883267892764072579 160374449824901839146108869)
            ·
              refine ⟨30070209342169094839895413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160374449824901839146108869 30070209342169094839895413)
              ·
                refine ⟨2819082125828352641240195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30070209342169094839895413 2819082125828352641240195)
                ·
                  refine ⟨4228623188742528961860293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819082125828352641240195 4228623188742528961860293)
                  ·
                    refine ⟨792866847889224180348805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228623188742528961860293 792866847889224180348805)
                    ·
                      rfl

theorem cell22_2316154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_2316154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316154 prefixEnd_2316154 := by exact prefixLift 2316154
  have htrace : WordTrace (prefixWord ++ tailWord_2316154) baseStart_2316154 baseEnd_2316154 := by
    simpa [prefixWord, tailWord_2316154, baseEnd_2316154] using wordTrace_append hprefix tailTrace_2316154
  have hstable : (prefixWord ++ tailWord_2316154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316154).length < 2 ^ (prefixWord ++ tailWord_2316154).sum := by decide
  have hdescent : baseEnd_2316154 < baseStart_2316154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316158 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2316158 : Nat := 118140960795 + 2316158 * 2 ^ 59
def prefixEnd_2316158 : Nat := 4983230072969 + 3 ^ 40 * 2316158 * 2
def baseEnd_2316158 : Nat := 264289405723656501082931

theorem tailTrace_2316158 : CollatzResearch.WordTrace tailWord_2316158 prefixEnd_2316158 264289405723656501082931 := by
  unfold tailWord_2316158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10559652792870326142338641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56318148228641739425806085 10559652792870326142338641)
  ·
    refine ⟨7919739594652744606753981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10559652792870326142338641 7919739594652744606753981)
    ·
      refine ⟨2969902347994779227532743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7919739594652744606753981 2969902347994779227532743)
      ·
        refine ⟨4454853521992168841299115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969902347994779227532743 4454853521992168841299115)
        ·
          refine ⟨6682280282988253261948673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454853521992168841299115 6682280282988253261948673)
          ·
            refine ⟨5011710212241189946461505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682280282988253261948673 5011710212241189946461505)
            ·
              refine ⟨3758782659180892459846129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011710212241189946461505 3758782659180892459846129)
              ·
                refine ⟨2819086994385669344884597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3758782659180892459846129 2819086994385669344884597)
                ·
                  refine ⟨264289405723656501082931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819086994385669344884597 264289405723656501082931)
                  ·
                    rfl

theorem cell22_2316158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2316158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316158 prefixEnd_2316158 := by exact prefixLift 2316158
  have htrace : WordTrace (prefixWord ++ tailWord_2316158) baseStart_2316158 baseEnd_2316158 := by
    simpa [prefixWord, tailWord_2316158, baseEnd_2316158] using wordTrace_append hprefix tailTrace_2316158
  have hstable : (prefixWord ++ tailWord_2316158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316158).length < 2 ^ (prefixWord ++ tailWord_2316158).sum := by decide
  have hdescent : baseEnd_2316158 < baseStart_2316158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316197 : List Nat := [1, 3, 1, 2, 1, 1, 1, 12]
def baseStart_2316197 : Nat := 118140960795 + 2316197 * 2 ^ 59
def prefixEnd_2316197 : Nat := 4983230072969 + 3 ^ 40 * 2316197 * 2
def baseEnd_2316197 : Nat := 88097951963109600169297

theorem tailTrace_2316197 : CollatzResearch.WordTrace tailWord_2316197 prefixEnd_2316197 88097951963109600169297 := by
  unfold tailWord_2316197
  simp only [CollatzResearch.WordTrace]
  refine ⟨84478644789821318799378845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56319096526547545866252563 84478644789821318799378845)
  ·
    refine ⟨31679491796182994549767067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84478644789821318799378845 31679491796182994549767067)
    ·
      refine ⟨47519237694274491824650601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31679491796182994549767067 47519237694274491824650601)
      ·
        refine ⟨35639428270705868868487951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47519237694274491824650601 35639428270705868868487951)
        ·
          refine ⟨53459142406058803302731927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35639428270705868868487951 53459142406058803302731927)
          ·
            refine ⟨80188713609088204954097891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53459142406058803302731927 80188713609088204954097891)
            ·
              refine ⟨120283070413632307431146837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80188713609088204954097891 120283070413632307431146837)
              ·
                refine ⟨88097951963109600169297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 120283070413632307431146837 88097951963109600169297)
                ·
                  rfl

theorem cell22_2316197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 12].length) (baseStart_2316197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316197 prefixEnd_2316197 := by exact prefixLift 2316197
  have htrace : WordTrace (prefixWord ++ tailWord_2316197) baseStart_2316197 baseEnd_2316197 := by
    simpa [prefixWord, tailWord_2316197, baseEnd_2316197] using wordTrace_append hprefix tailTrace_2316197
  have hstable : (prefixWord ++ tailWord_2316197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316197).length < 2 ^ (prefixWord ++ tailWord_2316197).sum := by decide
  have hdescent : baseEnd_2316197 < baseStart_2316197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316259 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 7]
def baseStart_2316259 : Nat := 118140960795 + 2316259 * 2 ^ 59
def prefixEnd_2316259 : Nat := 4983230072969 + 3 ^ 40 * 2316259 * 2
def baseEnd_2316259 : Nat := 264300930511679635491161

theorem tailTrace_2316259 : CollatzResearch.WordTrace tailWord_2316259 prefixEnd_2316259 264300930511679635491161 := by
  unfold tailWord_2316259
  simp only [CollatzResearch.WordTrace]
  refine ⟨84480906115596703388135831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56320604077064468925423887 84480906115596703388135831)
  ·
    refine ⟨126721359173395055082203747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84480906115596703388135831 126721359173395055082203747)
    ·
      refine ⟨190082038760092582623305621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126721359173395055082203747 190082038760092582623305621)
      ·
        refine ⟨8910095566879339810467451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190082038760092582623305621 8910095566879339810467451)
        ·
          refine ⟨13365143350319009715701177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8910095566879339810467451 13365143350319009715701177)
          ·
            refine ⟨10023857512739257286775883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13365143350319009715701177 10023857512739257286775883)
            ·
              refine ⟨15035786269108885930163825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10023857512739257286775883 15035786269108885930163825)
              ·
                refine ⟨11276839701831664447622869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15035786269108885930163825 11276839701831664447622869)
                ·
                  refine ⟨264300930511679635491161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11276839701831664447622869 264300930511679635491161)
                  ·
                    rfl

theorem cell22_2316259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_2316259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316259 prefixEnd_2316259 := by exact prefixLift 2316259
  have htrace : WordTrace (prefixWord ++ tailWord_2316259) baseStart_2316259 baseEnd_2316259 := by
    simpa [prefixWord, tailWord_2316259, baseEnd_2316259] using wordTrace_append hprefix tailTrace_2316259
  have hstable : (prefixWord ++ tailWord_2316259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316259).length < 2 ^ (prefixWord ++ tailWord_2316259).sum := by decide
  have hdescent : baseEnd_2316259 < baseStart_2316259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316293 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 5]
def baseStart_2316293 : Nat := 118140960795 + 2316293 * 2 ^ 59
def prefixEnd_2316293 : Nat := 4983230072969 + 3 ^ 40 * 2316293 * 2
def baseEnd_2316293 : Nat := 264304810143291383707793

theorem tailTrace_2316293 : CollatzResearch.WordTrace tailWord_2316293 prefixEnd_2316293 264304810143291383707793 := by
  unfold tailWord_2316293
  simp only [CollatzResearch.WordTrace]
  refine ⟨84482146197473527194873533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56321430798315684796582355 84482146197473527194873533)
  ·
    refine ⟨31680804824052572698077575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84482146197473527194873533 31680804824052572698077575)
    ·
      refine ⟨47521207236078859047116363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31680804824052572698077575 47521207236078859047116363)
      ·
        refine ⟨71281810854118288570674545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47521207236078859047116363 71281810854118288570674545)
        ·
          refine ⟨53461358140588716428005909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71281810854118288570674545 53461358140588716428005909)
          ·
            refine ⟨2506001162840096082562777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53461358140588716428005909 2506001162840096082562777)
            ·
              refine ⟨1879500872130072061922083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506001162840096082562777 1879500872130072061922083)
              ·
                refine ⟨2819251308195108092883125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879500872130072061922083 2819251308195108092883125)
                ·
                  refine ⟨264304810143291383707793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819251308195108092883125 264304810143291383707793)
                  ·
                    rfl

theorem cell22_2316293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_2316293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316293 prefixEnd_2316293 := by exact prefixLift 2316293
  have htrace : WordTrace (prefixWord ++ tailWord_2316293) baseStart_2316293 baseEnd_2316293 := by
    simpa [prefixWord, tailWord_2316293, baseEnd_2316293] using wordTrace_append hprefix tailTrace_2316293
  have hstable : (prefixWord ++ tailWord_2316293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316293).length < 2 ^ (prefixWord ++ tailWord_2316293).sum := by decide
  have hdescent : baseEnd_2316293 < baseStart_2316293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316323 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 1, 4]
def baseStart_2316323 : Nat := 118140960795 + 2316323 * 2 ^ 59
def prefixEnd_2316323 : Nat := 4983230072969 + 3 ^ 40 * 2316323 * 2
def baseEnd_2316323 : Nat := 792924700042964072873287

theorem tailTrace_2316323 : CollatzResearch.WordTrace tailWord_2316323 prefixEnd_2316323 792924700042964072873287 := by
  unfold tailWord_2316323
  simp only [CollatzResearch.WordTrace]
  refine ⟨84483240387364842318465623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56322160258243228212310415 84483240387364842318465623)
  ·
    refine ⟨126724860581047263477698435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84483240387364842318465623 126724860581047263477698435)
    ·
      refine ⟨190087290871570895216547653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126724860581047263477698435 190087290871570895216547653)
      ·
        refine ⟨35641367038419542853102685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190087290871570895216547653 35641367038419542853102685)
        ·
          refine ⟨13365512639407328569913507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35641367038419542853102685 13365512639407328569913507)
          ·
            refine ⟨20048268959110992854870261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13365512639407328569913507 20048268959110992854870261)
            ·
              refine ⟨1879525214916655580144087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20048268959110992854870261 1879525214916655580144087)
              ·
                refine ⟨2819287822374983370216131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879525214916655580144087 2819287822374983370216131)
                ·
                  refine ⟨4228931733562475055324197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819287822374983370216131 4228931733562475055324197)
                  ·
                    refine ⟨792924700042964072873287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228931733562475055324197 792924700042964072873287)
                    ·
                      rfl

theorem cell22_2316323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 4].length) (baseStart_2316323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316323 prefixEnd_2316323 := by exact prefixLift 2316323
  have htrace : WordTrace (prefixWord ++ tailWord_2316323) baseStart_2316323 baseEnd_2316323 := by
    simpa [prefixWord, tailWord_2316323, baseEnd_2316323] using wordTrace_append hprefix tailTrace_2316323
  have hstable : (prefixWord ++ tailWord_2316323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316323).length < 2 ^ (prefixWord ++ tailWord_2316323).sum := by decide
  have hdescent : baseEnd_2316323 < baseStart_2316323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316338 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_2316338 : Nat := 118140960795 + 2316338 * 2 ^ 59
def prefixEnd_2316338 : Nat := 4983230072969 + 3 ^ 40 * 2316338 * 2
def baseEnd_2316338 : Nat := 264309944949836344582747

theorem tailTrace_2316338 : CollatzResearch.WordTrace tailWord_2316338 prefixEnd_2316338 264309944949836344582747 := by
  unfold tailWord_2316338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21120946870577624970065417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56322524988206999920174445 21120946870577624970065417)
  ·
    refine ⟨15840710152933218727549063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21120946870577624970065417 15840710152933218727549063)
    ·
      refine ⟨23761065229399828091323595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15840710152933218727549063 23761065229399828091323595)
      ·
        refine ⟨35641597844099742136985393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23761065229399828091323595 35641597844099742136985393)
        ·
          refine ⟨26731198383074806602739045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35641597844099742136985393 26731198383074806602739045)
          ·
            refine ⟨5012099696826526238013571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26731198383074806602739045 5012099696826526238013571)
            ·
              refine ⟨7518149545239789357020357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012099696826526238013571 7518149545239789357020357)
              ·
                refine ⟨1409653039732460504441317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7518149545239789357020357 1409653039732460504441317)
                ·
                  refine ⟨264309944949836344582747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1409653039732460504441317 264309944949836344582747)
                  ·
                    rfl

theorem cell22_2316338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_2316338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316338 prefixEnd_2316338 := by exact prefixLift 2316338
  have htrace : WordTrace (prefixWord ++ tailWord_2316338) baseStart_2316338 baseEnd_2316338 := by
    simpa [prefixWord, tailWord_2316338, baseEnd_2316338] using wordTrace_append hprefix tailTrace_2316338
  have hstable : (prefixWord ++ tailWord_2316338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316338).length < 2 ^ (prefixWord ++ tailWord_2316338).sum := by decide
  have hdescent : baseEnd_2316338 < baseStart_2316338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316353 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2316353 : Nat := 118140960795 + 2316353 * 2 ^ 59
def prefixEnd_2316353 : Nat := 4983230072969 + 3 ^ 40 * 2316353 * 2
def baseEnd_2316353 : Nat := 792934969656053994623195

theorem tailTrace_2316353 : CollatzResearch.WordTrace tailWord_2316353 prefixEnd_2316353 792934969656053994623195 := by
  unfold tailWord_2316353
  simp only [CollatzResearch.WordTrace]
  refine ⟨84484334577256157442057713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56322889718170771628038475 84484334577256157442057713)
  ·
    refine ⟨63363250932942118081543285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84484334577256157442057713 63363250932942118081543285)
    ·
      refine ⟨5940304774963323570144683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63363250932942118081543285 5940304774963323570144683)
      ·
        refine ⟨8910457162444985355217025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5940304774963323570144683 8910457162444985355217025)
        ·
          refine ⟨6682842871833739016412769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8910457162444985355217025 6682842871833739016412769)
          ·
            refine ⟨5012132153875304262309577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682842871833739016412769 5012132153875304262309577)
            ·
              refine ⟨3759099115406478196732183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012132153875304262309577 3759099115406478196732183)
              ·
                refine ⟨5638648673109717295098275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759099115406478196732183 5638648673109717295098275)
                ·
                  refine ⟨8457973009664575942647413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638648673109717295098275 8457973009664575942647413)
                  ·
                    refine ⟨792934969656053994623195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8457973009664575942647413 792934969656053994623195)
                    ·
                      rfl

theorem cell22_2316353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2316353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316353 prefixEnd_2316353 := by exact prefixLift 2316353
  have htrace : WordTrace (prefixWord ++ tailWord_2316353) baseStart_2316353 baseEnd_2316353 := by
    simpa [prefixWord, tailWord_2316353, baseEnd_2316353] using wordTrace_append hprefix tailTrace_2316353
  have hstable : (prefixWord ++ tailWord_2316353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316353).length < 2 ^ (prefixWord ++ tailWord_2316353).sum := by decide
  have hdescent : baseEnd_2316353 < baseStart_2316353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316374 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2316374 : Nat := 118140960795 + 2316374 * 2 ^ 59
def prefixEnd_2316374 : Nat := 4983230072969 + 3 ^ 40 * 2316374 * 2
def baseEnd_2316374 : Nat := 792942158385216939848131

theorem tailTrace_2316374 : CollatzResearch.WordTrace tailWord_2316374 prefixEnd_2316374 792942158385216939848131 := by
  unfold tailWord_2316374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280318781886254876785761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56323400340120052019048117 5280318781886254876785761)
  ·
    refine ⟨3960239086414691157589321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280318781886254876785761 3960239086414691157589321)
    ·
      refine ⟨2970179314811018368191991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960239086414691157589321 2970179314811018368191991)
      ·
        refine ⟨4455268972216527552287987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970179314811018368191991 4455268972216527552287987)
        ·
          refine ⟨6682903458324791328431981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455268972216527552287987 6682903458324791328431981)
          ·
            refine ⟨2506088796871796748161993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6682903458324791328431981 2506088796871796748161993)
            ·
              refine ⟨1879566597653847561121495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506088796871796748161993 1879566597653847561121495)
              ·
                refine ⟨2819349896480771341682243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879566597653847561121495 2819349896480771341682243)
                ·
                  refine ⟨4229024844721157012523365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819349896480771341682243 4229024844721157012523365)
                  ·
                    refine ⟨792942158385216939848131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229024844721157012523365 792942158385216939848131)
                    ·
                      rfl

theorem cell22_2316374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2316374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316374 prefixEnd_2316374 := by exact prefixLift 2316374
  have htrace : WordTrace (prefixWord ++ tailWord_2316374) baseStart_2316374 baseEnd_2316374 := by
    simpa [prefixWord, tailWord_2316374, baseEnd_2316374] using wordTrace_append hprefix tailTrace_2316374
  have hstable : (prefixWord ++ tailWord_2316374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316374).length < 2 ^ (prefixWord ++ tailWord_2316374).sum := by decide
  have hdescent : baseEnd_2316374 < baseStart_2316374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316462 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_2316462 : Nat := 118140960795 + 2316462 * 2 ^ 59
def prefixEnd_2316462 : Nat := 4983230072969 + 3 ^ 40 * 2316462 * 2
def baseEnd_2316462 : Nat := 264324094194538014549287

theorem tailTrace_2316462 : CollatzResearch.WordTrace tailWord_2316462 prefixEnd_2316462 264324094194538014549287 := by
  unfold tailWord_2316462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561038766732658632221955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56325540089240846038517093 10561038766732658632221955)
  ·
    refine ⟨15841558150098987948332933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10561038766732658632221955 15841558150098987948332933)
    ·
      refine ⟨2970292153143560240312425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15841558150098987948332933 2970292153143560240312425)
      ·
        refine ⟨2227719114857670180234319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970292153143560240312425 2227719114857670180234319)
        ·
          refine ⟨3341578672286505270351479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227719114857670180234319 3341578672286505270351479)
          ·
            refine ⟨5012368008429757905527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341578672286505270351479 5012368008429757905527219)
            ·
              refine ⟨7518552012644636858290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012368008429757905527219 7518552012644636858290829)
              ·
                refine ⟨2819457004741738821859061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7518552012644636858290829 2819457004741738821859061)
                ·
                  refine ⟨264324094194538014549287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819457004741738821859061 264324094194538014549287)
                  ·
                    rfl

theorem cell22_2316462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_2316462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316462 prefixEnd_2316462 := by exact prefixLift 2316462
  have htrace : WordTrace (prefixWord ++ tailWord_2316462) baseStart_2316462 baseEnd_2316462 := by
    simpa [prefixWord, tailWord_2316462, baseEnd_2316462] using wordTrace_append hprefix tailTrace_2316462
  have hstable : (prefixWord ++ tailWord_2316462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316462).length < 2 ^ (prefixWord ++ tailWord_2316462).sum := by decide
  have hdescent : baseEnd_2316462 < baseStart_2316462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316501 : List Nat := [1, 3, 2, 4, 12]
def baseStart_2316501 : Nat := 118140960795 + 2316501 * 2 ^ 59
def prefixEnd_2316501 : Nat := 4983230072969 + 3 ^ 40 * 2316501 * 2
def baseEnd_2316501 : Nat := 3263315362471732271287

theorem tailTrace_2316501 : CollatzResearch.WordTrace tailWord_2316501 prefixEnd_2316501 3263315362471732271287 := by
  unfold tailWord_2316501
  simp only [CollatzResearch.WordTrace]
  refine ⟨84489732580719978718445357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56326488387146652478963571 84489732580719978718445357)
  ·
    refine ⟨31683649717769992019417009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84489732580719978718445357 31683649717769992019417009)
    ·
      refine ⟨23762737288327494014562757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31683649717769992019417009 23762737288327494014562757)
      ·
        refine ⟨4455513241561405127730517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23762737288327494014562757 4455513241561405127730517)
        ·
          refine ⟨3263315362471732271287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4455513241561405127730517 3263315362471732271287)
          ·
            rfl

theorem cell22_2316501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 12].length) (baseStart_2316501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316501 prefixEnd_2316501 := by exact prefixLift 2316501
  have htrace : WordTrace (prefixWord ++ tailWord_2316501) baseStart_2316501 baseEnd_2316501 := by
    simpa [prefixWord, tailWord_2316501, baseEnd_2316501] using wordTrace_append hprefix tailTrace_2316501
  have hstable : (prefixWord ++ tailWord_2316501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316501).length < 2 ^ (prefixWord ++ tailWord_2316501).sum := by decide
  have hdescent : baseEnd_2316501 < baseStart_2316501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316516 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2316516 : Nat := 118140960795 + 2316516 * 2 ^ 59
def prefixEnd_2316516 : Nat := 4983230072969 + 3 ^ 40 * 2316516 * 2
def baseEnd_2316516 : Nat := 792990767887175902797695

theorem tailTrace_2316516 : CollatzResearch.WordTrace tailWord_2316516 prefixEnd_2316516 792990767887175902797695 := by
  unfold tailWord_2316516
  simp only [CollatzResearch.WordTrace]
  refine ⟨42245139837832818140120701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56326853117110424186827601 42245139837832818140120701)
  ·
    refine ⟨15841927439187306802545263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42245139837832818140120701 15841927439187306802545263)
    ·
      refine ⟨23762891158780960203817895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15841927439187306802545263 23762891158780960203817895)
      ·
        refine ⟨35644336738171440305726843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23762891158780960203817895 35644336738171440305726843)
        ·
          refine ⟨53466505107257160458590265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35644336738171440305726843 53466505107257160458590265)
          ·
            refine ⟨40099878830442870343942699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53466505107257160458590265 40099878830442870343942699)
            ·
              refine ⟨60149818245664305515914049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40099878830442870343942699 60149818245664305515914049)
              ·
                refine ⟨45112363684248229136935537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60149818245664305515914049 45112363684248229136935537)
                ·
                  refine ⟨33834272763186171852701653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45112363684248229136935537 33834272763186171852701653)
                  ·
                    refine ⟨792990767887175902797695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33834272763186171852701653 792990767887175902797695)
                    ·
                      rfl

theorem cell22_2316516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2316516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316516 prefixEnd_2316516 := by exact prefixLift 2316516
  have htrace : WordTrace (prefixWord ++ tailWord_2316516) baseStart_2316516 baseEnd_2316516 := by
    simpa [prefixWord, tailWord_2316516, baseEnd_2316516] using wordTrace_append hprefix tailTrace_2316516
  have hstable : (prefixWord ++ tailWord_2316516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316516).length < 2 ^ (prefixWord ++ tailWord_2316516).sum := by decide
  have hdescent : baseEnd_2316516 < baseStart_2316516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316531 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_2316531 : Nat := 118140960795 + 2316531 * 2 ^ 59
def prefixEnd_2316531 : Nat := 4983230072969 + 3 ^ 40 * 2316531 * 2
def baseEnd_2316531 : Nat := 792995902693720863672649

theorem tailTrace_2316531 : CollatzResearch.WordTrace tailWord_2316531 prefixEnd_2316531 792995902693720863672649 := by
  unfold tailWord_2316531
  simp only [CollatzResearch.WordTrace]
  refine ⟨84490826770611293842037447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56327217847074195894691631 84490826770611293842037447)
  ·
    refine ⟨126736240155916940763056171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84490826770611293842037447 126736240155916940763056171)
    ·
      refine ⟨190104360233875411144584257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126736240155916940763056171 190104360233875411144584257)
      ·
        refine ⟨142578270175406558358438193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190104360233875411144584257 142578270175406558358438193)
        ·
          refine ⟨106933702631554918768828645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142578270175406558358438193 106933702631554918768828645)
          ·
            refine ⟨20050069243416547269155371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106933702631554918768828645 20050069243416547269155371)
            ·
              refine ⟨30075103865124820903733057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20050069243416547269155371 30075103865124820903733057)
              ·
                refine ⟨22556327898843615677799793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30075103865124820903733057 22556327898843615677799793)
                ·
                  refine ⟨16917245924132711758349845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22556327898843615677799793 16917245924132711758349845)
                  ·
                    refine ⟨792995902693720863672649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16917245924132711758349845 792995902693720863672649)
                    ·
                      rfl

theorem cell22_2316531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_2316531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316531 prefixEnd_2316531 := by exact prefixLift 2316531
  have htrace : WordTrace (prefixWord ++ tailWord_2316531) baseStart_2316531 baseEnd_2316531 := by
    simpa [prefixWord, tailWord_2316531, baseEnd_2316531] using wordTrace_append hprefix tailTrace_2316531
  have hstable : (prefixWord ++ tailWord_2316531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316531).length < 2 ^ (prefixWord ++ tailWord_2316531).sum := by decide
  have hdescent : baseEnd_2316531 < baseStart_2316531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316567 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 1, 3]
def baseStart_2316567 : Nat := 118140960795 + 2316567 * 2 ^ 59
def prefixEnd_2316567 : Nat := 4983230072969 + 3 ^ 40 * 2316567 * 2
def baseEnd_2316567 : Nat := 793008226229428769772539

theorem tailTrace_2316567 : CollatzResearch.WordTrace tailWord_2316567 prefixEnd_2316567 793008226229428769772539 := by
  unfold tailWord_2316567
  simp only [CollatzResearch.WordTrace]
  refine ⟨84492139798480871990347955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56328093198987247993565303 84492139798480871990347955)
  ·
    refine ⟨126738209697721307985521933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84492139798480871990347955 126738209697721307985521933)
    ·
      refine ⟨47526828636645490494570725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126738209697721307985521933 47526828636645490494570725)
      ·
        refine ⟨8911280369371029467732011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47526828636645490494570725 8911280369371029467732011)
        ·
          refine ⟨13366920554056544201598017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8911280369371029467732011 13366920554056544201598017)
          ·
            refine ⟨10025190415542408151198513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13366920554056544201598017 10025190415542408151198513)
            ·
              refine ⟨7518892811656806113398885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10025190415542408151198513 7518892811656806113398885)
              ·
                refine ⟨1409792402185651146262291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7518892811656806113398885 1409792402185651146262291)
                ·
                  refine ⟨2114688603278476719393437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409792402185651146262291 2114688603278476719393437)
                  ·
                    refine ⟨793008226229428769772539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2114688603278476719393437 793008226229428769772539)
                    ·
                      rfl

theorem cell22_2316567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_2316567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316567 prefixEnd_2316567 := by exact prefixLift 2316567
  have htrace : WordTrace (prefixWord ++ tailWord_2316567) baseStart_2316567 baseEnd_2316567 := by
    simpa [prefixWord, tailWord_2316567, baseEnd_2316567] using wordTrace_append hprefix tailTrace_2316567
  have hstable : (prefixWord ++ tailWord_2316567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316567).length < 2 ^ (prefixWord ++ tailWord_2316567).sum := by decide
  have hdescent : baseEnd_2316567 < baseStart_2316567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316625 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 6]
def baseStart_2316625 : Nat := 118140960795 + 2316625 * 2 ^ 59
def prefixEnd_2316625 : Nat := 4983230072969 + 3 ^ 40 * 2316625 * 2
def baseEnd_2316625 : Nat := 264342693604911983940787

theorem tailTrace_2316625 : CollatzResearch.WordTrace tailWord_2316625 prefixEnd_2316625 264342693604911983940787 := by
  unfold tailWord_2316625
  simp only [CollatzResearch.WordTrace]
  refine ⟨84494255232270747895959329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56329503488180498597306219 84494255232270747895959329)
  ·
    refine ⟨63370691424203060921969497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84494255232270747895959329 63370691424203060921969497)
    ·
      refine ⟨47528018568152295691477123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63370691424203060921969497 47528018568152295691477123)
      ·
        refine ⟨71292027852228443537215685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47528018568152295691477123 71292027852228443537215685)
        ·
          refine ⟨13367255222292833163227941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71292027852228443537215685 13367255222292833163227941)
          ·
            refine ⟨2506360354179906218105239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13367255222292833163227941 2506360354179906218105239)
            ·
              refine ⟨3759540531269859327157859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506360354179906218105239 3759540531269859327157859)
              ·
                refine ⟨5639310796904788990736789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759540531269859327157859 5639310796904788990736789)
                ·
                  refine ⟨264342693604911983940787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5639310796904788990736789 264342693604911983940787)
                  ·
                    rfl

theorem cell22_2316625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_2316625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316625 prefixEnd_2316625 := by exact prefixLift 2316625
  have htrace : WordTrace (prefixWord ++ tailWord_2316625) baseStart_2316625 baseEnd_2316625 := by
    simpa [prefixWord, tailWord_2316625, baseEnd_2316625] using wordTrace_append hprefix tailTrace_2316625
  have hstable : (prefixWord ++ tailWord_2316625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316625).length < 2 ^ (prefixWord ++ tailWord_2316625).sum := by decide
  have hdescent : baseEnd_2316625 < baseStart_2316625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316653 : List Nat := [1, 5, 1, 1, 1, 2, 1, 10]
def baseStart_2316653 : Nat := 118140960795 + 2316653 * 2 ^ 59
def prefixEnd_2316653 : Nat := 4983230072969 + 3 ^ 40 * 2316653 * 2
def baseEnd_2316653 : Nat := 88115296198550356902475

theorem tailTrace_2316653 : CollatzResearch.WordTrace tailWord_2316653 prefixEnd_2316653 88115296198550356902475 := by
  unfold tailWord_2316653
  simp only [CollatzResearch.WordTrace]
  refine ⟨84495276476169308677978613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56330184317446205785319075 84495276476169308677978613)
  ·
    refine ⟨7921432169640872688560495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84495276476169308677978613 7921432169640872688560495)
    ·
      refine ⟨11882148254461309032840743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7921432169640872688560495 11882148254461309032840743)
      ·
        refine ⟨17823222381691963549261115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11882148254461309032840743 17823222381691963549261115)
        ·
          refine ⟨26734833572537945323891673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17823222381691963549261115 26734833572537945323891673)
          ·
            refine ⟨20051125179403458992918755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26734833572537945323891673 20051125179403458992918755)
            ·
              refine ⟨30076687769105188489378133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20051125179403458992918755 30076687769105188489378133)
              ·
                refine ⟨88115296198550356902475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30076687769105188489378133 88115296198550356902475)
                ·
                  rfl

theorem cell22_2316653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 10].length) (baseStart_2316653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316653 prefixEnd_2316653 := by exact prefixLift 2316653
  have htrace : WordTrace (prefixWord ++ tailWord_2316653) baseStart_2316653 baseEnd_2316653 := by
    simpa [prefixWord, tailWord_2316653, baseEnd_2316653] using wordTrace_append hprefix tailTrace_2316653
  have hstable : (prefixWord ++ tailWord_2316653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316653).length < 2 ^ (prefixWord ++ tailWord_2316653).sum := by decide
  have hdescent : baseEnd_2316653 < baseStart_2316653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316683 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_2316683 : Nat := 118140960795 + 2316683 * 2 ^ 59
def prefixEnd_2316683 : Nat := 4983230072969 + 3 ^ 40 * 2316683 * 2
def baseEnd_2316683 : Nat := 793047935400043133872183

theorem tailTrace_2316683 : CollatzResearch.WordTrace tailWord_2316683 prefixEnd_2316683 793047935400043133872183 := by
  unfold tailWord_2316683
  simp only [CollatzResearch.WordTrace]
  refine ⟨84496370666060623801570703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56330913777373749201047135 84496370666060623801570703)
  ·
    refine ⟨126744555999090935702356055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84496370666060623801570703 126744555999090935702356055)
    ·
      refine ⟨190116833998636403553534083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126744555999090935702356055 190116833998636403553534083)
      ·
        refine ⟨285175250997954605330301125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190116833998636403553534083 285175250997954605330301125)
        ·
          refine ⟨53470359562116488499431461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285175250997954605330301125 53470359562116488499431461)
          ·
            refine ⟨10025692417896841593643399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53470359562116488499431461 10025692417896841593643399)
            ·
              refine ⟨15038538626845262390465099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10025692417896841593643399 15038538626845262390465099)
              ·
                refine ⟨22557807940267893585697649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15038538626845262390465099 22557807940267893585697649)
                ·
                  refine ⟨16918355955200920189273237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22557807940267893585697649 16918355955200920189273237)
                  ·
                    refine ⟨793047935400043133872183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16918355955200920189273237 793047935400043133872183)
                    ·
                      rfl

theorem cell22_2316683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_2316683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316683 prefixEnd_2316683 := by exact prefixLift 2316683
  have htrace : WordTrace (prefixWord ++ tailWord_2316683) baseStart_2316683 baseEnd_2316683 := by
    simpa [prefixWord, tailWord_2316683, baseEnd_2316683] using wordTrace_append hprefix tailTrace_2316683
  have hstable : (prefixWord ++ tailWord_2316683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316683).length < 2 ^ (prefixWord ++ tailWord_2316683).sum := by decide
  have hdescent : baseEnd_2316683 < baseStart_2316683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316732 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_2316732 : Nat := 118140960795 + 2316732 * 2 ^ 59
def prefixEnd_2316732 : Nat := 4983230072969 + 3 ^ 40 * 2316732 * 2
def baseEnd_2316732 : Nat := 264354903033807779799011

theorem tailTrace_2316732 : CollatzResearch.WordTrace tailWord_2316732 prefixEnd_2316732 264354903033807779799011 := by
  unfold tailWord_2316732
  simp only [CollatzResearch.WordTrace]
  refine ⟨42249078921441552585052225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56332105228588736780069633 42249078921441552585052225)
  ·
    refine ⟨31686809191081164438789169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42249078921441552585052225 31686809191081164438789169)
    ·
      refine ⟨23765106893310873329091877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31686809191081164438789169 23765106893310873329091877)
      ·
        refine ⟨4455957542495788749204727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23765106893310873329091877 4455957542495788749204727)
        ·
          refine ⟨6683936313743683123807091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455957542495788749204727 6683936313743683123807091)
          ·
            refine ⟨10025904470615524685710637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683936313743683123807091 10025904470615524685710637)
            ·
              refine ⟨3759714176480821757141489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10025904470615524685710637 3759714176480821757141489)
              ·
                refine ⟨2819785632360616317856117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759714176480821757141489 2819785632360616317856117)
                ·
                  refine ⟨264354903033807779799011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819785632360616317856117 264354903033807779799011)
                  ·
                    rfl

theorem cell22_2316732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_2316732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316732 prefixEnd_2316732 := by exact prefixLift 2316732
  have htrace : WordTrace (prefixWord ++ tailWord_2316732) baseStart_2316732 baseEnd_2316732 := by
    simpa [prefixWord, tailWord_2316732, baseEnd_2316732] using wordTrace_append hprefix tailTrace_2316732
  have hstable : (prefixWord ++ tailWord_2316732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316732).length < 2 ^ (prefixWord ++ tailWord_2316732).sum := by decide
  have hdescent : baseEnd_2316732 < baseStart_2316732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316762 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_2316762 : Nat := 118140960795 + 2316762 * 2 ^ 59
def prefixEnd_2316762 : Nat := 4983230072969 + 3 ^ 40 * 2316762 * 2
def baseEnd_2316762 : Nat := 793074978714513261146941

theorem tailTrace_2316762 : CollatzResearch.WordTrace tailWord_2316762 prefixEnd_2316762 793074978714513261146941 := by
  unfold tailWord_2316762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21124813008193605073424135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56332834688516280195797693 21124813008193605073424135)
  ·
    refine ⟨31687219512290407610136203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21124813008193605073424135 31687219512290407610136203)
    ·
      refine ⟨47530829268435611415204305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31687219512290407610136203 47530829268435611415204305)
      ·
        refine ⟨35648121951326708561403229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47530829268435611415204305 35648121951326708561403229)
        ·
          refine ⟨13368045731747515710526211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35648121951326708561403229 13368045731747515710526211)
          ·
            refine ⟨20052068597621273565789317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13368045731747515710526211 20052068597621273565789317)
            ·
              refine ⟨3759762862053988793585497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20052068597621273565789317 3759762862053988793585497)
              ·
                refine ⟨2819822146540491595189123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759762862053988793585497 2819822146540491595189123)
                ·
                  refine ⟨4229733219810737392783685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819822146540491595189123 4229733219810737392783685)
                  ·
                    refine ⟨793074978714513261146941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229733219810737392783685 793074978714513261146941)
                    ·
                      rfl

theorem cell22_2316762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_2316762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316762 prefixEnd_2316762 := by exact prefixLift 2316762
  have htrace : WordTrace (prefixWord ++ tailWord_2316762) baseStart_2316762 baseEnd_2316762 := by
    simpa [prefixWord, tailWord_2316762, baseEnd_2316762] using wordTrace_append hprefix tailTrace_2316762
  have hstable : (prefixWord ++ tailWord_2316762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316762).length < 2 ^ (prefixWord ++ tailWord_2316762).sum := by decide
  have hdescent : baseEnd_2316762 < baseStart_2316762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316770 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2316770 : Nat := 118140960795 + 2316770 * 2 ^ 59
def prefixEnd_2316770 : Nat := 4983230072969 + 3 ^ 40 * 2316770 * 2
def baseEnd_2316770 : Nat := 793077717278003906946917

theorem tailTrace_2316770 : CollatzResearch.WordTrace tailWord_2316770 prefixEnd_2316770 793077717278003906946917 := by
  unfold tailWord_2316770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21124885954186359414996941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56333029211163625106658509 21124885954186359414996941)
  ·
    refine ⟨7921832232819884780623853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21124885954186359414996941 7921832232819884780623853)
    ·
      refine ⟨2970687087307456792733945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7921832232819884780623853 2970687087307456792733945)
      ·
        refine ⟨2228015315480592594550459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970687087307456792733945 2228015315480592594550459)
        ·
          refine ⟨3342022973220888891825689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228015315480592594550459 3342022973220888891825689)
          ·
            refine ⟨2506517229915666668869267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342022973220888891825689 2506517229915666668869267)
            ·
              refine ⟨3759775844873500003303901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506517229915666668869267 3759775844873500003303901)
              ·
                refine ⟨1409915941827562501238963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3759775844873500003303901 1409915941827562501238963)
                ·
                  refine ⟨2114873912741343751858445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409915941827562501238963 2114873912741343751858445)
                  ·
                    refine ⟨793077717278003906946917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2114873912741343751858445 793077717278003906946917)
                    ·
                      rfl

theorem cell22_2316770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2316770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316770 prefixEnd_2316770 := by exact prefixLift 2316770
  have htrace : WordTrace (prefixWord ++ tailWord_2316770) baseStart_2316770 baseEnd_2316770 := by
    simpa [prefixWord, tailWord_2316770, baseEnd_2316770] using wordTrace_append hprefix tailTrace_2316770
  have hstable : (prefixWord ++ tailWord_2316770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316770).length < 2 ^ (prefixWord ++ tailWord_2316770).sum := by decide
  have hdescent : baseEnd_2316770 < baseStart_2316770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316775 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2316775 : Nat := 118140960795 + 2316775 * 2 ^ 59
def prefixEnd_2316775 : Nat := 4983230072969 + 3 ^ 40 * 2316775 * 2
def baseEnd_2316775 : Nat := 793079428880185560571901

theorem tailTrace_2316775 : CollatzResearch.WordTrace tailWord_2316775 prefixEnd_2316775 793079428880185560571901 := by
  unfold tailWord_2316775
  simp only [CollatzResearch.WordTrace]
  refine ⟨84499726181727323513919779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56333150787818215675946519 84499726181727323513919779)
  ·
    refine ⟨126749589272590985270879669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84499726181727323513919779 126749589272590985270879669)
    ·
      refine ⟨11882773994305404869144969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126749589272590985270879669 11882773994305404869144969)
      ·
        refine ⟨8912080495729053651858727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11882773994305404869144969 8912080495729053651858727)
        ·
          refine ⟨13368120743593580477788091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912080495729053651858727 13368120743593580477788091)
          ·
            refine ⟨20052181115390370716682137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13368120743593580477788091 20052181115390370716682137)
            ·
              refine ⟨15039135836542778037511603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20052181115390370716682137 15039135836542778037511603)
              ·
                refine ⟨22558703754814167056267405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15039135836542778037511603 22558703754814167056267405)
                ·
                  refine ⟨8459513908055312646100277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22558703754814167056267405 8459513908055312646100277)
                  ·
                    refine ⟨793079428880185560571901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8459513908055312646100277 793079428880185560571901)
                    ·
                      rfl

theorem cell22_2316775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2316775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316775 prefixEnd_2316775 := by exact prefixLift 2316775
  have htrace : WordTrace (prefixWord ++ tailWord_2316775) baseStart_2316775 baseEnd_2316775 := by
    simpa [prefixWord, tailWord_2316775, baseEnd_2316775] using wordTrace_append hprefix tailTrace_2316775
  have hstable : (prefixWord ++ tailWord_2316775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316775).length < 2 ^ (prefixWord ++ tailWord_2316775).sum := by decide
  have hdescent : baseEnd_2316775 < baseStart_2316775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316792 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_2316792 : Nat := 118140960795 + 2316792 * 2 ^ 59
def prefixEnd_2316792 : Nat := 4983230072969 + 3 ^ 40 * 2316792 * 2
def baseEnd_2316792 : Nat := 793085248327603182896849

theorem tailTrace_2316792 : CollatzResearch.WordTrace tailWord_2316792 prefixEnd_2316792 793085248327603182896849 := by
  unfold tailWord_2316792
  simp only [CollatzResearch.WordTrace]
  refine ⟨42250173111332867708644315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56333564148443823611525753 42250173111332867708644315)
  ·
    refine ⟨63375259666999301562966473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42250173111332867708644315 63375259666999301562966473)
    ·
      refine ⟨47531444750249476172224855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63375259666999301562966473 47531444750249476172224855)
      ·
        refine ⟨71297167125374214258337283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47531444750249476172224855 71297167125374214258337283)
        ·
          refine ⟨106945750688061321387505925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71297167125374214258337283 106945750688061321387505925)
          ·
            refine ⟨20052328254011497760157361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106945750688061321387505925 20052328254011497760157361)
            ·
              refine ⟨15039246190508623320118021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20052328254011497760157361 15039246190508623320118021)
              ·
                refine ⟨2819858660720366872522129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15039246190508623320118021 2819858660720366872522129)
                ·
                  refine ⟨2114893995540275154391597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2819858660720366872522129 2114893995540275154391597)
                  ·
                    refine ⟨793085248327603182896849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2114893995540275154391597 793085248327603182896849)
                    ·
                      rfl

theorem cell22_2316792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_2316792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316792 prefixEnd_2316792 := by exact prefixLift 2316792
  have htrace : WordTrace (prefixWord ++ tailWord_2316792) baseStart_2316792 baseEnd_2316792 := by
    simpa [prefixWord, tailWord_2316792, baseEnd_2316792] using wordTrace_append hprefix tailTrace_2316792
  have hstable : (prefixWord ++ tailWord_2316792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316792).length < 2 ^ (prefixWord ++ tailWord_2316792).sum := by decide
  have hdescent : baseEnd_2316792 < baseStart_2316792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316813 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2316813 : Nat := 118140960795 + 2316813 * 2 ^ 59
def prefixEnd_2316813 : Nat := 4983230072969 + 3 ^ 40 * 2316813 * 2
def baseEnd_2316813 : Nat := 793092437056766128121785

theorem tailTrace_2316813 : CollatzResearch.WordTrace tailWord_2316813 prefixEnd_2316813 793092437056766128121785 := by
  unfold tailWord_2316813
  simp only [CollatzResearch.WordTrace]
  refine ⟨84501112155589656003803093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56334074770393104002535395 84501112155589656003803093)
  ·
    refine ⟨1980494816146632562589135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84501112155589656003803093 1980494816146632562589135)
    ·
      refine ⟨2970742224219948843883703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980494816146632562589135 2970742224219948843883703)
      ·
        refine ⟨4456113336329923265825555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970742224219948843883703 4456113336329923265825555)
        ·
          refine ⟨6684170004494884898738333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456113336329923265825555 6684170004494884898738333)
          ·
            refine ⟨2506563751685581837026875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6684170004494884898738333 2506563751685581837026875)
            ·
              refine ⟨3759845627528372755540313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506563751685581837026875 3759845627528372755540313)
              ·
                refine ⟨2819884220646279566655235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759845627528372755540313 2819884220646279566655235)
                ·
                  refine ⟨4229826330969419349982853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819884220646279566655235 4229826330969419349982853)
                  ·
                    refine ⟨793092437056766128121785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229826330969419349982853 793092437056766128121785)
                    ·
                      rfl

theorem cell22_2316813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2316813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316813 prefixEnd_2316813 := by exact prefixLift 2316813
  have htrace : WordTrace (prefixWord ++ tailWord_2316813) baseStart_2316813 baseEnd_2316813 := by
    simpa [prefixWord, tailWord_2316813, baseEnd_2316813] using wordTrace_append hprefix tailTrace_2316813
  have hstable : (prefixWord ++ tailWord_2316813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316813).length < 2 ^ (prefixWord ++ tailWord_2316813).sum := by decide
  have hdescent : baseEnd_2316813 < baseStart_2316813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316839 : List Nat := [1, 1, 7, 2, 2, 9]
def baseStart_2316839 : Nat := 118140960795 + 2316839 * 2 ^ 59
def prefixEnd_2316839 : Nat := 4983230072969 + 3 ^ 40 * 2316839 * 2
def baseEnd_2316839 : Nat := 9791374535655687987305

theorem tailTrace_2316839 : CollatzResearch.WordTrace tailWord_2316839 prefixEnd_2316839 9791374535655687987305 := by
  unfold tailWord_2316839
  simp only [CollatzResearch.WordTrace]
  refine ⟨84502060453495462444249571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56334706968996974962833047 84502060453495462444249571)
  ·
    refine ⟨126753090680243193666374357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84502060453495462444249571 126753090680243193666374357)
    ·
      refine ⟨2970775562818199851555649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 126753090680243193666374357 2970775562818199851555649)
      ·
        refine ⟨2228081672113649888666737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970775562818199851555649 2228081672113649888666737)
        ·
          refine ⟨1671061254085237416500053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228081672113649888666737 1671061254085237416500053)
          ·
            refine ⟨9791374535655687987305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1671061254085237416500053 9791374535655687987305)
            ·
              rfl

theorem cell22_2316839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 9].length) (baseStart_2316839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316839 prefixEnd_2316839 := by exact prefixLift 2316839
  have htrace : WordTrace (prefixWord ++ tailWord_2316839) baseStart_2316839 baseEnd_2316839 := by
    simpa [prefixWord, tailWord_2316839, baseEnd_2316839] using wordTrace_append hprefix tailTrace_2316839
  have hstable : (prefixWord ++ tailWord_2316839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316839).length < 2 ^ (prefixWord ++ tailWord_2316839).sum := by decide
  have hdescent : baseEnd_2316839 < baseStart_2316839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316850 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_2316850 : Nat := 118140960795 + 2316850 * 2 ^ 59
def prefixEnd_2316850 : Nat := 4983230072969 + 3 ^ 40 * 2316850 * 2
def baseEnd_2316850 : Nat := 264368367637636788315557

theorem tailTrace_2316850 : CollatzResearch.WordTrace tailWord_2316850 prefixEnd_2316850 264368367637636788315557 := by
  unfold tailWord_2316850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125615414113902830725001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56334974437637074215266669 21125615414113902830725001)
  ·
    refine ⟨15844211560585427123043751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21125615414113902830725001 15844211560585427123043751)
    ·
      refine ⟨23766317340878140684565627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15844211560585427123043751 23766317340878140684565627)
      ·
        refine ⟨35649476011317211026848441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23766317340878140684565627 35649476011317211026848441)
        ·
          refine ⟨26737107008487908270136331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35649476011317211026848441 26737107008487908270136331)
          ·
            refine ⟨40105660512731862405204497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26737107008487908270136331 40105660512731862405204497)
            ·
              refine ⟨30079245384548896803903373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40105660512731862405204497 30079245384548896803903373)
              ·
                refine ⟨11279717019205836301463765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30079245384548896803903373 11279717019205836301463765)
                ·
                  refine ⟨264368367637636788315557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11279717019205836301463765 264368367637636788315557)
                  ·
                    rfl

theorem cell22_2316850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_2316850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316850 prefixEnd_2316850 := by exact prefixLift 2316850
  have htrace : WordTrace (prefixWord ++ tailWord_2316850) baseStart_2316850 baseEnd_2316850 := by
    simpa [prefixWord, tailWord_2316850, baseEnd_2316850] using wordTrace_append hprefix tailTrace_2316850
  have hstable : (prefixWord ++ tailWord_2316850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316850).length < 2 ^ (prefixWord ++ tailWord_2316850).sum := by decide
  have hdescent : baseEnd_2316850 < baseStart_2316850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316901 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 5]
def baseStart_2316901 : Nat := 118140960795 + 2316901 * 2 ^ 59
def prefixEnd_2316901 : Nat := 4983230072969 + 3 ^ 40 * 2316901 * 2
def baseEnd_2316901 : Nat := 264374187085054410640505

theorem tailTrace_2316901 : CollatzResearch.WordTrace tailWord_2316901 prefixEnd_2316901 264374187085054410640505 := by
  unfold tailWord_2316901
  simp only [CollatzResearch.WordTrace]
  refine ⟨84504321779270847033006557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56336214519513898022004371 84504321779270847033006557)
  ·
    refine ⟨31689120667226567637377459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84504321779270847033006557 31689120667226567637377459)
    ·
      refine ⟨47533681000839851456066189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31689120667226567637377459 47533681000839851456066189)
      ·
        refine ⟨17825130375314944296024821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47533681000839851456066189 17825130375314944296024821)
        ·
          refine ⟨1671105972685776027752327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17825130375314944296024821 1671105972685776027752327)
          ·
            refine ⟨2506658959028664041628491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671105972685776027752327 2506658959028664041628491)
            ·
              refine ⟨3759988438542996062442737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506658959028664041628491 3759988438542996062442737)
              ·
                refine ⟨2819991328907247046832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759988438542996062442737 2819991328907247046832053)
                ·
                  refine ⟨264374187085054410640505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819991328907247046832053 264374187085054410640505)
                  ·
                    rfl

theorem cell22_2316901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_2316901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316901 prefixEnd_2316901 := by exact prefixLift 2316901
  have htrace : WordTrace (prefixWord ++ tailWord_2316901) baseStart_2316901 baseEnd_2316901 := by
    simpa [prefixWord, tailWord_2316901, baseEnd_2316901] using wordTrace_append hprefix tailTrace_2316901
  have hstable : (prefixWord ++ tailWord_2316901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316901).length < 2 ^ (prefixWord ++ tailWord_2316901).sum := by decide
  have hdescent : baseEnd_2316901 < baseStart_2316901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316942 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2316942 : Nat := 118140960795 + 2316942 * 2 ^ 59
def prefixEnd_2316942 : Nat := 4983230072969 + 3 ^ 40 * 2316942 * 2
def baseEnd_2316942 : Nat := 793136596393052791646389

theorem tailTrace_2316942 : CollatzResearch.WordTrace tailWord_2316942 prefixEnd_2316942 793136596393052791646389 := by
  unfold tailWord_2316942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563227146515288879406135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56337211448081540690166053 10563227146515288879406135)
  ·
    refine ⟨15844840719772933319109203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10563227146515288879406135 15844840719772933319109203)
    ·
      refine ⟨23767261079659399978663805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15844840719772933319109203 23767261079659399978663805)
      ·
        refine ⟨8912722904872274991998927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23767261079659399978663805 8912722904872274991998927)
        ·
          refine ⟨13369084357308412487998391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912722904872274991998927 13369084357308412487998391)
          ·
            refine ⟨20053626535962618731997587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13369084357308412487998391 20053626535962618731997587)
            ·
              refine ⟨30080439803943928097996381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20053626535962618731997587 30080439803943928097996381)
              ·
                refine ⟨11280164926478973036748643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30080439803943928097996381 11280164926478973036748643)
                ·
                  refine ⟨16920247389718459555122965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11280164926478973036748643 16920247389718459555122965)
                  ·
                    refine ⟨793136596393052791646389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16920247389718459555122965 793136596393052791646389)
                    ·
                      rfl

theorem cell22_2316942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2316942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316942 prefixEnd_2316942 := by exact prefixLift 2316942
  have htrace : WordTrace (prefixWord ++ tailWord_2316942) baseStart_2316942 baseEnd_2316942 := by
    simpa [prefixWord, tailWord_2316942, baseEnd_2316942] using wordTrace_append hprefix tailTrace_2316942
  have hstable : (prefixWord ++ tailWord_2316942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316942).length < 2 ^ (prefixWord ++ tailWord_2316942).sum := by decide
  have hdescent : baseEnd_2316942 < baseStart_2316942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316946 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_2316946 : Nat := 118140960795 + 2316946 * 2 ^ 59
def prefixEnd_2316946 : Nat := 4983230072969 + 3 ^ 40 * 2316946 * 2
def baseEnd_2316946 : Nat := 264379321891599371515459

theorem tailTrace_2316946 : CollatzResearch.WordTrace tailWord_2316946 prefixEnd_2316946 264379321891599371515459 := by
  unfold tailWord_2316946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21126490766026954929598673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56337308709405213145596461 21126490766026954929598673)
  ·
    refine ⟨15844868074520216197199005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21126490766026954929598673 15844868074520216197199005)
    ·
      refine ⟨5941825527945081073949627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15844868074520216197199005 5941825527945081073949627)
      ·
        refine ⟨8912738291917621610924441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941825527945081073949627 8912738291917621610924441)
        ·
          refine ⟨6684553718938216208193331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8912738291917621610924441 6684553718938216208193331)
          ·
            refine ⟨10026830578407324312289997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684553718938216208193331 10026830578407324312289997)
            ·
              refine ⟨3760061466902746617108749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10026830578407324312289997 3760061466902746617108749)
              ·
                refine ⟨1410023050088529981415781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3760061466902746617108749 1410023050088529981415781)
                ·
                  refine ⟨264379321891599371515459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410023050088529981415781 264379321891599371515459)
                  ·
                    rfl

theorem cell22_2316946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_2316946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316946 prefixEnd_2316946 := by exact prefixLift 2316946
  have htrace : WordTrace (prefixWord ++ tailWord_2316946) baseStart_2316946 baseEnd_2316946 := by
    simpa [prefixWord, tailWord_2316946, baseEnd_2316946] using wordTrace_append hprefix tailTrace_2316946
  have hstable : (prefixWord ++ tailWord_2316946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316946).length < 2 ^ (prefixWord ++ tailWord_2316946).sum := by decide
  have hdescent : baseEnd_2316946 < baseStart_2316946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316974 : List Nat := [4, 1, 4, 1, 1, 1, 1, 9]
def baseStart_2316974 : Nat := 118140960795 + 2316974 * 2 ^ 59
def prefixEnd_2316974 : Nat := 4983230072969 + 3 ^ 40 * 2316974 * 2
def baseEnd_2316974 : Nat := 88127505627446152760699

theorem tailTrace_2316974 : CollatzResearch.WordTrace tailWord_2316974 prefixEnd_2316974 88127505627446152760699 := by
  unfold tailWord_2316974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563373038500797562551747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56337989538670920333609317 10563373038500797562551747)
  ·
    refine ⟨15845059557751196343827621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10563373038500797562551747 15845059557751196343827621)
    ·
      refine ⟨2970948667078349314467679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15845059557751196343827621 2970948667078349314467679)
      ·
        refine ⟨4456423000617523971701519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970948667078349314467679 4456423000617523971701519)
        ·
          refine ⟨6684634500926285957552279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456423000617523971701519 6684634500926285957552279)
          ·
            refine ⟨10026951751389428936328419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684634500926285957552279 10026951751389428936328419)
            ·
              refine ⟨15040427627084143404492629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10026951751389428936328419 15040427627084143404492629)
              ·
                refine ⟨88127505627446152760699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15040427627084143404492629 88127505627446152760699)
                ·
                  rfl

theorem cell22_2316974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_2316974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316974 prefixEnd_2316974 := by exact prefixLift 2316974
  have htrace : WordTrace (prefixWord ++ tailWord_2316974) baseStart_2316974 baseEnd_2316974 := by
    simpa [prefixWord, tailWord_2316974, baseEnd_2316974] using wordTrace_append hprefix tailTrace_2316974
  have hstable : (prefixWord ++ tailWord_2316974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316974).length < 2 ^ (prefixWord ++ tailWord_2316974).sum := by decide
  have hdescent : baseEnd_2316974 < baseStart_2316974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2316993 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2316993 : Nat := 118140960795 + 2316993 * 2 ^ 59
def prefixEnd_2316993 : Nat := 4983230072969 + 3 ^ 40 * 2316993 * 2
def baseEnd_2316993 : Nat := 793154054735305658621233

theorem tailTrace_2316993 : CollatzResearch.WordTrace tailWord_2316993 prefixEnd_2316993 793154054735305658621233 := by
  unfold tailWord_2316993
  simp only [CollatzResearch.WordTrace]
  refine ⟨84507677294937546745355633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56338451529958364496903755 84507677294937546745355633)
  ·
    refine ⟨63380757971203160059016725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84507677294937546745355633 63380757971203160059016725)
    ·
      refine ⟨2970973029900148127766409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63380757971203160059016725 2970973029900148127766409)
      ·
        refine ⟨2228229772425111095824807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970973029900148127766409 2228229772425111095824807)
        ·
          refine ⟨3342344658637666643737211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228229772425111095824807 3342344658637666643737211)
          ·
            refine ⟨5013516987956499965605817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342344658637666643737211 5013516987956499965605817)
            ·
              refine ⟨3760137740967374974204363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5013516987956499965605817 3760137740967374974204363)
              ·
                refine ⟨5640206611451062461306545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760137740967374974204363 5640206611451062461306545)
                ·
                  refine ⟨4230154958588296845979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5640206611451062461306545 4230154958588296845979909)
                  ·
                    refine ⟨793154054735305658621233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4230154958588296845979909 793154054735305658621233)
                    ·
                      rfl

theorem cell22_2316993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2316993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2316993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2316993 prefixEnd_2316993 := by exact prefixLift 2316993
  have htrace : WordTrace (prefixWord ++ tailWord_2316993) baseStart_2316993 baseEnd_2316993 := by
    simpa [prefixWord, tailWord_2316993, baseEnd_2316993] using wordTrace_append hprefix tailTrace_2316993
  have hstable : (prefixWord ++ tailWord_2316993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2316993).length < 2 ^ (prefixWord ++ tailWord_2316993).sum := by decide
  have hdescent : baseEnd_2316993 < baseStart_2316993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2316993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317017 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_2317017 : Nat := 118140960795 + 2317017 * 2 ^ 59
def prefixEnd_2317017 : Nat := 4983230072969 + 3 ^ 40 * 2317017 * 2
def baseEnd_2317017 : Nat := 793162270425777596021159

theorem tailTrace_2317017 : CollatzResearch.WordTrace tailWord_2317017 prefixEnd_2317017 793162270425777596021159 := by
  unfold tailWord_2317017
  simp only [CollatzResearch.WordTrace]
  refine ⟨84508552646850598844229305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56339035097900399229486203 84508552646850598844229305)
  ·
    refine ⟨63381414485137949133171979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84508552646850598844229305 63381414485137949133171979)
    ·
      refine ⟨95072121727706923699757969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63381414485137949133171979 95072121727706923699757969)
      ·
        refine ⟨71304091295780192774818477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95072121727706923699757969 71304091295780192774818477)
        ·
          refine ⟨26739034235917572290556929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71304091295780192774818477 26739034235917572290556929)
          ·
            refine ⟨20054275676938179217917697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26739034235917572290556929 20054275676938179217917697)
            ·
              refine ⟨15040706757703634413438273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20054275676938179217917697 15040706757703634413438273)
              ·
                refine ⟨11280530068277725810078705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15040706757703634413438273 11280530068277725810078705)
                ·
                  refine ⟨8460397551208294357559029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11280530068277725810078705 8460397551208294357559029)
                  ·
                    refine ⟨793162270425777596021159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8460397551208294357559029 793162270425777596021159)
                    ·
                      rfl

theorem cell22_2317017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_2317017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317017 prefixEnd_2317017 := by exact prefixLift 2317017
  have htrace : WordTrace (prefixWord ++ tailWord_2317017) baseStart_2317017 baseEnd_2317017 := by
    simpa [prefixWord, tailWord_2317017, baseEnd_2317017] using wordTrace_append hprefix tailTrace_2317017
  have hstable : (prefixWord ++ tailWord_2317017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317017).length < 2 ^ (prefixWord ++ tailWord_2317017).sum := by decide
  have hdescent : baseEnd_2317017 < baseStart_2317017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317023 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 1, 3]
def baseStart_2317023 : Nat := 118140960795 + 2317023 * 2 ^ 59
def prefixEnd_2317023 : Nat := 4983230072969 + 3 ^ 40 * 2317023 * 2
def baseEnd_2317023 : Nat := 793164324348395580371141

theorem tailTrace_2317023 : CollatzResearch.WordTrace tailWord_2317023 prefixEnd_2317023 793164324348395580371141 := by
  unfold tailWord_2317023
  simp only [CollatzResearch.WordTrace]
  refine ⟨84508771484828861868947723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56339180989885907912631815 84508771484828861868947723)
  ·
    refine ⟨126763157227243292803421585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84508771484828861868947723 126763157227243292803421585)
    ·
      refine ⟨95072367920432469602566189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126763157227243292803421585 95072367920432469602566189)
      ·
        refine ⟨35652137970162176100962321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95072367920432469602566189 35652137970162176100962321)
        ·
          refine ⟨26739103477621632075721741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35652137970162176100962321 26739103477621632075721741)
          ·
            refine ⟨10027163804108112028395653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26739103477621632075721741 10027163804108112028395653)
            ·
              refine ⟨1880093213270271005324185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10027163804108112028395653 1880093213270271005324185)
              ·
                refine ⟨1410069909952703253993139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880093213270271005324185 1410069909952703253993139)
                ·
                  refine ⟨2115104864929054880989709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410069909952703253993139 2115104864929054880989709)
                  ·
                    refine ⟨793164324348395580371141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115104864929054880989709 793164324348395580371141)
                    ·
                      rfl

theorem cell22_2317023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_2317023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317023 prefixEnd_2317023 := by exact prefixLift 2317023
  have htrace : WordTrace (prefixWord ++ tailWord_2317023) baseStart_2317023 baseEnd_2317023 := by
    simpa [prefixWord, tailWord_2317023, baseEnd_2317023] using wordTrace_append hprefix tailTrace_2317023
  have hstable : (prefixWord ++ tailWord_2317023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317023).length < 2 ^ (prefixWord ++ tailWord_2317023).sum := by decide
  have hdescent : baseEnd_2317023 < baseStart_2317023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317109 : List Nat := [1, 3, 3, 1, 3, 2, 1, 8]
def baseStart_2317109 : Nat := 118140960795 + 2317109 * 2 ^ 59
def prefixEnd_2317109 : Nat := 4983230072969 + 3 ^ 40 * 2317109 * 2
def baseEnd_2317109 : Nat := 88132640433991113635653

theorem tailTrace_2317109 : CollatzResearch.WordTrace tailWord_2317109 prefixEnd_2317109 88132640433991113635653 := by
  unfold tailWord_2317109
  simp only [CollatzResearch.WordTrace]
  refine ⟨84511908162517298556578381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56341272108344865704385587 84511908162517298556578381)
  ·
    refine ⟨31691965560943986958716893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84511908162517298556578381 31691965560943986958716893)
    ·
      refine ⟨11884487085353995109518835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31691965560943986958716893 11884487085353995109518835)
      ·
        refine ⟨17826730628030992664278253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11884487085353995109518835 17826730628030992664278253)
        ·
          refine ⟨6685023985511622249104345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17826730628030992664278253 6685023985511622249104345)
          ·
            refine ⟨5013767989133716686828259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6685023985511622249104345 5013767989133716686828259)
            ·
              refine ⟨7520651983700575030242389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013767989133716686828259 7520651983700575030242389)
              ·
                refine ⟨88132640433991113635653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7520651983700575030242389 88132640433991113635653)
                ·
                  rfl

theorem cell22_2317109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 8].length) (baseStart_2317109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317109 prefixEnd_2317109 := by exact prefixLift 2317109
  have htrace : WordTrace (prefixWord ++ tailWord_2317109) baseStart_2317109 baseEnd_2317109 := by
    simpa [prefixWord, tailWord_2317109, baseEnd_2317109] using wordTrace_append hprefix tailTrace_2317109
  have hstable : (prefixWord ++ tailWord_2317109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317109).length < 2 ^ (prefixWord ++ tailWord_2317109).sum := by decide
  have hdescent : baseEnd_2317109 < baseStart_2317109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317192 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 1, 3]
def baseStart_2317192 : Nat := 118140960795 + 2317192 * 2 ^ 59
def prefixEnd_2317192 : Nat := 4983230072969 + 3 ^ 40 * 2317192 * 2
def baseEnd_2317192 : Nat := 793222176502135472895623

theorem tailTrace_2317192 : CollatzResearch.WordTrace tailWord_2317192 prefixEnd_2317192 793222176502135472895623 := by
  unfold tailWord_2317192
  simp only [CollatzResearch.WordTrace]
  refine ⟨42257467710608301865924915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56343290280811069154566553 42257467710608301865924915)
  ·
    refine ⟨63386201565912452798887373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42257467710608301865924915 63386201565912452798887373)
    ·
      refine ⟨23769825587217169799582765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63386201565912452798887373 23769825587217169799582765)
      ·
        refine ⟨8913684595206438674843537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23769825587217169799582765 8913684595206438674843537)
        ·
          refine ⟨6685263446404829006132653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8913684595206438674843537 6685263446404829006132653)
          ·
            refine ⟨2506973792401810877299745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6685263446404829006132653 2506973792401810877299745)
            ·
              refine ⟨1880230344301358157974809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506973792401810877299745 1880230344301358157974809)
              ·
                refine ⟨1410172758226018618481107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880230344301358157974809 1410172758226018618481107)
                ·
                  refine ⟨2115259137339027927721661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410172758226018618481107 2115259137339027927721661)
                  ·
                    refine ⟨793222176502135472895623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115259137339027927721661 793222176502135472895623)
                    ·
                      rfl

theorem cell22_2317192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_2317192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317192 prefixEnd_2317192 := by exact prefixLift 2317192
  have htrace : WordTrace (prefixWord ++ tailWord_2317192) baseStart_2317192 baseEnd_2317192 := by
    simpa [prefixWord, tailWord_2317192, baseEnd_2317192] using wordTrace_append hprefix tailTrace_2317192
  have hstable : (prefixWord ++ tailWord_2317192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317192).length < 2 ^ (prefixWord ++ tailWord_2317192).sum := by decide
  have hdescent : baseEnd_2317192 < baseStart_2317192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317246 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2317246 : Nat := 118140960795 + 2317246 * 2 ^ 59
def prefixEnd_2317246 : Nat := 4983230072969 + 3 ^ 40 * 2317246 * 2
def baseEnd_2317246 : Nat := 793240661805697332045457

theorem tailTrace_2317246 : CollatzResearch.WordTrace tailWord_2317246 prefixEnd_2317246 793240661805697332045457 := by
  unfold tailWord_2317246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564613120377621369289449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56344603308680647302877061 10564613120377621369289449)
  ·
    refine ⟨7923459840283216026967087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10564613120377621369289449 7923459840283216026967087)
    ·
      refine ⟨11885189760424824040450631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7923459840283216026967087 11885189760424824040450631)
      ·
        refine ⟨17827784640637236060675947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11885189760424824040450631 17827784640637236060675947)
        ·
          refine ⟨26741676960955854091013921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17827784640637236060675947 26741676960955854091013921)
          ·
            refine ⟨20056257720716890568260441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26741676960955854091013921 20056257720716890568260441)
            ·
              refine ⟨15042193290537667926195331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20056257720716890568260441 15042193290537667926195331)
              ·
                refine ⟨22563289935806501889292997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15042193290537667926195331 22563289935806501889292997)
                ·
                  refine ⟨4230616862963719104242437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22563289935806501889292997 4230616862963719104242437)
                  ·
                    refine ⟨793240661805697332045457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4230616862963719104242437 793240661805697332045457)
                    ·
                      rfl

theorem cell22_2317246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2317246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317246 prefixEnd_2317246 := by exact prefixLift 2317246
  have htrace : WordTrace (prefixWord ++ tailWord_2317246) baseStart_2317246 baseEnd_2317246 := by
    simpa [prefixWord, tailWord_2317246, baseEnd_2317246] using wordTrace_append hprefix tailTrace_2317246
  have hstable : (prefixWord ++ tailWord_2317246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317246).length < 2 ^ (prefixWord ++ tailWord_2317246).sum := by decide
  have hdescent : baseEnd_2317246 < baseStart_2317246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317248 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_2317248 : Nat := 118140960795 + 2317248 * 2 ^ 59
def prefixEnd_2317248 : Nat := 4983230072969 + 3 ^ 40 * 2317248 * 2
def baseEnd_2317248 : Nat := 793241346446569993495451

theorem tailTrace_2317248 : CollatzResearch.WordTrace tailWord_2317248 prefixEnd_2317248 793241346446569993495451 := by
  unfold tailWord_2317248
  simp only [CollatzResearch.WordTrace]
  refine ⟨42258488954506862647944199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56344651939342483530592265 42258488954506862647944199)
  ·
    refine ⟨63387733431760293971916299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42258488954506862647944199 63387733431760293971916299)
    ·
      refine ⟨95081600147640440957874449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63387733431760293971916299 95081600147640440957874449)
      ·
        refine ⟨71311200110730330718405837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95081600147640440957874449 71311200110730330718405837)
        ·
          refine ⟨26741700041523874019402189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71311200110730330718405837 26741700041523874019402189)
          ·
            refine ⟨10028137515571452757275821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26741700041523874019402189 10028137515571452757275821)
            ·
              refine ⟨3760551568339294783978433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10028137515571452757275821 3760551568339294783978433)
              ·
                refine ⟨2820413676254471087983825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3760551568339294783978433 2820413676254471087983825)
                ·
                  refine ⟨2115310257190853315987869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820413676254471087983825 2115310257190853315987869)
                  ·
                    refine ⟨793241346446569993495451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115310257190853315987869 793241346446569993495451)
                    ·
                      rfl

theorem cell22_2317248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_2317248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317248 prefixEnd_2317248 := by exact prefixLift 2317248
  have htrace : WordTrace (prefixWord ++ tailWord_2317248) baseStart_2317248 baseEnd_2317248 := by
    simpa [prefixWord, tailWord_2317248, baseEnd_2317248] using wordTrace_append hprefix tailTrace_2317248
  have hstable : (prefixWord ++ tailWord_2317248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317248).length < 2 ^ (prefixWord ++ tailWord_2317248).sum := by decide
  have hdescent : baseEnd_2317248 < baseStart_2317248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317323 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 5]
def baseStart_2317323 : Nat := 118140960795 + 2317323 * 2 ^ 59
def prefixEnd_2317323 : Nat := 4983230072969 + 3 ^ 40 * 2317323 * 2
def baseEnd_2317323 : Nat := 264422340159764932623407

theorem tailTrace_2317323 : CollatzResearch.WordTrace tailWord_2317323 prefixEnd_2317323 264422340159764932623407 := by
  unfold tailWord_2317323
  simp only [CollatzResearch.WordTrace]
  refine ⟨84519713383742013104868623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56346475589161342069912415 84519713383742013104868623)
  ·
    refine ⟨126779570075613019657302935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84519713383742013104868623 126779570075613019657302935)
    ·
      refine ⟨190169355113419529485954403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126779570075613019657302935 190169355113419529485954403)
      ·
        refine ⟨285254032670129294228931605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190169355113419529485954403 285254032670129294228931605)
        ·
          refine ⟨13371282781412310666981169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285254032670129294228931605 13371282781412310666981169)
          ·
            refine ⟨10028462086059233000235877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13371282781412310666981169 10028462086059233000235877)
            ·
              refine ⟨1880336641136106187544227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10028462086059233000235877 1880336641136106187544227)
              ·
                refine ⟨2820504961704159281316341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880336641136106187544227 2820504961704159281316341)
                ·
                  refine ⟨264422340159764932623407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820504961704159281316341 264422340159764932623407)
                  ·
                    rfl

theorem cell22_2317323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 5].length) (baseStart_2317323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317323 prefixEnd_2317323 := by exact prefixLift 2317323
  have htrace : WordTrace (prefixWord ++ tailWord_2317323) baseStart_2317323 baseEnd_2317323 := by
    simpa [prefixWord, tailWord_2317323, baseEnd_2317323] using wordTrace_append hprefix tailTrace_2317323
  have hstable : (prefixWord ++ tailWord_2317323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317323).length < 2 ^ (prefixWord ++ tailWord_2317323).sum := by decide
  have hdescent : baseEnd_2317323 < baseStart_2317323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317381 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2317381 : Nat := 118140960795 + 2317381 * 2 ^ 59
def prefixEnd_2317381 : Nat := 4983230072969 + 3 ^ 40 * 2317381 * 2
def baseEnd_2317381 : Nat := 793286875064601979920043

theorem tailTrace_2317381 : CollatzResearch.WordTrace tailWord_2317381 prefixEnd_2317381 793286875064601979920043 := by
  unfold tailWord_2317381
  simp only [CollatzResearch.WordTrace]
  refine ⟨84521828817531889010479997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56347885878354592673653331 84521828817531889010479997)
  ·
    refine ⟨31695685806574458378929999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84521828817531889010479997 31695685806574458378929999)
    ·
      refine ⟨47543528709861687568394999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31695685806574458378929999 47543528709861687568394999)
      ·
        refine ⟨71315293064792531352592499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47543528709861687568394999 71315293064792531352592499)
        ·
          refine ⟨106972939597188797028888749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71315293064792531352592499 106972939597188797028888749)
          ·
            refine ⟨40114852348945798885833281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106972939597188797028888749 40114852348945798885833281)
            ·
              refine ⟨30086139261709349164374961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40114852348945798885833281 30086139261709349164374961)
              ·
                refine ⟨22564604446282011873281221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30086139261709349164374961 22564604446282011873281221)
                ·
                  refine ⟨4230863333677877226240229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22564604446282011873281221 4230863333677877226240229)
                  ·
                    refine ⟨793286875064601979920043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4230863333677877226240229 793286875064601979920043)
                    ·
                      rfl

theorem cell22_2317381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2317381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317381 prefixEnd_2317381 := by exact prefixLift 2317381
  have htrace : WordTrace (prefixWord ++ tailWord_2317381) baseStart_2317381 baseEnd_2317381 := by
    simpa [prefixWord, tailWord_2317381, baseEnd_2317381] using wordTrace_append hprefix tailTrace_2317381
  have hstable : (prefixWord ++ tailWord_2317381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317381).length < 2 ^ (prefixWord ++ tailWord_2317381).sum := by decide
  have hdescent : baseEnd_2317381 < baseStart_2317381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317383 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2317383 : Nat := 118140960795 + 2317383 * 2 ^ 59
def prefixEnd_2317383 : Nat := 4983230072969 + 3 ^ 40 * 2317383 * 2
def baseEnd_2317383 : Nat := 793287559705474641370037

theorem tailTrace_2317383 : CollatzResearch.WordTrace tailWord_2317383 prefixEnd_2317383 793287559705474641370037 := by
  unfold tailWord_2317383
  simp only [CollatzResearch.WordTrace]
  refine ⟨84521901763524643352052803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56347934509016428901368535 84521901763524643352052803)
  ·
    refine ⟨126782852645286965028079205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84521901763524643352052803 126782852645286965028079205)
    ·
      refine ⟨23771784870991305942764851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126782852645286965028079205 23771784870991305942764851)
      ·
        refine ⟨35657677306486958914147277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23771784870991305942764851 35657677306486958914147277)
        ·
          refine ⟨13371628989932609592805229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35657677306486958914147277 13371628989932609592805229)
          ·
            refine ⟨5014360871224728597301961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13371628989932609592805229 5014360871224728597301961)
            ·
              refine ⟨3760770653418546447976471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5014360871224728597301961 3760770653418546447976471)
              ·
                refine ⟨5641155980127819671964707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760770653418546447976471 5641155980127819671964707)
                ·
                  refine ⟨8461733970191729507947061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641155980127819671964707 8461733970191729507947061)
                  ·
                    refine ⟨793287559705474641370037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8461733970191729507947061 793287559705474641370037)
                    ·
                      rfl

theorem cell22_2317383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2317383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317383 prefixEnd_2317383 := by exact prefixLift 2317383
  have htrace : WordTrace (prefixWord ++ tailWord_2317383) baseStart_2317383 baseEnd_2317383 := by
    simpa [prefixWord, tailWord_2317383, baseEnd_2317383] using wordTrace_append hprefix tailTrace_2317383
  have hstable : (prefixWord ++ tailWord_2317383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317383).length < 2 ^ (prefixWord ++ tailWord_2317383).sum := by decide
  have hdescent : baseEnd_2317383 < baseStart_2317383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317396 : List Nat := [2, 4, 1, 1, 1, 1, 2, 10]
def baseStart_2317396 : Nat := 118140960795 + 2317396 * 2 ^ 59
def prefixEnd_2317396 : Nat := 4983230072969 + 3 ^ 40 * 2317396 * 2
def baseEnd_2317396 : Nat := 88143556652349660088333

theorem tailTrace_2317396 : CollatzResearch.WordTrace tailWord_2317396 prefixEnd_2317396 88143556652349660088333 := by
  unfold tailWord_2317396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42261187956238773286138021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56348250608318364381517361 42261187956238773286138021)
  ·
    refine ⟨7923972741794769991150879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42261187956238773286138021 7923972741794769991150879)
    ·
      refine ⟨11885959112692154986726319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7923972741794769991150879 11885959112692154986726319)
      ·
        refine ⟨17828938669038232480089479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11885959112692154986726319 17828938669038232480089479)
        ·
          refine ⟨26743408003557348720134219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17828938669038232480089479 26743408003557348720134219)
          ·
            refine ⟨40115112005336023080201329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26743408003557348720134219 40115112005336023080201329)
            ·
              refine ⟨30086334004002017310150997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40115112005336023080201329 30086334004002017310150997)
              ·
                refine ⟨88143556652349660088333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30086334004002017310150997 88143556652349660088333)
                ·
                  rfl

theorem cell22_2317396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_2317396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317396 prefixEnd_2317396 := by exact prefixLift 2317396
  have htrace : WordTrace (prefixWord ++ tailWord_2317396) baseStart_2317396 baseEnd_2317396 := by
    simpa [prefixWord, tailWord_2317396, baseEnd_2317396] using wordTrace_append hprefix tailTrace_2317396
  have hstable : (prefixWord ++ tailWord_2317396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317396).length < 2 ^ (prefixWord ++ tailWord_2317396).sum := by decide
  have hdescent : baseEnd_2317396 < baseStart_2317396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317456 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_2317456 : Nat := 118140960795 + 2317456 * 2 ^ 59
def prefixEnd_2317456 : Nat := 4983230072969 + 3 ^ 40 * 2317456 * 2
def baseEnd_2317456 : Nat := 793312549097326784294813

theorem tailTrace_2317456 : CollatzResearch.WordTrace tailWord_2317456 prefixEnd_2317456 793312549097326784294813 := by
  unfold tailWord_2317456
  simp only [CollatzResearch.WordTrace]
  refine ⟨42262282146130088409730111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56349709528173451212973481 42262282146130088409730111)
  ·
    refine ⟨63393423219195132614595167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42262282146130088409730111 63393423219195132614595167)
    ·
      refine ⟨95090134828792698921892751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63393423219195132614595167 95090134828792698921892751)
      ·
        refine ⟨142635202243189048382839127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95090134828792698921892751 142635202243189048382839127)
        ·
          refine ⟨213952803364783572574258691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142635202243189048382839127 213952803364783572574258691)
          ·
            refine ⟨320929205047175358861388037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213952803364783572574258691 320929205047175358861388037)
            ·
              refine ⟨60174225946345379786510257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320929205047175358861388037 60174225946345379786510257)
              ·
                refine ⟨45130669459759034839882693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60174225946345379786510257 45130669459759034839882693)
                ·
                  refine ⟨8462000523704819032478005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45130669459759034839882693 8462000523704819032478005)
                  ·
                    refine ⟨793312549097326784294813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8462000523704819032478005 793312549097326784294813)
                    ·
                      rfl

theorem cell22_2317456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_2317456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317456 prefixEnd_2317456 := by exact prefixLift 2317456
  have htrace : WordTrace (prefixWord ++ tailWord_2317456) baseStart_2317456 baseEnd_2317456 := by
    simpa [prefixWord, tailWord_2317456, baseEnd_2317456] using wordTrace_append hprefix tailTrace_2317456
  have hstable : (prefixWord ++ tailWord_2317456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317456).length < 2 ^ (prefixWord ++ tailWord_2317456).sum := by decide
  have hdescent : baseEnd_2317456 < baseStart_2317456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317458 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_2317458 : Nat := 118140960795 + 2317458 * 2 ^ 59
def prefixEnd_2317458 : Nat := 4983230072969 + 3 ^ 40 * 2317458 * 2
def baseEnd_2317458 : Nat := 264437744579399815248269

theorem tailTrace_2317458 : CollatzResearch.WordTrace tailWord_2317458 prefixEnd_2317458 264437744579399815248269 := by
  unfold tailWord_2317458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21131159309563232790258257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56349758158835287440688685 21131159309563232790258257)
  ·
    refine ⟨15848369482172424592693693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21131159309563232790258257 15848369482172424592693693)
    ·
      refine ⟨5943138555814659222260135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15848369482172424592693693 5943138555814659222260135)
      ·
        refine ⟨8914707833721988833390203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5943138555814659222260135 8914707833721988833390203)
        ·
          refine ⟨13372061750582983250085305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8914707833721988833390203 13372061750582983250085305)
          ·
            refine ⟨10029046312937237437563979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13372061750582983250085305 10029046312937237437563979)
            ·
              refine ⟨15043569469405856156345969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10029046312937237437563979 15043569469405856156345969)
              ·
                refine ⟨11282677102054392117259477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15043569469405856156345969 11282677102054392117259477)
                ·
                  refine ⟨264437744579399815248269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11282677102054392117259477 264437744579399815248269)
                  ·
                    rfl

theorem cell22_2317458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_2317458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317458 prefixEnd_2317458 := by exact prefixLift 2317458
  have htrace : WordTrace (prefixWord ++ tailWord_2317458) baseStart_2317458 baseEnd_2317458 := by
    simpa [prefixWord, tailWord_2317458, baseEnd_2317458] using wordTrace_append hprefix tailTrace_2317458
  have hstable : (prefixWord ++ tailWord_2317458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317458).length < 2 ^ (prefixWord ++ tailWord_2317458).sum := by decide
  have hdescent : baseEnd_2317458 < baseStart_2317458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317522 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2317522 : Nat := 118140960795 + 2317522 * 2 ^ 59
def prefixEnd_2317522 : Nat := 4983230072969 + 3 ^ 40 * 2317522 * 2
def baseEnd_2317522 : Nat := 793335142246124612144611

theorem tailTrace_2317522 : CollatzResearch.WordTrace tailWord_2317522 prefixEnd_2317522 793335142246124612144611 := by
  unfold tailWord_2317522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21131742877505267522840705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56351314340014046727575213 21131742877505267522840705)
  ·
    refine ⟨15848807158128950642130529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21131742877505267522840705 15848807158128950642130529)
    ·
      refine ⟨11886605368596712981597897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15848807158128950642130529 11886605368596712981597897)
      ·
        refine ⟨8914954026447534736198423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11886605368596712981597897 8914954026447534736198423)
        ·
          refine ⟨13372431039671302104297635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8914954026447534736198423 13372431039671302104297635)
          ·
            refine ⟨20058646559506953156446453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13372431039671302104297635 20058646559506953156446453)
            ·
              refine ⟨1880498114953776858416855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20058646559506953156446453 1880498114953776858416855)
              ·
                refine ⟨2820747172430665287625283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880498114953776858416855 2820747172430665287625283)
                ·
                  refine ⟨4231120758645997931437925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820747172430665287625283 4231120758645997931437925)
                  ·
                    refine ⟨793335142246124612144611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231120758645997931437925 793335142246124612144611)
                    ·
                      rfl

theorem cell22_2317522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2317522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317522 prefixEnd_2317522 := by exact prefixLift 2317522
  have htrace : WordTrace (prefixWord ++ tailWord_2317522) baseStart_2317522 baseEnd_2317522 := by
    simpa [prefixWord, tailWord_2317522, baseEnd_2317522] using wordTrace_append hprefix tailTrace_2317522
  have hstable : (prefixWord ++ tailWord_2317522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317522).length < 2 ^ (prefixWord ++ tailWord_2317522).sum := by decide
  have hdescent : baseEnd_2317522 < baseStart_2317522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317535 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 2, 3]
def baseStart_2317535 : Nat := 118140960795 + 2317535 * 2 ^ 59
def prefixEnd_2317535 : Nat := 4983230072969 + 3 ^ 40 * 2317535 * 2
def baseEnd_2317535 : Nat := 793339592411796911569571

theorem tailTrace_2317535 : CollatzResearch.WordTrace tailWord_2317535 prefixEnd_2317535 793339592411796911569571 := by
  unfold tailWord_2317535
  simp only [CollatzResearch.WordTrace]
  refine ⟨84527445658973973311586059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56351630439315982207724039 84527445658973973311586059)
  ·
    refine ⟨126791168488460959967379089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84527445658973973311586059 126791168488460959967379089)
    ·
      refine ⟨95093376366345719975534317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126791168488460959967379089 95093376366345719975534317)
      ·
        refine ⟨35660016137379644990825369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95093376366345719975534317 35660016137379644990825369)
        ·
          refine ⟨26745012103034733743119027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35660016137379644990825369 26745012103034733743119027)
          ·
            refine ⟨40117518154552100614678541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26745012103034733743119027 40117518154552100614678541)
            ·
              refine ⟨15044069307957037730504453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40117518154552100614678541 15044069307957037730504453)
              ·
                refine ⟨2820762995241944574469585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15044069307957037730504453 2820762995241944574469585)
                ·
                  refine ⟨2115572246431458430852189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820762995241944574469585 2115572246431458430852189)
                  ·
                    refine ⟨793339592411796911569571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115572246431458430852189 793339592411796911569571)
                    ·
                      rfl

theorem cell22_2317535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_2317535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317535 prefixEnd_2317535 := by exact prefixLift 2317535
  have htrace : WordTrace (prefixWord ++ tailWord_2317535) baseStart_2317535 baseEnd_2317535 := by
    simpa [prefixWord, tailWord_2317535, baseEnd_2317535] using wordTrace_append hprefix tailTrace_2317535
  have hstable : (prefixWord ++ tailWord_2317535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317535).length < 2 ^ (prefixWord ++ tailWord_2317535).sum := by decide
  have hdescent : baseEnd_2317535 < baseStart_2317535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317537 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 4]
def baseStart_2317537 : Nat := 118140960795 + 2317537 * 2 ^ 59
def prefixEnd_2317537 : Nat := 4983230072969 + 3 ^ 40 * 2317537 * 2
def baseEnd_2317537 : Nat := 264446759017556524339855

theorem tailTrace_2317537 : CollatzResearch.WordTrace tailWord_2317537 prefixEnd_2317537 264446759017556524339855 := by
  unfold tailWord_2317537
  simp only [CollatzResearch.WordTrace]
  refine ⟨84527518604966727653158865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56351679069977818435439243 84527518604966727653158865)
  ·
    refine ⟨63395638953725045739869149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84527518604966727653158865 63395638953725045739869149)
    ·
      refine ⟨23773364607646892152450931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63395638953725045739869149 23773364607646892152450931)
      ·
        refine ⟨35660046911470338228676397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23773364607646892152450931 35660046911470338228676397)
        ·
          refine ⟨13372517591801376835753649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35660046911470338228676397 13372517591801376835753649)
          ·
            refine ⟨10029388193851032626815237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13372517591801376835753649 10029388193851032626815237)
            ·
              refine ⟨1880510286347068617527857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10029388193851032626815237 1880510286347068617527857)
              ·
                refine ⟨1410382714760301463145893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880510286347068617527857 1410382714760301463145893)
                ·
                  refine ⟨264446759017556524339855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410382714760301463145893 264446759017556524339855)
                  ·
                    rfl

theorem cell22_2317537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_2317537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317537 prefixEnd_2317537 := by exact prefixLift 2317537
  have htrace : WordTrace (prefixWord ++ tailWord_2317537) baseStart_2317537 baseEnd_2317537 := by
    simpa [prefixWord, tailWord_2317537, baseEnd_2317537] using wordTrace_append hprefix tailTrace_2317537
  have hstable : (prefixWord ++ tailWord_2317537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317537).length < 2 ^ (prefixWord ++ tailWord_2317537).sum := by decide
  have hdescent : baseEnd_2317537 < baseStart_2317537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317548 : List Nat := [2, 2, 1, 1, 2, 4, 3, 7]
def baseStart_2317548 : Nat := 118140960795 + 2317548 * 2 ^ 59
def prefixEnd_2317548 : Nat := 4983230072969 + 3 ^ 40 * 2317548 * 2
def baseEnd_2317548 : Nat := 88149338064163245666059

theorem tailTrace_2317548 : CollatzResearch.WordTrace tailWord_2317548 prefixEnd_2317548 88149338064163245666059 := by
  unfold tailWord_2317548
  simp only [CollatzResearch.WordTrace]
  refine ⟨42263959903963438265904649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56351946538617917687872865 42263959903963438265904649)
  ·
    refine ⟨31697969927972578699428487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42263959903963438265904649 31697969927972578699428487)
    ·
      refine ⟨47546954891958868049142731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31697969927972578699428487 47546954891958868049142731)
      ·
        refine ⟨71320432337938302073714097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47546954891958868049142731 71320432337938302073714097)
        ·
          refine ⟨53490324253453726555285573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71320432337938302073714097 53490324253453726555285573)
          ·
            refine ⟨10029435797522573729116045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53490324253453726555285573 10029435797522573729116045)
            ·
              refine ⟨3761038424070965148418517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10029435797522573729116045 3761038424070965148418517)
              ·
                refine ⟨88149338064163245666059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3761038424070965148418517 88149338064163245666059)
                ·
                  rfl

theorem cell22_2317548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_2317548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317548 prefixEnd_2317548 := by exact prefixLift 2317548
  have htrace : WordTrace (prefixWord ++ tailWord_2317548) baseStart_2317548 baseEnd_2317548 := by
    simpa [prefixWord, tailWord_2317548, baseEnd_2317548] using wordTrace_append hprefix tailTrace_2317548
  have hstable : (prefixWord ++ tailWord_2317548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317548).length < 2 ^ (prefixWord ++ tailWord_2317548).sum := by decide
  have hdescent : baseEnd_2317548 < baseStart_2317548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317597 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_2317597 : Nat := 118140960795 + 2317597 * 2 ^ 59
def prefixEnd_2317597 : Nat := 4983230072969 + 3 ^ 40 * 2317597 * 2
def baseEnd_2317597 : Nat := 793360816278849416519381

theorem tailTrace_2317597 : CollatzResearch.WordTrace tailWord_2317597 prefixEnd_2317597 793360816278849416519381 := by
  unfold tailWord_2317597
  simp only [CollatzResearch.WordTrace]
  refine ⟨84529706984749357900343045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56353137989832905266895363 84529706984749357900343045)
  ·
    refine ⟨15849320059640504606314321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84529706984749357900343045 15849320059640504606314321)
    ·
      refine ⟨11886990044730378454735741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15849320059640504606314321 11886990044730378454735741)
      ·
        refine ⟨4457621266773891920525903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11886990044730378454735741 4457621266773891920525903)
        ·
          refine ⟨6686431900160837880788855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457621266773891920525903 6686431900160837880788855)
          ·
            refine ⟨10029647850241256821183283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686431900160837880788855 10029647850241256821183283)
            ·
              refine ⟨15044471775361885231774925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10029647850241256821183283 15044471775361885231774925)
              ·
                refine ⟨5641676915760706961915597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15044471775361885231774925 5641676915760706961915597)
                ·
                  refine ⟨2115628843410265110718349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5641676915760706961915597 2115628843410265110718349)
                  ·
                    refine ⟨793360816278849416519381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115628843410265110718349 793360816278849416519381)
                    ·
                      rfl

theorem cell22_2317597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_2317597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317597 prefixEnd_2317597 := by exact prefixLift 2317597
  have htrace : WordTrace (prefixWord ++ tailWord_2317597) baseStart_2317597 baseEnd_2317597 := by
    simpa [prefixWord, tailWord_2317597, baseEnd_2317597] using wordTrace_append hprefix tailTrace_2317597
  have hstable : (prefixWord ++ tailWord_2317597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317597).length < 2 ^ (prefixWord ++ tailWord_2317597).sum := by decide
  have hdescent : baseEnd_2317597 < baseStart_2317597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317655 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 6]
def baseStart_2317655 : Nat := 118140960795 + 2317655 * 2 ^ 59
def prefixEnd_2317655 : Nat := 4983230072969 + 3 ^ 40 * 2317655 * 2
def baseEnd_2317655 : Nat := 264460223621385532856401

theorem tailTrace_2317655 : CollatzResearch.WordTrace tailWord_2317655 prefixEnd_2317655 264460223621385532856401 := by
  unfold tailWord_2317655
  simp only [CollatzResearch.WordTrace]
  refine ⟨84531822418539233805954419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56354548279026155870636279 84531822418539233805954419)
  ·
    refine ⟨126797733627808850708931629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84531822418539233805954419 126797733627808850708931629)
    ·
      refine ⟨47549150110428319015849361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126797733627808850708931629 47549150110428319015849361)
      ·
        refine ⟨35661862582821239261887021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47549150110428319015849361 35661862582821239261887021)
        ·
          refine ⟨13373198468557964723207633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35661862582821239261887021 13373198468557964723207633)
          ·
            refine ⟨10029898851418473542405725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13373198468557964723207633 10029898851418473542405725)
            ·
              refine ⟨3761212069281927578402147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10029898851418473542405725 3761212069281927578402147)
              ·
                refine ⟨5641818103922891367603221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761212069281927578402147 5641818103922891367603221)
                ·
                  refine ⟨264460223621385532856401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5641818103922891367603221 264460223621385532856401)
                  ·
                    rfl

theorem cell22_2317655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 6].length) (baseStart_2317655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317655 prefixEnd_2317655 := by exact prefixLift 2317655
  have htrace : WordTrace (prefixWord ++ tailWord_2317655) baseStart_2317655 baseEnd_2317655 := by
    simpa [prefixWord, tailWord_2317655, baseEnd_2317655] using wordTrace_append hprefix tailTrace_2317655
  have hstable : (prefixWord ++ tailWord_2317655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317655).length < 2 ^ (prefixWord ++ tailWord_2317655).sum := by decide
  have hdescent : baseEnd_2317655 < baseStart_2317655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317661 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 5]
def baseStart_2317661 : Nat := 118140960795 + 2317661 * 2 ^ 59
def prefixEnd_2317661 : Nat := 4983230072969 + 3 ^ 40 * 2317661 * 2
def baseEnd_2317661 : Nat := 264460908262258194306395

theorem tailTrace_2317661 : CollatzResearch.WordTrace tailWord_2317661 prefixEnd_2317661 264460908262258194306395 := by
  unfold tailWord_2317661
  simp only [CollatzResearch.WordTrace]
  refine ⟨84532041256517496830672837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56354694171011664553781891 84532041256517496830672837)
  ·
    refine ⟨15849757735597030655751157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84532041256517496830672837 15849757735597030655751157)
    ·
      refine ⟨1485914787712221623976671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15849757735597030655751157 1485914787712221623976671)
      ·
        refine ⟨2228872181568332435965007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485914787712221623976671 2228872181568332435965007)
        ·
          refine ⟨3343308272352498653947511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228872181568332435965007 3343308272352498653947511)
          ·
            refine ⟨5014962408528747980921267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343308272352498653947511 5014962408528747980921267)
            ·
              refine ⟨7522443612793121971381901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014962408528747980921267 7522443612793121971381901)
              ·
                refine ⟨2820916354797420739268213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7522443612793121971381901 2820916354797420739268213)
                ·
                  refine ⟨264460908262258194306395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820916354797420739268213 264460908262258194306395)
                  ·
                    rfl

theorem cell22_2317661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_2317661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317661 prefixEnd_2317661 := by exact prefixLift 2317661
  have htrace : WordTrace (prefixWord ++ tailWord_2317661) baseStart_2317661 baseEnd_2317661 := by
    simpa [prefixWord, tailWord_2317661, baseEnd_2317661] using wordTrace_append hprefix tailTrace_2317661
  have hstable : (prefixWord ++ tailWord_2317661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317661).length < 2 ^ (prefixWord ++ tailWord_2317661).sum := by decide
  have hdescent : baseEnd_2317661 < baseStart_2317661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317704 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2317704 : Nat := 118140960795 + 2317704 * 2 ^ 59
def prefixEnd_2317704 : Nat := 4983230072969 + 3 ^ 40 * 2317704 * 2
def baseEnd_2317704 : Nat := 793397444565536804094053

theorem tailTrace_2317704 : CollatzResearch.WordTrace tailWord_2317704 prefixEnd_2317704 793397444565536804094053 := by
  unfold tailWord_2317704
  simp only [CollatzResearch.WordTrace]
  refine ⟨42266804797680857587244083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56355739730241143449658777 42266804797680857587244083)
  ·
    refine ⟨63400207196521286380866125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42266804797680857587244083 63400207196521286380866125)
    ·
      refine ⟨23775077698695482392824797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63400207196521286380866125 23775077698695482392824797)
      ·
        refine ⟨8915654137010805897309299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23775077698695482392824797 8915654137010805897309299)
        ·
          refine ⟨13373481205516208845963949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8915654137010805897309299 13373481205516208845963949)
          ·
            refine ⟨5015055452068578317236481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13373481205516208845963949 5015055452068578317236481)
            ·
              refine ⟨3761291589051433737927361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5015055452068578317236481 3761291589051433737927361)
              ·
                refine ⟨2820968691788575303445521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761291589051433737927361 2820968691788575303445521)
                ·
                  refine ⟨2115726518841431477584141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820968691788575303445521 2115726518841431477584141)
                  ·
                    refine ⟨793397444565536804094053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115726518841431477584141 793397444565536804094053)
                    ·
                      rfl

theorem cell22_2317704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2317704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317704 prefixEnd_2317704 := by exact prefixLift 2317704
  have htrace : WordTrace (prefixWord ++ tailWord_2317704) baseStart_2317704 baseEnd_2317704 := by
    simpa [prefixWord, tailWord_2317704, baseEnd_2317704] using wordTrace_append hprefix tailTrace_2317704
  have hstable : (prefixWord ++ tailWord_2317704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317704).length < 2 ^ (prefixWord ++ tailWord_2317704).sum := by decide
  have hdescent : baseEnd_2317704 < baseStart_2317704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317715 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 9, 3]
def baseStart_2317715 : Nat := 118140960795 + 2317715 * 2 ^ 59
def prefixEnd_2317715 : Nat := 4983230072969 + 3 ^ 40 * 2317715 * 2
def baseEnd_2317715 : Nat := 793401210090336442069019

theorem tailTrace_2317715 : CollatzResearch.WordTrace tailWord_2317715 prefixEnd_2317715 793401210090336442069019 := by
  unfold tailWord_2317715
  simp only [CollatzResearch.WordTrace]
  refine ⟨84534010798321864053138599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56356007198881242702092399 84534010798321864053138599)
  ·
    refine ⟨126801016197482796079707899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84534010798321864053138599 126801016197482796079707899)
    ·
      refine ⟨190201524296224194119561849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126801016197482796079707899 190201524296224194119561849)
      ·
        refine ⟨142651143222168145589671387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190201524296224194119561849 142651143222168145589671387)
        ·
          refine ⟨213976714833252218384507081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142651143222168145589671387 213976714833252218384507081)
          ·
            refine ⟨160482536124939163788380311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213976714833252218384507081 160482536124939163788380311)
            ·
              refine ⟨240723804187408745682570467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160482536124939163788380311 240723804187408745682570467)
              ·
                refine ⟨361085706281113118523855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240723804187408745682570467 361085706281113118523855701)
                ·
                  refine ⟨2115736560240897178850717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 361085706281113118523855701 2115736560240897178850717)
                  ·
                    refine ⟨793401210090336442069019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115736560240897178850717 793401210090336442069019)
                    ·
                      rfl

theorem cell22_2317715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3].length) (baseStart_2317715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317715 prefixEnd_2317715 := by exact prefixLift 2317715
  have htrace : WordTrace (prefixWord ++ tailWord_2317715) baseStart_2317715 baseEnd_2317715 := by
    simpa [prefixWord, tailWord_2317715, baseEnd_2317715] using wordTrace_append hprefix tailTrace_2317715
  have hstable : (prefixWord ++ tailWord_2317715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317715).length < 2 ^ (prefixWord ++ tailWord_2317715).sum := by decide
  have hdescent : baseEnd_2317715 < baseStart_2317715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317736 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2317736 : Nat := 118140960795 + 2317736 * 2 ^ 59
def prefixEnd_2317736 : Nat := 4983230072969 + 3 ^ 40 * 2317736 * 2
def baseEnd_2317736 : Nat := 793408398819499387293955

theorem tailTrace_2317736 : CollatzResearch.WordTrace tailWord_2317736 prefixEnd_2317736 793408398819499387293955 := by
  unfold tailWord_2317736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42267388365622892319826531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56356517820830523093102041 42267388365622892319826531)
  ·
    refine ⟨63401082548434338479739797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42267388365622892319826531 63401082548434338479739797)
    ·
      refine ⟨2971925744457859616237803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63401082548434338479739797 2971925744457859616237803)
      ·
        refine ⟨4457888616686789424356705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971925744457859616237803 4457888616686789424356705)
        ·
          refine ⟨3343416462515092068267529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4457888616686789424356705 3343416462515092068267529)
          ·
            refine ⟨2507562346886319051200647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343416462515092068267529 2507562346886319051200647)
            ·
              refine ⟨3761343520329478576800971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507562346886319051200647 3761343520329478576800971)
              ·
                refine ⟨5642015280494217865201457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761343520329478576800971 5642015280494217865201457)
                ·
                  refine ⟨4231511460370663398901093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5642015280494217865201457 4231511460370663398901093)
                  ·
                    refine ⟨793408398819499387293955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231511460370663398901093 793408398819499387293955)
                    ·
                      rfl

theorem cell22_2317736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2317736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317736 prefixEnd_2317736 := by exact prefixLift 2317736
  have htrace : WordTrace (prefixWord ++ tailWord_2317736) baseStart_2317736 baseEnd_2317736 := by
    simpa [prefixWord, tailWord_2317736, baseEnd_2317736] using wordTrace_append hprefix tailTrace_2317736
  have hstable : (prefixWord ++ tailWord_2317736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317736).length < 2 ^ (prefixWord ++ tailWord_2317736).sum := by decide
  have hdescent : baseEnd_2317736 < baseStart_2317736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317745 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 7]
def baseStart_2317745 : Nat := 118140960795 + 2317745 * 2 ^ 59
def prefixEnd_2317745 : Nat := 4983230072969 + 3 ^ 40 * 2317745 * 2
def baseEnd_2317745 : Nat := 264470493234475454606309

theorem tailTrace_2317745 : CollatzResearch.WordTrace tailWord_2317745 prefixEnd_2317745 264470493234475454606309 := by
  unfold tailWord_2317745
  simp only [CollatzResearch.WordTrace]
  refine ⟨84535104988213179176730689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56356736658808786117820459 84535104988213179176730689)
  ·
    refine ⟨63401328741159884382548017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84535104988213179176730689 63401328741159884382548017)
    ·
      refine ⟨47550996555869913286911013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63401328741159884382548017 47550996555869913286911013)
      ·
        refine ⟨8915811854225608741295815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47550996555869913286911013 8915811854225608741295815)
        ·
          refine ⟨13373717781338413111943723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8915811854225608741295815 13373717781338413111943723)
          ·
            refine ⟨20060576672007619667915585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13373717781338413111943723 20060576672007619667915585)
            ·
              refine ⟨15045432504005714750936689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20060576672007619667915585 15045432504005714750936689)
              ·
                refine ⟨11284074378004286063202517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15045432504005714750936689 11284074378004286063202517)
                ·
                  refine ⟨264470493234475454606309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11284074378004286063202517 264470493234475454606309)
                  ·
                    rfl

theorem cell22_2317745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_2317745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317745 prefixEnd_2317745 := by exact prefixLift 2317745
  have htrace : WordTrace (prefixWord ++ tailWord_2317745) baseStart_2317745 baseEnd_2317745 := by
    simpa [prefixWord, tailWord_2317745, baseEnd_2317745] using wordTrace_append hprefix tailTrace_2317745
  have hstable : (prefixWord ++ tailWord_2317745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317745).length < 2 ^ (prefixWord ++ tailWord_2317745).sum := by decide
  have hdescent : baseEnd_2317745 < baseStart_2317745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317760 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_2317760 : Nat := 118140960795 + 2317760 * 2 ^ 59
def prefixEnd_2317760 : Nat := 4983230072969 + 3 ^ 40 * 2317760 * 2
def baseEnd_2317760 : Nat := 793416614509971324693881

theorem tailTrace_2317760 : CollatzResearch.WordTrace tailWord_2317760 prefixEnd_2317760 793416614509971324693881 := by
  unfold tailWord_2317760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42267826041579418369263367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56357101388772557825684489 42267826041579418369263367)
  ·
    refine ⟨63401739062369127553895051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42267826041579418369263367 63401739062369127553895051)
    ·
      refine ⟨95102608593553691330842577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63401739062369127553895051 95102608593553691330842577)
      ·
        refine ⟨71326956445165268498131933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95102608593553691330842577 71326956445165268498131933)
        ·
          refine ⟨26747608666936975686799475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71326956445165268498131933 26747608666936975686799475)
          ·
            refine ⟨40121413000405463530199213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26747608666936975686799475 40121413000405463530199213)
            ·
              refine ⟨15045529875152048823824705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40121413000405463530199213 15045529875152048823824705)
              ·
                refine ⟨11284147406364036617868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15045529875152048823824705 11284147406364036617868529)
                ·
                  refine ⟨8463110554773027463401397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11284147406364036617868529 8463110554773027463401397)
                  ·
                    refine ⟨793416614509971324693881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8463110554773027463401397 793416614509971324693881)
                    ·
                      rfl

theorem cell22_2317760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_2317760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317760 prefixEnd_2317760 := by exact prefixLift 2317760
  have htrace : WordTrace (prefixWord ++ tailWord_2317760) baseStart_2317760 baseEnd_2317760 := by
    simpa [prefixWord, tailWord_2317760, baseEnd_2317760] using wordTrace_append hprefix tailTrace_2317760
  have hstable : (prefixWord ++ tailWord_2317760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317760).length < 2 ^ (prefixWord ++ tailWord_2317760).sum := by decide
  have hdescent : baseEnd_2317760 < baseStart_2317760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317775 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_2317775 : Nat := 118140960795 + 2317775 * 2 ^ 59
def prefixEnd_2317775 : Nat := 4983230072969 + 3 ^ 40 * 2317775 * 2
def baseEnd_2317775 : Nat := 793421749316516285568835

theorem tailTrace_2317775 : CollatzResearch.WordTrace tailWord_2317775 prefixEnd_2317775 793421749316516285568835 := by
  unfold tailWord_2317775
  simp only [CollatzResearch.WordTrace]
  refine ⟨84536199178104494300322779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56357466118736329533548519 84536199178104494300322779)
  ·
    refine ⟨126804298767156741450484169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84536199178104494300322779 126804298767156741450484169)
    ·
      refine ⟨95103224075367556087863127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126804298767156741450484169 95103224075367556087863127)
      ·
        refine ⟨142654836113051334131794691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95103224075367556087863127 142654836113051334131794691)
        ·
          refine ⟨213982254169577001197692037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142654836113051334131794691 213982254169577001197692037)
          ·
            refine ⟨40121672656795687724567257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213982254169577001197692037 40121672656795687724567257)
            ·
              refine ⟨30091254492596765793425443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40121672656795687724567257 30091254492596765793425443)
              ·
                refine ⟨45136881738895148690138165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30091254492596765793425443 45136881738895148690138165)
                ·
                  refine ⟨4231582663021420189700453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45136881738895148690138165 4231582663021420189700453)
                  ·
                    refine ⟨793421749316516285568835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231582663021420189700453 793421749316516285568835)
                    ·
                      rfl

theorem cell22_2317775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_2317775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317775 prefixEnd_2317775 := by exact prefixLift 2317775
  have htrace : WordTrace (prefixWord ++ tailWord_2317775) baseStart_2317775 baseEnd_2317775 := by
    simpa [prefixWord, tailWord_2317775, baseEnd_2317775] using wordTrace_append hprefix tailTrace_2317775
  have hstable : (prefixWord ++ tailWord_2317775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317775).length < 2 ^ (prefixWord ++ tailWord_2317775).sum := by decide
  have hdescent : baseEnd_2317775 < baseStart_2317775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2317976 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_2317976 : Nat := 118140960795 + 2317976 * 2 ^ 59
def prefixEnd_2317976 : Nat := 4983230072969 + 3 ^ 40 * 2317976 * 2
def baseEnd_2317976 : Nat := 264496851908072920431073

theorem tailTrace_2317976 : CollatzResearch.WordTrace tailWord_2317976 prefixEnd_2317976 264496851908072920431073 := by
  unfold tailWord_2317976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42271765125188152814194891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56362353500250870418926521 42271765125188152814194891)
  ·
    refine ⟨63407647687782229221292337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42271765125188152814194891 63407647687782229221292337)
    ·
      refine ⟨47555735765836671915969253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63407647687782229221292337 47555735765836671915969253)
      ·
        refine ⟨8916700456094375984244235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47555735765836671915969253 8916700456094375984244235)
        ·
          refine ⟨13375050684141563976366353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916700456094375984244235 13375050684141563976366353)
          ·
            refine ⟨10031288013106172982274765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13375050684141563976366353 10031288013106172982274765)
            ·
              refine ⟨3761733004914814868353037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10031288013106172982274765 3761733004914814868353037)
              ·
                refine ⟨1410649876843055575632389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3761733004914814868353037 1410649876843055575632389)
                ·
                  refine ⟨264496851908072920431073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410649876843055575632389 264496851908072920431073)
                  ·
                    rfl

theorem cell22_2317976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_2317976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2317976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2317976 prefixEnd_2317976 := by exact prefixLift 2317976
  have htrace : WordTrace (prefixWord ++ tailWord_2317976) baseStart_2317976 baseEnd_2317976 := by
    simpa [prefixWord, tailWord_2317976, baseEnd_2317976] using wordTrace_append hprefix tailTrace_2317976
  have hstable : (prefixWord ++ tailWord_2317976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2317976).length < 2 ^ (prefixWord ++ tailWord_2317976).sum := by decide
  have hdescent : baseEnd_2317976 < baseStart_2317976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2317976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318032 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_2318032 : Nat := 118140960795 + 2318032 * 2 ^ 59
def prefixEnd_2318032 : Nat := 4983230072969 + 3 ^ 40 * 2318032 * 2
def baseEnd_2318032 : Nat := 264503241889551093964349

theorem tailTrace_2318032 : CollatzResearch.WordTrace tailWord_2318032 prefixEnd_2318032 264503241889551093964349 := by
  unfold tailWord_2318032
  simp only [CollatzResearch.WordTrace]
  refine ⟨42272786369086713596214175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56363715158782284794952233 42272786369086713596214175)
  ·
    refine ⟨63409179553630070394321263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42272786369086713596214175 63409179553630070394321263)
    ·
      refine ⟨95113769330445105591481895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63409179553630070394321263 95113769330445105591481895)
      ·
        refine ⟨142670653995667658387222843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95113769330445105591481895 142670653995667658387222843)
        ·
          refine ⟨214005980993501487580834265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142670653995667658387222843 214005980993501487580834265)
          ·
            refine ⟨160504485745126115685625699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214005980993501487580834265 160504485745126115685625699)
            ·
              refine ⟨240756728617689173528438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160504485745126115685625699 240756728617689173528438549)
              ·
                refine ⟨11285471653954180009145557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 240756728617689173528438549 11285471653954180009145557)
                ·
                  refine ⟨264503241889551093964349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11285471653954180009145557 264503241889551093964349)
                  ·
                    rfl

theorem cell22_2318032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_2318032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318032 prefixEnd_2318032 := by exact prefixLift 2318032
  have htrace : WordTrace (prefixWord ++ tailWord_2318032) baseStart_2318032 baseEnd_2318032 := by
    simpa [prefixWord, tailWord_2318032, baseEnd_2318032] using wordTrace_append hprefix tailTrace_2318032
  have hstable : (prefixWord ++ tailWord_2318032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318032).length < 2 ^ (prefixWord ++ tailWord_2318032).sum := by decide
  have hdescent : baseEnd_2318032 < baseStart_2318032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318038 : List Nat := [5, 2, 1, 3, 2, 9]
def baseStart_2318038 : Nat := 118140960795 + 2318038 * 2 ^ 59
def prefixEnd_2318038 : Nat := 4983230072969 + 3 ^ 40 * 2318038 * 2
def baseEnd_2318038 : Nat := 9796441723349027978309

theorem tailTrace_2318038 : CollatzResearch.WordTrace tailWord_2318038 prefixEnd_2318038 9796441723349027978309 := by
  unfold tailWord_2318038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284111973509480638571673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56363861050767793478097845 5284111973509480638571673)
  ·
    refine ⟨3963083980132110478928755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5284111973509480638571673 3963083980132110478928755)
    ·
      refine ⟨5944625970198165718393133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963083980132110478928755 5944625970198165718393133)
      ·
        refine ⟨2229234738824312144397425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5944625970198165718393133 2229234738824312144397425)
        ·
          refine ⟨1671926054118234108298069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229234738824312144397425 1671926054118234108298069)
          ·
            refine ⟨9796441723349027978309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1671926054118234108298069 9796441723349027978309)
            ·
              rfl

theorem cell22_2318038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 9].length) (baseStart_2318038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318038 prefixEnd_2318038 := by exact prefixLift 2318038
  have htrace : WordTrace (prefixWord ++ tailWord_2318038) baseStart_2318038 baseEnd_2318038 := by
    simpa [prefixWord, tailWord_2318038, baseEnd_2318038] using wordTrace_append hprefix tailTrace_2318038
  have hstable : (prefixWord ++ tailWord_2318038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318038).length < 2 ^ (prefixWord ++ tailWord_2318038).sum := by decide
  have hdescent : baseEnd_2318038 < baseStart_2318038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318053 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_2318053 : Nat := 118140960795 + 2318053 * 2 ^ 59
def prefixEnd_2318053 : Nat := 4983230072969 + 3 ^ 40 * 2318053 * 2
def baseEnd_2318053 : Nat := 793516914397816227117983

theorem tailTrace_2318053 : CollatzResearch.WordTrace tailWord_2318053 prefixEnd_2318053 793516914397816227117983 := by
  unfold tailWord_2318053
  simp only [CollatzResearch.WordTrace]
  refine ⟨84546338671097347778942813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56364225780731565185961875 84546338671097347778942813)
  ·
    refine ⟨31704877001661505417103555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84546338671097347778942813 31704877001661505417103555)
    ·
      refine ⟨47557315502492258125655333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31704877001661505417103555 47557315502492258125655333)
      ·
        refine ⟨8916996656717298398560375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47557315502492258125655333 8916996656717298398560375)
        ·
          refine ⟨13375494985075947597840563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916996656717298398560375 13375494985075947597840563)
          ·
            refine ⟨20063242477613921396760845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13375494985075947597840563 20063242477613921396760845)
            ·
              refine ⟨7523715929105220523785317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20063242477613921396760845 7523715929105220523785317)
              ·
                refine ⟨1410696736707228848209747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7523715929105220523785317 1410696736707228848209747)
                ·
                  refine ⟨2116045105060843272314621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410696736707228848209747 2116045105060843272314621)
                  ·
                    refine ⟨793516914397816227117983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116045105060843272314621 793516914397816227117983)
                    ·
                      rfl

theorem cell22_2318053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_2318053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318053 prefixEnd_2318053 := by exact prefixLift 2318053
  have htrace : WordTrace (prefixWord ++ tailWord_2318053) baseStart_2318053 baseEnd_2318053 := by
    simpa [prefixWord, tailWord_2318053, baseEnd_2318053] using wordTrace_append hprefix tailTrace_2318053
  have hstable : (prefixWord ++ tailWord_2318053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318053).length < 2 ^ (prefixWord ++ tailWord_2318053).sum := by decide
  have hdescent : baseEnd_2318053 < baseStart_2318053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318079 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_2318079 : Nat := 118140960795 + 2318079 * 2 ^ 59
def prefixEnd_2318079 : Nat := 4983230072969 + 3 ^ 40 * 2318079 * 2
def baseEnd_2318079 : Nat := 793525814729160825967903

theorem tailTrace_2318079 : CollatzResearch.WordTrace tailWord_2318079 prefixEnd_2318079 793525814729160825967903 := by
  unfold tailWord_2318079
  simp only [CollatzResearch.WordTrace]
  refine ⟨84547286969003154219389291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56364857979335436146259527 84547286969003154219389291)
  ·
    refine ⟨126820930453504731329083937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84547286969003154219389291 126820930453504731329083937)
    ·
      refine ⟨95115697840128548496812953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126820930453504731329083937 95115697840128548496812953)
      ·
        refine ⟨71336773380096411372609715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95115697840128548496812953 71336773380096411372609715)
        ·
          refine ⟨107005160070144617058914573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71336773380096411372609715 107005160070144617058914573)
          ·
            refine ⟨40126935026304231397092965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107005160070144617058914573 40126935026304231397092965)
            ·
              refine ⟨7523800317432043386954931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40126935026304231397092965 7523800317432043386954931)
              ·
                refine ⟨11285700476148065080432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7523800317432043386954931 11285700476148065080432397)
                ·
                  refine ⟨4232137678555524405162149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11285700476148065080432397 4232137678555524405162149)
                  ·
                    refine ⟨793525814729160825967903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4232137678555524405162149 793525814729160825967903)
                    ·
                      rfl

theorem cell22_2318079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_2318079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318079 prefixEnd_2318079 := by exact prefixLift 2318079
  have htrace : WordTrace (prefixWord ++ tailWord_2318079) baseStart_2318079 baseEnd_2318079 := by
    simpa [prefixWord, tailWord_2318079, baseEnd_2318079] using wordTrace_append hprefix tailTrace_2318079
  have hstable : (prefixWord ++ tailWord_2318079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318079).length < 2 ^ (prefixWord ++ tailWord_2318079).sum := by decide
  have hdescent : baseEnd_2318079 < baseStart_2318079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318100 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_2318100 : Nat := 118140960795 + 2318100 * 2 ^ 59
def prefixEnd_2318100 : Nat := 4983230072969 + 3 ^ 40 * 2318100 * 2
def baseEnd_2318100 : Nat := 264511001152774590397613

theorem tailTrace_2318100 : CollatzResearch.WordTrace tailWord_2318100 prefixEnd_2318100 264511001152774590397613 := by
  unfold tailWord_2318100
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274026450963537402951877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56365368601284716537269169 42274026450963537402951877)
  ·
    refine ⟨7926379959555663263053477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42274026450963537402951877 7926379959555663263053477)
    ·
      refine ⟨1486196242416686861822527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7926379959555663263053477 1486196242416686861822527)
      ·
        refine ⟨2229294363625030292733791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486196242416686861822527 2229294363625030292733791)
        ·
          refine ⟨3343941545437545439100687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229294363625030292733791 3343941545437545439100687)
          ·
            refine ⟨5015912318156318158651031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343941545437545439100687 5015912318156318158651031)
            ·
              refine ⟨7523868477234477237976547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015912318156318158651031 7523868477234477237976547)
              ·
                refine ⟨11285802715851715856964821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7523868477234477237976547 11285802715851715856964821)
                ·
                  refine ⟨264511001152774590397613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11285802715851715856964821 264511001152774590397613)
                  ·
                    rfl

theorem cell22_2318100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_2318100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318100 prefixEnd_2318100 := by exact prefixLift 2318100
  have htrace : WordTrace (prefixWord ++ tailWord_2318100) baseStart_2318100 baseEnd_2318100 := by
    simpa [prefixWord, tailWord_2318100, baseEnd_2318100] using wordTrace_append hprefix tailTrace_2318100
  have hstable : (prefixWord ++ tailWord_2318100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318100).length < 2 ^ (prefixWord ++ tailWord_2318100).sum := by decide
  have hdescent : baseEnd_2318100 < baseStart_2318100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318111 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 4]
def baseStart_2318111 : Nat := 118140960795 + 2318111 * 2 ^ 59
def prefixEnd_2318111 : Nat := 4983230072969 + 3 ^ 40 * 2318111 * 2
def baseEnd_2318111 : Nat := 264512256327707803055935

theorem tailTrace_2318111 : CollatzResearch.WordTrace tailWord_2318111 prefixEnd_2318111 264512256327707803055935 := by
  unfold tailWord_2318111
  simp only [CollatzResearch.WordTrace]
  refine ⟨84548454104887223684554187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56365636069924815789702791 84548454104887223684554187)
  ·
    refine ⟨126822681157330835526831281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84548454104887223684554187 126822681157330835526831281)
    ·
      refine ⟨95117010867998126645123461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126822681157330835526831281 95117010867998126645123461)
      ·
        refine ⟨17834439537749648745960649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95117010867998126645123461 17834439537749648745960649)
        ·
          refine ⟨13375829653312236559470487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17834439537749648745960649 13375829653312236559470487)
          ·
            refine ⟨20063744479968354839205731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13375829653312236559470487 20063744479968354839205731)
            ·
              refine ⟨30095616719952532258808597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20063744479968354839205731 30095616719952532258808597)
              ·
                refine ⟨1410732033747774949631653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30095616719952532258808597 1410732033747774949631653)
                ·
                  refine ⟨264512256327707803055935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1410732033747774949631653 264512256327707803055935)
                  ·
                    rfl

theorem cell22_2318111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 4].length) (baseStart_2318111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318111 prefixEnd_2318111 := by exact prefixLift 2318111
  have htrace : WordTrace (prefixWord ++ tailWord_2318111) baseStart_2318111 baseEnd_2318111 := by
    simpa [prefixWord, tailWord_2318111, baseEnd_2318111] using wordTrace_append hprefix tailTrace_2318111
  have hstable : (prefixWord ++ tailWord_2318111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318111).length < 2 ^ (prefixWord ++ tailWord_2318111).sum := by decide
  have hdescent : baseEnd_2318111 < baseStart_2318111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318124 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_2318124 : Nat := 118140960795 + 2318124 * 2 ^ 59
def prefixEnd_2318124 : Nat := 4983230072969 + 3 ^ 40 * 2318124 * 2
def baseEnd_2318124 : Nat := 793541219148795708592765

theorem tailTrace_2318124 : CollatzResearch.WordTrace tailWord_2318124 prefixEnd_2318124 793541219148795708592765 := by
  unfold tailWord_2318124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274464126920063452388713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56365952169226751269851617 42274464126920063452388713)
  ·
    refine ⟨31705848095190047589291535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42274464126920063452388713 31705848095190047589291535)
    ·
      refine ⟨47558772142785071383937303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31705848095190047589291535 47558772142785071383937303)
      ·
        refine ⟨71338158214177607075905955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47558772142785071383937303 71338158214177607075905955)
        ·
          refine ⟨107007237321266410613858933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71338158214177607075905955 107007237321266410613858933)
          ·
            refine ⟨10031928498868725995049275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107007237321266410613858933 10031928498868725995049275)
            ·
              refine ⟨15047892748303088992573913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10031928498868725995049275 15047892748303088992573913)
              ·
                refine ⟨11285919561227316744430435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15047892748303088992573913 11285919561227316744430435)
                ·
                  refine ⟨16928879341840975116645653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11285919561227316744430435 16928879341840975116645653)
                  ·
                    refine ⟨793541219148795708592765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16928879341840975116645653 793541219148795708592765)
                    ·
                      rfl

theorem cell22_2318124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_2318124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318124 prefixEnd_2318124 := by exact prefixLift 2318124
  have htrace : WordTrace (prefixWord ++ tailWord_2318124) baseStart_2318124 baseEnd_2318124 := by
    simpa [prefixWord, tailWord_2318124, baseEnd_2318124] using wordTrace_append hprefix tailTrace_2318124
  have hstable : (prefixWord ++ tailWord_2318124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318124).length < 2 ^ (prefixWord ++ tailWord_2318124).sum := by decide
  have hdescent : baseEnd_2318124 < baseStart_2318124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318141 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2318141 : Nat := 118140960795 + 2318141 * 2 ^ 59
def prefixEnd_2318141 : Nat := 4983230072969 + 3 ^ 40 * 2318141 * 2
def baseEnd_2318141 : Nat := 793547038596213330917713

theorem tailTrace_2318141 : CollatzResearch.WordTrace tailWord_2318141 prefixEnd_2318141 793547038596213330917713 := by
  unfold tailWord_2318141
  simp only [CollatzResearch.WordTrace]
  refine ⟨84549548294778538808146277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56366365529852359205430851 84549548294778538808146277)
  ·
    refine ⟨15853040305270976026527427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84549548294778538808146277 15853040305270976026527427)
    ·
      refine ⟨23779560457906464039791141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15853040305270976026527427 23779560457906464039791141)
      ·
        refine ⟨4458667585857462007460839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23779560457906464039791141 4458667585857462007460839)
        ·
          refine ⟨6688001378786193011191259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458667585857462007460839 6688001378786193011191259)
          ·
            refine ⟨10032002068179289516786889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6688001378786193011191259 10032002068179289516786889)
            ·
              refine ⟨7524001551134467137590167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10032002068179289516786889 7524001551134467137590167)
              ·
                refine ⟨11286002326701700706385251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7524001551134467137590167 11286002326701700706385251)
                ·
                  refine ⟨16929003490052551059577877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11286002326701700706385251 16929003490052551059577877)
                  ·
                    refine ⟨793547038596213330917713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16929003490052551059577877 793547038596213330917713)
                    ·
                      rfl

theorem cell22_2318141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2318141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318141 prefixEnd_2318141 := by exact prefixLift 2318141
  have htrace : WordTrace (prefixWord ++ tailWord_2318141) baseStart_2318141 baseEnd_2318141 := by
    simpa [prefixWord, tailWord_2318141, baseEnd_2318141] using wordTrace_append hprefix tailTrace_2318141
  have hstable : (prefixWord ++ tailWord_2318141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318141).length < 2 ^ (prefixWord ++ tailWord_2318141).sum := by decide
  have hdescent : baseEnd_2318141 < baseStart_2318141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318156 : List Nat := [2, 2, 1, 3, 4, 2, 8]
def baseStart_2318156 : Nat := 118140960795 + 2318156 * 2 ^ 59
def prefixEnd_2318156 : Nat := 4983230072969 + 3 ^ 40 * 2318156 * 2
def baseEnd_2318156 : Nat := 29390821237139195992321

theorem tailTrace_2318156 : CollatzResearch.WordTrace tailWord_2318156 prefixEnd_2318156 29390821237139195992321 := by
  unfold tailWord_2318156
  simp only [CollatzResearch.WordTrace]
  refine ⟨42275047694862098184971161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56366730259816130913294881 42275047694862098184971161)
  ·
    refine ⟨31706285771146573638728371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42275047694862098184971161 31706285771146573638728371)
    ·
      refine ⟨47559428656719860458092557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31706285771146573638728371 47559428656719860458092557)
      ·
        refine ⟨17834785746269947671784709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47559428656719860458092557 17834785746269947671784709)
        ·
          refine ⟨3344022327425615188459633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17834785746269947671784709 3344022327425615188459633)
          ·
            refine ⟨2508016745569211391344725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3344022327425615188459633 2508016745569211391344725)
            ·
              refine ⟨29390821237139195992321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2508016745569211391344725 29390821237139195992321)
              ·
                rfl

theorem cell22_2318156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 8].length) (baseStart_2318156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318156 prefixEnd_2318156 := by exact prefixLift 2318156
  have htrace : WordTrace (prefixWord ++ tailWord_2318156) baseStart_2318156 baseEnd_2318156 := by
    simpa [prefixWord, tailWord_2318156, baseEnd_2318156] using wordTrace_append hprefix tailTrace_2318156
  have hstable : (prefixWord ++ tailWord_2318156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318156).length < 2 ^ (prefixWord ++ tailWord_2318156).sum := by decide
  have hdescent : baseEnd_2318156 < baseStart_2318156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318169 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_2318169 : Nat := 118140960795 + 2318169 * 2 ^ 59
def prefixEnd_2318169 : Nat := 4983230072969 + 3 ^ 40 * 2318169 * 2
def baseEnd_2318169 : Nat := 793556623568430591217627

theorem tailTrace_2318169 : CollatzResearch.WordTrace tailWord_2318169 prefixEnd_2318169 793556623568430591217627 := by
  unfold tailWord_2318169
  simp only [CollatzResearch.WordTrace]
  refine ⟨84550569538677099590165561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56367046359118066393443707 84550569538677099590165561)
  ·
    refine ⟨63412927154007824692624171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84550569538677099590165561 63412927154007824692624171)
    ·
      refine ⟨95119390731011737038936257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63412927154007824692624171 95119390731011737038936257)
      ·
        refine ⟨71339543048258802779202193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95119390731011737038936257 71339543048258802779202193)
        ·
          refine ⟨53504657286194102084401645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71339543048258802779202193 53504657286194102084401645)
          ·
            refine ⟨20064246482322788281650617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53504657286194102084401645 20064246482322788281650617)
            ·
              refine ⟨15048184861742091211237963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20064246482322788281650617 15048184861742091211237963)
              ·
                refine ⟨22572277292613136816856945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15048184861742091211237963 22572277292613136816856945)
                ·
                  refine ⟨16929207969459852612642709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22572277292613136816856945 16929207969459852612642709)
                  ·
                    refine ⟨793556623568430591217627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16929207969459852612642709 793556623568430591217627)
                    ·
                      rfl

theorem cell22_2318169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_2318169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318169 prefixEnd_2318169 := by exact prefixLift 2318169
  have htrace : WordTrace (prefixWord ++ tailWord_2318169) baseStart_2318169 baseEnd_2318169 := by
    simpa [prefixWord, tailWord_2318169, baseEnd_2318169] using wordTrace_append hprefix tailTrace_2318169
  have hstable : (prefixWord ++ tailWord_2318169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318169).length < 2 ^ (prefixWord ++ tailWord_2318169).sum := by decide
  have hdescent : baseEnd_2318169 < baseStart_2318169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318199 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2318199 : Nat := 118140960795 + 2318199 * 2 ^ 59
def prefixEnd_2318199 : Nat := 4983230072969 + 3 ^ 40 * 2318199 * 2
def baseEnd_2318199 : Nat := 793566893181520512967535

theorem tailTrace_2318199 : CollatzResearch.WordTrace tailWord_2318199 prefixEnd_2318199 793566893181520512967535 := by
  unfold tailWord_2318199
  simp only [CollatzResearch.WordTrace]
  refine ⟨84551663728568414713757651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56367775819045609809171767 84551663728568414713757651)
  ·
    refine ⟨126827495592852622070636477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84551663728568414713757651 126827495592852622070636477)
    ·
      refine ⟨47560310847319733276488679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126827495592852622070636477 47560310847319733276488679)
      ·
        refine ⟨71340466270979599914733019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47560310847319733276488679 71340466270979599914733019)
        ·
          refine ⟨107010699406469399872099529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71340466270979599914733019 107010699406469399872099529)
          ·
            refine ⟨80258024554852049904074647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107010699406469399872099529 80258024554852049904074647)
            ·
              refine ⟨120387036832278074856111971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80258024554852049904074647 120387036832278074856111971)
              ·
                refine ⟨180580555248417112284167957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120387036832278074856111971 180580555248417112284167957)
                ·
                  refine ⟨8464713527269552138320373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180580555248417112284167957 8464713527269552138320373)
                  ·
                    refine ⟨793566893181520512967535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8464713527269552138320373 793566893181520512967535)
                    ·
                      rfl

theorem cell22_2318199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2318199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318199 prefixEnd_2318199 := by exact prefixLift 2318199
  have htrace : WordTrace (prefixWord ++ tailWord_2318199) baseStart_2318199 baseEnd_2318199 := by
    simpa [prefixWord, tailWord_2318199, baseEnd_2318199] using wordTrace_append hprefix tailTrace_2318199
  have hstable : (prefixWord ++ tailWord_2318199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318199).length < 2 ^ (prefixWord ++ tailWord_2318199).sum := by decide
  have hdescent : baseEnd_2318199 < baseStart_2318199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318231 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_2318231 : Nat := 118140960795 + 2318231 * 2 ^ 59
def prefixEnd_2318231 : Nat := 4983230072969 + 3 ^ 40 * 2318231 * 2
def baseEnd_2318231 : Nat := 793577847435483096167437

theorem tailTrace_2318231 : CollatzResearch.WordTrace tailWord_2318231 prefixEnd_2318231 793577847435483096167437 := by
  unfold tailWord_2318231
  simp only [CollatzResearch.WordTrace]
  refine ⟨84552830864452484178922547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56368553909634989452615031 84552830864452484178922547)
  ·
    refine ⟨126829246296678726268383821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84552830864452484178922547 126829246296678726268383821)
    ·
      refine ⟨47560967361254522350643933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126829246296678726268383821 47560967361254522350643933)
      ·
        refine ⟨17835362760470445881491475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47560967361254522350643933 17835362760470445881491475)
        ·
          refine ⟨26753044140705668822237213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17835362760470445881491475 26753044140705668822237213)
          ·
            refine ⟨10032391552764625808338955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26753044140705668822237213 10032391552764625808338955)
            ·
              refine ⟨15048587329146938712508433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10032391552764625808338955 15048587329146938712508433)
              ·
                refine ⟨11286440496860204034381325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15048587329146938712508433 11286440496860204034381325)
                ·
                  refine ⟨4232415186322576512892997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11286440496860204034381325 4232415186322576512892997)
                  ·
                    refine ⟨793577847435483096167437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4232415186322576512892997 793577847435483096167437)
                    ·
                      rfl

theorem cell22_2318231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_2318231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318231 prefixEnd_2318231 := by exact prefixLift 2318231
  have htrace : WordTrace (prefixWord ++ tailWord_2318231) baseStart_2318231 baseEnd_2318231 := by
    simpa [prefixWord, tailWord_2318231, baseEnd_2318231] using wordTrace_append hprefix tailTrace_2318231
  have hstable : (prefixWord ++ tailWord_2318231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318231).length < 2 ^ (prefixWord ++ tailWord_2318231).sum := by decide
  have hdescent : baseEnd_2318231 < baseStart_2318231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318295 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 2, 3]
def baseStart_2318295 : Nat := 118140960795 + 2318295 * 2 ^ 59
def prefixEnd_2318295 : Nat := 4983230072969 + 3 ^ 40 * 2318295 * 2
def baseEnd_2318295 : Nat := 793599755943408262567241

theorem tailTrace_2318295 : CollatzResearch.WordTrace tailWord_2318295 prefixEnd_2318295 793599755943408262567241 := by
  unfold tailWord_2318295
  simp only [CollatzResearch.WordTrace]
  refine ⟨84555165136220623109252339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56370110090813748739501559 84555165136220623109252339)
  ·
    refine ⟨126832747704330934663878509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84555165136220623109252339 126832747704330934663878509)
    ·
      refine ⟨47562280389124100498954441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126832747704330934663878509 47562280389124100498954441)
      ·
        refine ⟨35671710291843075374215831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47562280389124100498954441 35671710291843075374215831)
        ·
          refine ⟨53507565437764613061323747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35671710291843075374215831 53507565437764613061323747)
          ·
            refine ⟨80261348156646919591985621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53507565437764613061323747 80261348156646919591985621)
            ·
              refine ⟨1881125347421412177937163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 80261348156646919591985621 1881125347421412177937163)
              ·
                refine ⟨2821688021132118266905745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881125347421412177937163 2821688021132118266905745)
                ·
                  refine ⟨2116266015849088700179309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2821688021132118266905745 2116266015849088700179309)
                  ·
                    refine ⟨793599755943408262567241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116266015849088700179309 793599755943408262567241)
                    ·
                      rfl

theorem cell22_2318295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_2318295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318295 prefixEnd_2318295 := by exact prefixLift 2318295
  have htrace : WordTrace (prefixWord ++ tailWord_2318295) baseStart_2318295 baseEnd_2318295 := by
    simpa [prefixWord, tailWord_2318295, baseEnd_2318295] using wordTrace_append hprefix tailTrace_2318295
  have hstable : (prefixWord ++ tailWord_2318295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318295).length < 2 ^ (prefixWord ++ tailWord_2318295).sum := by decide
  have hdescent : baseEnd_2318295 < baseStart_2318295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318411 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_2318411 : Nat := 118140960795 + 2318411 * 2 ^ 59
def prefixEnd_2318411 : Nat := 4983230072969 + 3 ^ 40 * 2318411 * 2
def baseEnd_2318411 : Nat := 793639465114022626666885

theorem tailTrace_2318411 : CollatzResearch.WordTrace tailWord_2318411 prefixEnd_2318411 793639465114022626666885 := by
  unfold tailWord_2318411
  simp only [CollatzResearch.WordTrace]
  refine ⟨84559396003800374920475087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56372930669200249946983391 84559396003800374920475087)
  ·
    refine ⟨126839094005700562380712631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84559396003800374920475087 126839094005700562380712631)
    ·
      refine ⟨190258641008550843571068947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126839094005700562380712631 190258641008550843571068947)
      ·
        refine ⟨285387961512826265356603421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190258641008550843571068947 285387961512826265356603421)
        ·
          refine ⟨107020485567309849508726283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285387961512826265356603421 107020485567309849508726283)
          ·
            refine ⟨160530728350964774263089425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107020485567309849508726283 160530728350964774263089425)
            ·
              refine ⟨120398046263223580697317069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160530728350964774263089425 120398046263223580697317069)
              ·
                refine ⟨45149267348708842761493901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120398046263223580697317069 45149267348708842761493901)
                ·
                  refine ⟨16930975255765816035560213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45149267348708842761493901 16930975255765816035560213)
                  ·
                    refine ⟨793639465114022626666885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16930975255765816035560213 793639465114022626666885)
                    ·
                      rfl

theorem cell22_2318411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_2318411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318411 prefixEnd_2318411 := by exact prefixLift 2318411
  have htrace : WordTrace (prefixWord ++ tailWord_2318411) baseStart_2318411 baseEnd_2318411 := by
    simpa [prefixWord, tailWord_2318411, baseEnd_2318411] using wordTrace_append hprefix tailTrace_2318411
  have hstable : (prefixWord ++ tailWord_2318411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318411).length < 2 ^ (prefixWord ++ tailWord_2318411).sum := by decide
  have hdescent : baseEnd_2318411 < baseStart_2318411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318447 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 2, 3]
def baseStart_2318447 : Nat := 118140960795 + 2318447 * 2 ^ 59
def prefixEnd_2318447 : Nat := 4983230072969 + 3 ^ 40 * 2318447 * 2
def baseEnd_2318447 : Nat := 793651788649730532766775

theorem tailTrace_2318447 : CollatzResearch.WordTrace tailWord_2318447 prefixEnd_2318447 793651788649730532766775 := by
  unfold tailWord_2318447
  simp only [CollatzResearch.WordTrace]
  refine ⟨84560709031669953068785595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56373806021113302045857063 84560709031669953068785595)
  ·
    refine ⟨126841063547504929603178393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84560709031669953068785595 126841063547504929603178393)
    ·
      refine ⟨95130797660628697202383795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126841063547504929603178393 95130797660628697202383795)
      ·
        refine ⟨142696196490943045803575693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95130797660628697202383795 142696196490943045803575693)
        ·
          refine ⟨53511073684103642176340885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142696196490943045803575693 53511073684103642176340885)
          ·
            refine ⟨2508331578942358227015979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53511073684103642176340885 2508331578942358227015979)
            ·
              refine ⟨3762497368413537340523969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508331578942358227015979 3762497368413537340523969)
              ·
                refine ⟨2821873026310153005392977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3762497368413537340523969 2821873026310153005392977)
                ·
                  refine ⟨2116404769732614754044733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2821873026310153005392977 2116404769732614754044733)
                  ·
                    refine ⟨793651788649730532766775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116404769732614754044733 793651788649730532766775)
                    ·
                      rfl

theorem cell22_2318447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_2318447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318447 prefixEnd_2318447 := by exact prefixLift 2318447
  have htrace : WordTrace (prefixWord ++ tailWord_2318447) baseStart_2318447 baseEnd_2318447 := by
    simpa [prefixWord, tailWord_2318447, baseEnd_2318447] using wordTrace_append hprefix tailTrace_2318447
  have hstable : (prefixWord ++ tailWord_2318447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318447).length < 2 ^ (prefixWord ++ tailWord_2318447).sum := by decide
  have hdescent : baseEnd_2318447 < baseStart_2318447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318509 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2318509 : Nat := 118140960795 + 2318509 * 2 ^ 59
def prefixEnd_2318509 : Nat := 4983230072969 + 3 ^ 40 * 2318509 * 2
def baseEnd_2318509 : Nat := 793673012516783037716585

theorem tailTrace_2318509 : CollatzResearch.WordTrace tailWord_2318509 prefixEnd_2318509 793673012516783037716585 := by
  unfold tailWord_2318509
  simp only [CollatzResearch.WordTrace]
  refine ⟨84562970357445337657542581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56375313571630225105028387 84562970357445337657542581)
  ·
    refine ⟨7927778471010500405394617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84562970357445337657542581 7927778471010500405394617)
    ·
      refine ⟨5945833853257875304045963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7927778471010500405394617 5945833853257875304045963)
      ·
        refine ⟨8918750779886812956068945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5945833853257875304045963 8918750779886812956068945)
        ·
          refine ⟨6689063084915109717051709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8918750779886812956068945 6689063084915109717051709)
          ·
            refine ⟨2508398656843166143894391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6689063084915109717051709 2508398656843166143894391)
            ·
              refine ⟨3762597985264749215841587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508398656843166143894391 3762597985264749215841587)
              ·
                refine ⟨5643896977897123823762381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762597985264749215841587 5643896977897123823762381)
                ·
                  refine ⟨2116461366711421433910893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5643896977897123823762381 2116461366711421433910893)
                  ·
                    refine ⟨793673012516783037716585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116461366711421433910893 793673012516783037716585)
                    ·
                      rfl

theorem cell22_2318509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2318509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318509 prefixEnd_2318509 := by exact prefixLift 2318509
  have htrace : WordTrace (prefixWord ++ tailWord_2318509) baseStart_2318509 baseEnd_2318509 := by
    simpa [prefixWord, tailWord_2318509, baseEnd_2318509] using wordTrace_append hprefix tailTrace_2318509
  have hstable : (prefixWord ++ tailWord_2318509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318509).length < 2 ^ (prefixWord ++ tailWord_2318509).sum := by decide
  have hdescent : baseEnd_2318509 < baseStart_2318509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318533 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 6]
def baseStart_2318533 : Nat := 118140960795 + 2318533 * 2 ^ 59
def prefixEnd_2318533 : Nat := 4983230072969 + 3 ^ 40 * 2318533 * 2
def baseEnd_2318533 : Nat := 264560409402418325038837

theorem tailTrace_2318533 : CollatzResearch.WordTrace tailWord_2318533 prefixEnd_2318533 264560409402418325038837 := by
  unfold tailWord_2318533
  simp only [CollatzResearch.WordTrace]
  refine ⟨84563845709358389756416253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56375897139572259837610835 84563845709358389756416253)
  ·
    refine ⟨31711442141009396158656095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84563845709358389756416253 31711442141009396158656095)
    ·
      refine ⟨47567163211514094237984143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31711442141009396158656095 47567163211514094237984143)
      ·
        refine ⟨71350744817271141356976215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47567163211514094237984143 71350744817271141356976215)
        ·
          refine ⟨107026117225906712035464323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71350744817271141356976215 107026117225906712035464323)
          ·
            refine ⟨160539175838860068053196485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107026117225906712035464323 160539175838860068053196485)
            ·
              refine ⟨30101095469786262759974341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160539175838860068053196485 30101095469786262759974341)
              ·
                refine ⟨5643955400584924267495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30101095469786262759974341 5643955400584924267495189)
                ·
                  refine ⟨264560409402418325038837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5643955400584924267495189 264560409402418325038837)
                  ·
                    rfl

theorem cell22_2318533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_2318533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318533 prefixEnd_2318533 := by exact prefixLift 2318533
  have htrace : WordTrace (prefixWord ++ tailWord_2318533) baseStart_2318533 baseEnd_2318533 := by
    simpa [prefixWord, tailWord_2318533, baseEnd_2318533] using wordTrace_append hprefix tailTrace_2318533
  have hstable : (prefixWord ++ tailWord_2318533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318533).length < 2 ^ (prefixWord ++ tailWord_2318533).sum := by decide
  have hdescent : baseEnd_2318533 < baseStart_2318533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318595 : List Nat := [1, 1, 1, 3, 2, 3, 5, 6]
def baseStart_2318595 : Nat := 118140960795 + 2318595 * 2 ^ 59
def prefixEnd_2318595 : Nat := 4983230072969 + 3 ^ 40 * 2318595 * 2
def baseEnd_2318595 : Nat := 88189161341589720007369

theorem tailTrace_2318595 : CollatzResearch.WordTrace tailWord_2318595 prefixEnd_2318595 88189161341589720007369 := by
  unfold tailWord_2318595
  simp only [CollatzResearch.WordTrace]
  refine ⟨84566107035133774345173239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56377404690089182896782159 84566107035133774345173239)
  ·
    refine ⟨126849160552700661517759859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84566107035133774345173239 126849160552700661517759859)
    ·
      refine ⟨190273740829050992276639789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126849160552700661517759859 190273740829050992276639789)
      ·
        refine ⟨71352652810894122103739921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190273740829050992276639789 71352652810894122103739921)
        ·
          refine ⟨53514489608170591577804941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71352652810894122103739921 53514489608170591577804941)
          ·
            refine ⟨20067933603063971841676853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53514489608170591577804941 20067933603063971841676853)
            ·
              refine ⟨1881368775287247360157205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20067933603063971841676853 1881368775287247360157205)
              ·
                refine ⟨88189161341589720007369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1881368775287247360157205 88189161341589720007369)
                ·
                  rfl

theorem cell22_2318595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 6].length) (baseStart_2318595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318595 prefixEnd_2318595 := by exact prefixLift 2318595
  have htrace : WordTrace (prefixWord ++ tailWord_2318595) baseStart_2318595 baseEnd_2318595 := by
    simpa [prefixWord, tailWord_2318595, baseEnd_2318595] using wordTrace_append hprefix tailTrace_2318595
  have hstable : (prefixWord ++ tailWord_2318595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318595).length < 2 ^ (prefixWord ++ tailWord_2318595).sum := by decide
  have hdescent : baseEnd_2318595 < baseStart_2318595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318627 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 3, 3]
def baseStart_2318627 : Nat := 118140960795 + 2318627 * 2 ^ 59
def prefixEnd_2318627 : Nat := 4983230072969 + 3 ^ 40 * 2318627 * 2
def baseEnd_2318627 : Nat := 793713406328270063266223

theorem tailTrace_2318627 : CollatzResearch.WordTrace tailWord_2318627 prefixEnd_2318627 793713406328270063266223 := by
  unfold tailWord_2318627
  simp only [CollatzResearch.WordTrace]
  refine ⟨84567274171017843810338135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56378182780678562540225423 84567274171017843810338135)
  ·
    refine ⟨126850911256526765715507203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84567274171017843810338135 126850911256526765715507203)
    ·
      refine ⟨190276366884790148573260805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126850911256526765715507203 190276366884790148573260805)
      ·
        refine ⟨35676818790898152857486401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190276366884790148573260805 35676818790898152857486401)
        ·
          refine ⟨26757614093173614643114801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35676818790898152857486401 26757614093173614643114801)
          ·
            refine ⟨20068210569880210982336101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26757614093173614643114801 20068210569880210982336101)
            ·
              refine ⟨3762789481852539559188019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20068210569880210982336101 3762789481852539559188019)
              ·
                refine ⟨5644184222778809338782029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762789481852539559188019 5644184222778809338782029)
                ·
                  refine ⟨2116569083542053502043261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5644184222778809338782029 2116569083542053502043261)
                  ·
                    refine ⟨793713406328270063266223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116569083542053502043261 793713406328270063266223)
                    ·
                      rfl

theorem cell22_2318627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3].length) (baseStart_2318627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318627 prefixEnd_2318627 := by exact prefixLift 2318627
  have htrace : WordTrace (prefixWord ++ tailWord_2318627) baseStart_2318627 baseEnd_2318627 := by
    simpa [prefixWord, tailWord_2318627, baseEnd_2318627] using wordTrace_append hprefix tailTrace_2318627
  have hstable : (prefixWord ++ tailWord_2318627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318627).length < 2 ^ (prefixWord ++ tailWord_2318627).sum := by decide
  have hdescent : baseEnd_2318627 < baseStart_2318627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318644 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2318644 : Nat := 118140960795 + 2318644 * 2 ^ 59
def prefixEnd_2318644 : Nat := 4983230072969 + 3 ^ 40 * 2318644 * 2
def baseEnd_2318644 : Nat := 793719225775687685591171

theorem tailTrace_2318644 : CollatzResearch.WordTrace tailWord_2318644 prefixEnd_2318644 793719225775687685591171 := by
  unfold tailWord_2318644
  simp only [CollatzResearch.WordTrace]
  refine ⟨42283947105978127856853493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56378596141304170475804657 42283947105978127856853493)
  ·
    refine ⟨3964120041185449486580015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42283947105978127856853493 3964120041185449486580015)
    ·
      refine ⟨5946180061778174229870023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964120041185449486580015 5946180061778174229870023)
      ·
        refine ⟨8919270092667261344805035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946180061778174229870023 8919270092667261344805035)
        ·
          refine ⟨13378905139000892017207553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919270092667261344805035 13378905139000892017207553)
          ·
            refine ⟨10034178854250669012905665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13378905139000892017207553 10034178854250669012905665)
            ·
              refine ⟨7525634140688001759679249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10034178854250669012905665 7525634140688001759679249)
              ·
                refine ⟨5644225605516001319759437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7525634140688001759679249 5644225605516001319759437)
                ·
                  refine ⟨2116584602068500494909789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5644225605516001319759437 2116584602068500494909789)
                  ·
                    refine ⟨793719225775687685591171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116584602068500494909789 793719225775687685591171)
                    ·
                      rfl

theorem cell22_2318644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2318644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318644 prefixEnd_2318644 := by exact prefixLift 2318644
  have htrace : WordTrace (prefixWord ++ tailWord_2318644) baseStart_2318644 baseEnd_2318644 := by
    simpa [prefixWord, tailWord_2318644, baseEnd_2318644] using wordTrace_append hprefix tailTrace_2318644
  have hstable : (prefixWord ++ tailWord_2318644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318644).length < 2 ^ (prefixWord ++ tailWord_2318644).sum := by decide
  have hdescent : baseEnd_2318644 < baseStart_2318644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318704 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_2318704 : Nat := 118140960795 + 2318704 * 2 ^ 59
def prefixEnd_2318704 : Nat := 4983230072969 + 3 ^ 40 * 2318704 * 2
def baseEnd_2318704 : Nat := 793739765001867529090987

theorem tailTrace_2318704 : CollatzResearch.WordTrace tailWord_2318704 prefixEnd_2318704 793739765001867529090987 := by
  unfold tailWord_2318704
  simp only [CollatzResearch.WordTrace]
  refine ⟨42285041295869442980445583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56380055061159257307260777 42285041295869442980445583)
  ·
    refine ⟨63427561943804164470668375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42285041295869442980445583 63427561943804164470668375)
    ·
      refine ⟨95141342915706246706002563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63427561943804164470668375 95141342915706246706002563)
      ·
        refine ⟨142712014373559370059003845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95141342915706246706002563 142712014373559370059003845)
        ·
          refine ⟨26758502695042381886063221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142712014373559370059003845 26758502695042381886063221)
          ·
            refine ⟨2508609627660223301818427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26758502695042381886063221 2508609627660223301818427)
            ·
              refine ⟨3762914441490334952727641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508609627660223301818427 3762914441490334952727641)
              ·
                refine ⟨2822185831117751214545731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3762914441490334952727641 2822185831117751214545731)
                ·
                  refine ⟨4233278746676626821818597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822185831117751214545731 4233278746676626821818597)
                  ·
                    refine ⟨793739765001867529090987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233278746676626821818597 793739765001867529090987)
                    ·
                      rfl

theorem cell22_2318704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_2318704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318704 prefixEnd_2318704 := by exact prefixLift 2318704
  have htrace : WordTrace (prefixWord ++ tailWord_2318704) baseStart_2318704 baseEnd_2318704 := by
    simpa [prefixWord, tailWord_2318704, baseEnd_2318704] using wordTrace_append hprefix tailTrace_2318704
  have hstable : (prefixWord ++ tailWord_2318704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318704).length < 2 ^ (prefixWord ++ tailWord_2318704).sum := by decide
  have hdescent : baseEnd_2318704 < baseStart_2318704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318717 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2318717 : Nat := 118140960795 + 2318717 * 2 ^ 59
def prefixEnd_2318717 : Nat := 4983230072969 + 3 ^ 40 * 2318717 * 2
def baseEnd_2318717 : Nat := 793744215167539828515947

theorem tailTrace_2318717 : CollatzResearch.WordTrace tailWord_2318717 prefixEnd_2318717 793744215167539828515947 := by
  unfold tailWord_2318717
  simp only [CollatzResearch.WordTrace]
  refine ⟨84570556740691789181114405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56380371160461192787409603 84570556740691789181114405)
  ·
    refine ⟨15856979388879710471458951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84570556740691789181114405 15856979388879710471458951)
    ·
      refine ⟨23785469083319565707188427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15856979388879710471458951 23785469083319565707188427)
      ·
        refine ⟨35678203624979348560782641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23785469083319565707188427 35678203624979348560782641)
        ·
          refine ⟨26758652718734511420586981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35678203624979348560782641 26758652718734511420586981)
          ·
            refine ⟨5017247384762720891360059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26758652718734511420586981 5017247384762720891360059)
            ·
              refine ⟨7525871077144081337040089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017247384762720891360059 7525871077144081337040089)
              ·
                refine ⟨5644403307858061002780067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7525871077144081337040089 5644403307858061002780067)
                ·
                  refine ⟨8466604961787091504170101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5644403307858061002780067 8466604961787091504170101)
                  ·
                    refine ⟨793744215167539828515947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8466604961787091504170101 793744215167539828515947)
                    ·
                      rfl

theorem cell22_2318717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2318717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318717 prefixEnd_2318717 := by exact prefixLift 2318717
  have htrace : WordTrace (prefixWord ++ tailWord_2318717) baseStart_2318717 baseEnd_2318717 := by
    simpa [prefixWord, tailWord_2318717, baseEnd_2318717] using wordTrace_append hprefix tailTrace_2318717
  have hstable : (prefixWord ++ tailWord_2318717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318717).length < 2 ^ (prefixWord ++ tailWord_2318717).sum := by decide
  have hdescent : baseEnd_2318717 < baseStart_2318717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318721 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2318721 : Nat := 118140960795 + 2318721 * 2 ^ 59
def prefixEnd_2318721 : Nat := 4983230072969 + 3 ^ 40 * 2318721 * 2
def baseEnd_2318721 : Nat := 793745584449285151415935

theorem tailTrace_2318721 : CollatzResearch.WordTrace tailWord_2318721 prefixEnd_2318721 793745584449285151415935 := by
  unfold tailWord_2318721
  simp only [CollatzResearch.WordTrace]
  refine ⟨84570702632677297864260017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56380468421784865242840011 84570702632677297864260017)
  ·
    refine ⟨63428026974507973398195013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84570702632677297864260017 63428026974507973398195013)
    ·
      refine ⟨11892755057720245012161565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63428026974507973398195013 11892755057720245012161565)
      ·
        refine ⟨4459783146645091879560587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11892755057720245012161565 4459783146645091879560587)
        ·
          refine ⟨6689674719967637819340881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459783146645091879560587 6689674719967637819340881)
          ·
            refine ⟨5017256039975728364505661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689674719967637819340881 5017256039975728364505661)
            ·
              refine ⟨1881471014990898136689623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5017256039975728364505661 1881471014990898136689623)
              ·
                refine ⟨2822206522486347205034435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881471014990898136689623 2822206522486347205034435)
                ·
                  refine ⟨4233309783729520807551653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822206522486347205034435 4233309783729520807551653)
                  ·
                    refine ⟨793745584449285151415935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233309783729520807551653 793745584449285151415935)
                    ·
                      rfl

theorem cell22_2318721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2318721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318721 prefixEnd_2318721 := by exact prefixLift 2318721
  have htrace : WordTrace (prefixWord ++ tailWord_2318721) baseStart_2318721 baseEnd_2318721 := by
    simpa [prefixWord, tailWord_2318721, baseEnd_2318721] using wordTrace_append hprefix tailTrace_2318721
  have hstable : (prefixWord ++ tailWord_2318721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318721).length < 2 ^ (prefixWord ++ tailWord_2318721).sum := by decide
  have hdescent : baseEnd_2318721 < baseStart_2318721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318732 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_2318732 : Nat := 118140960795 + 2318732 * 2 ^ 59
def prefixEnd_2318732 : Nat := 4983230072969 + 3 ^ 40 * 2318732 * 2
def baseEnd_2318732 : Nat := 793749349974084789390901

theorem tailTrace_2318732 : CollatzResearch.WordTrace tailWord_2318732 prefixEnd_2318732 793749349974084789390901 := by
  unfold tailWord_2318732
  simp only [CollatzResearch.WordTrace]
  refine ⟨42285551917818723371455225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56380735890424964495273633 42285551917818723371455225)
  ·
    refine ⟨31714163938364042528591419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42285551917818723371455225 31714163938364042528591419)
    ·
      refine ⟨47571245907546063792887129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31714163938364042528591419 47571245907546063792887129)
      ·
        refine ⟨35678434430659547844665347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47571245907546063792887129 35678434430659547844665347)
        ·
          refine ⟨53517651645989321766998021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35678434430659547844665347 53517651645989321766998021)
          ·
            refine ⟨10034559683622997831312129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53517651645989321766998021 10034559683622997831312129)
            ·
              refine ⟨7525919762717248373484097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10034559683622997831312129 7525919762717248373484097)
              ·
                refine ⟨5644439822037936280113073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7525919762717248373484097 5644439822037936280113073)
                ·
                  refine ⟨4233329866528452210084805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5644439822037936280113073 4233329866528452210084805)
                  ·
                    refine ⟨793749349974084789390901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233329866528452210084805 793749349974084789390901)
                    ·
                      rfl

theorem cell22_2318732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_2318732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318732 prefixEnd_2318732 := by exact prefixLift 2318732
  have htrace : WordTrace (prefixWord ++ tailWord_2318732) baseStart_2318732 baseEnd_2318732 := by
    simpa [prefixWord, tailWord_2318732, baseEnd_2318732] using wordTrace_append hprefix tailTrace_2318732
  have hstable : (prefixWord ++ tailWord_2318732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318732).length < 2 ^ (prefixWord ++ tailWord_2318732).sum := by decide
  have hdescent : baseEnd_2318732 < baseStart_2318732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318772 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2318772 : Nat := 118140960795 + 2318772 * 2 ^ 59
def prefixEnd_2318772 : Nat := 4983230072969 + 3 ^ 40 * 2318772 * 2
def baseEnd_2318772 : Nat := 793763042791538018390779

theorem tailTrace_2318772 : CollatzResearch.WordTrace tailWord_2318772 prefixEnd_2318772 793763042791538018390779 := by
  unfold tailWord_2318772
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286281377746266787183285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56381708503661689049577713 42286281377746266787183285)
  ·
    refine ⟨3964338879163712511298433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42286281377746266787183285 3964338879163712511298433)
    ·
      refine ⟨2973254159372784383473825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3964338879163712511298433 2973254159372784383473825)
      ·
        refine ⟨2229940619529588287605369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2973254159372784383473825 2229940619529588287605369)
        ·
          refine ⟨1672455464647191215704027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229940619529588287605369 1672455464647191215704027)
          ·
            refine ⟨2508683196970786823556041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672455464647191215704027 2508683196970786823556041)
            ·
              refine ⟨1881512397728090117667031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508683196970786823556041 1881512397728090117667031)
              ·
                refine ⟨2822268596592135176500547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881512397728090117667031 2822268596592135176500547)
                ·
                  refine ⟨4233402894888202764750821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822268596592135176500547 4233402894888202764750821)
                  ·
                    refine ⟨793763042791538018390779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233402894888202764750821 793763042791538018390779)
                    ·
                      rfl

theorem cell22_2318772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2318772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318772 prefixEnd_2318772 := by exact prefixLift 2318772
  have htrace : WordTrace (prefixWord ++ tailWord_2318772) baseStart_2318772 baseEnd_2318772 := by
    simpa [prefixWord, tailWord_2318772, baseEnd_2318772] using wordTrace_append hprefix tailTrace_2318772
  have hstable : (prefixWord ++ tailWord_2318772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318772).length < 2 ^ (prefixWord ++ tailWord_2318772).sum := by decide
  have hdescent : baseEnd_2318772 < baseStart_2318772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318792 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_2318792 : Nat := 118140960795 + 2318792 * 2 ^ 59
def prefixEnd_2318792 : Nat := 4983230072969 + 3 ^ 40 * 2318792 * 2
def baseEnd_2318792 : Nat := 264589963066754877630239

theorem tailTrace_2318792 : CollatzResearch.WordTrace tailWord_2318792 prefixEnd_2318792 264589963066754877630239 := by
  unfold tailWord_2318792
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286646107710038495047315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56382194810280051326729753 42286646107710038495047315)
  ·
    refine ⟨63429969161565057742570973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42286646107710038495047315 63429969161565057742570973)
    ·
      refine ⟨23786238435586896653464115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63429969161565057742570973 23786238435586896653464115)
      ·
        refine ⟨35679357653380344980196173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23786238435586896653464115 35679357653380344980196173)
        ·
          refine ⟨13379759120017629367573565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35679357653380344980196173 13379759120017629367573565)
          ·
            refine ⟨5017409670006611012840087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13379759120017629367573565 5017409670006611012840087)
            ·
              refine ⟨7526114505009916519260131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017409670006611012840087 7526114505009916519260131)
              ·
                refine ⟨11289171757514874778890197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526114505009916519260131 11289171757514874778890197)
                ·
                  refine ⟨264589963066754877630239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11289171757514874778890197 264589963066754877630239)
                  ·
                    rfl

theorem cell22_2318792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_2318792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318792 prefixEnd_2318792 := by exact prefixLift 2318792
  have htrace : WordTrace (prefixWord ++ tailWord_2318792) baseStart_2318792 baseEnd_2318792 := by
    simpa [prefixWord, tailWord_2318792, baseEnd_2318792] using wordTrace_append hprefix tailTrace_2318792
  have hstable : (prefixWord ++ tailWord_2318792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318792).length < 2 ^ (prefixWord ++ tailWord_2318792).sum := by decide
  have hdescent : baseEnd_2318792 < baseStart_2318792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318796 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_2318796 : Nat := 118140960795 + 2318796 * 2 ^ 59
def prefixEnd_2318796 : Nat := 4983230072969 + 3 ^ 40 * 2318796 * 2
def baseEnd_2318796 : Nat := 793771258482009955790705

theorem tailTrace_2318796 : CollatzResearch.WordTrace tailWord_2318796 prefixEnd_2318796 793771258482009955790705 := by
  unfold tailWord_2318796
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286719053702792836620121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56382292071603723782160161 42286719053702792836620121)
  ·
    refine ⟨31715039290277094627465091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42286719053702792836620121 31715039290277094627465091)
    ·
      refine ⟨47572558935415641941197637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31715039290277094627465091 47572558935415641941197637)
      ·
        refine ⟨8919854800390432863974557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47572558935415641941197637 8919854800390432863974557)
        ·
          refine ⟨3344945550146412323990459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8919854800390432863974557 3344945550146412323990459)
          ·
            refine ⟨5017418325219618485985689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344945550146412323990459 5017418325219618485985689)
            ·
              refine ⟨3763063743914713864489267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5017418325219618485985689 3763063743914713864489267)
              ·
                refine ⟨5644595615872070796733901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763063743914713864489267 5644595615872070796733901)
                ·
                  refine ⟨2116723355952026548775213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5644595615872070796733901 2116723355952026548775213)
                  ·
                    refine ⟨793771258482009955790705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116723355952026548775213 793771258482009955790705)
                    ·
                      rfl

theorem cell22_2318796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_2318796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318796 prefixEnd_2318796 := by exact prefixLift 2318796
  have htrace : WordTrace (prefixWord ++ tailWord_2318796) baseStart_2318796 baseEnd_2318796 := by
    simpa [prefixWord, tailWord_2318796, baseEnd_2318796] using wordTrace_append hprefix tailTrace_2318796
  have hstable : (prefixWord ++ tailWord_2318796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318796).length < 2 ^ (prefixWord ++ tailWord_2318796).sum := by decide
  have hdescent : baseEnd_2318796 < baseStart_2318796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318809 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 5]
def baseStart_2318809 : Nat := 118140960795 + 2318809 * 2 ^ 59
def prefixEnd_2318809 : Nat := 4983230072969 + 3 ^ 40 * 2318809 * 2
def baseEnd_2318809 : Nat := 264591902882560751738555

theorem tailTrace_2318809 : CollatzResearch.WordTrace tailWord_2318809 prefixEnd_2318809 264591902882560751738555 := by
  unfold tailWord_2318809
  simp only [CollatzResearch.WordTrace]
  refine ⟨84573912256358488893463481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56382608170905659262308987 84573912256358488893463481)
  ·
    refine ⟨63430434192268866670097611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84573912256358488893463481 63430434192268866670097611)
    ·
      refine ⟨95145651288403300005146417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63430434192268866670097611 95145651288403300005146417)
      ·
        refine ⟨71359238466302475003859813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95145651288403300005146417 71359238466302475003859813)
        ·
          refine ⟨13379857212431714063223715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71359238466302475003859813 13379857212431714063223715)
          ·
            refine ⟨20069785818647571094835573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379857212431714063223715 20069785818647571094835573)
            ·
              refine ⟨1881542420498209790140835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20069785818647571094835573 1881542420498209790140835)
              ·
                refine ⟨2822313630747314685211253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881542420498209790140835 2822313630747314685211253)
                ·
                  refine ⟨264591902882560751738555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2822313630747314685211253 264591902882560751738555)
                  ·
                    rfl

theorem cell22_2318809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_2318809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318809 prefixEnd_2318809 := by exact prefixLift 2318809
  have htrace : WordTrace (prefixWord ++ tailWord_2318809) baseStart_2318809 baseEnd_2318809 := by
    simpa [prefixWord, tailWord_2318809, baseEnd_2318809] using wordTrace_append hprefix tailTrace_2318809
  have hstable : (prefixWord ++ tailWord_2318809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318809).length < 2 ^ (prefixWord ++ tailWord_2318809).sum := by decide
  have hdescent : baseEnd_2318809 < baseStart_2318809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318867 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_2318867 : Nat := 118140960795 + 2318867 * 2 ^ 59
def prefixEnd_2318867 : Nat := 4983230072969 + 3 ^ 40 * 2318867 * 2
def baseEnd_2318867 : Nat := 793795563232989437265487

theorem tailTrace_2318867 : CollatzResearch.WordTrace tailWord_2318867 prefixEnd_2318867 793795563232989437265487 := by
  unfold tailWord_2318867
  simp only [CollatzResearch.WordTrace]
  refine ⟨84576027690148364799074855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56384018460098909866049903 84576027690148364799074855)
  ·
    refine ⟨126864041535222547198612283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84576027690148364799074855 126864041535222547198612283)
    ·
      refine ⟨190296062302833820797918425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126864041535222547198612283 190296062302833820797918425)
      ·
        refine ⟨142722046727125365598438819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190296062302833820797918425 142722046727125365598438819)
        ·
          refine ⟨214083070090688048397658229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142722046727125365598438819 214083070090688048397658229)
          ·
            refine ⟨20070287821002004537280459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214083070090688048397658229 20070287821002004537280459)
            ·
              refine ⟨30105431731503006805920689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20070287821002004537280459 30105431731503006805920689)
              ·
                refine ⟨22579073798627255104440517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30105431731503006805920689 22579073798627255104440517)
                ·
                  refine ⟨4233576337242610332082597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22579073798627255104440517 4233576337242610332082597)
                  ·
                    refine ⟨793795563232989437265487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233576337242610332082597 793795563232989437265487)
                    ·
                      rfl

theorem cell22_2318867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_2318867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318867 prefixEnd_2318867 := by exact prefixLift 2318867
  have htrace : WordTrace (prefixWord ++ tailWord_2318867) baseStart_2318867 baseEnd_2318867 := by
    simpa [prefixWord, tailWord_2318867, baseEnd_2318867] using wordTrace_append hprefix tailTrace_2318867
  have hstable : (prefixWord ++ tailWord_2318867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318867).length < 2 ^ (prefixWord ++ tailWord_2318867).sum := by decide
  have hdescent : baseEnd_2318867 < baseStart_2318867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318912 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_2318912 : Nat := 118140960795 + 2318912 * 2 ^ 59
def prefixEnd_2318912 : Nat := 4983230072969 + 3 ^ 40 * 2318912 * 2
def baseEnd_2318912 : Nat := 793810967652624319890349

theorem tailTrace_2318912 : CollatzResearch.WordTrace tailWord_2318912 prefixEnd_2318912 793810967652624319890349 := by
  unfold tailWord_2318912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42288834487492668742231495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56385112649990224989641993 42288834487492668742231495)
  ·
    refine ⟨63433251731239003113347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42288834487492668742231495 63433251731239003113347243)
    ·
      refine ⟨95149877596858504670020865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63433251731239003113347243 95149877596858504670020865)
      ·
        refine ⟨71362408197643878502515649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95149877596858504670020865 71362408197643878502515649)
        ·
          refine ⟨53521806148232908876886737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71362408197643878502515649 53521806148232908876886737)
          ·
            refine ⟨40141354611174681657665053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53521806148232908876886737 40141354611174681657665053)
            ·
              refine ⟨15053007979190505621624395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40141354611174681657665053 15053007979190505621624395)
              ·
                refine ⟨22579511968785758432436593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15053007979190505621624395 22579511968785758432436593)
                ·
                  refine ⟨16934633976589318824327445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22579511968785758432436593 16934633976589318824327445)
                  ·
                    refine ⟨793810967652624319890349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16934633976589318824327445 793810967652624319890349)
                    ·
                      rfl

theorem cell22_2318912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_2318912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318912 prefixEnd_2318912 := by exact prefixLift 2318912
  have htrace : WordTrace (prefixWord ++ tailWord_2318912) baseStart_2318912 baseEnd_2318912 := by
    simpa [prefixWord, tailWord_2318912, baseEnd_2318912] using wordTrace_append hprefix tailTrace_2318912
  have hstable : (prefixWord ++ tailWord_2318912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318912).length < 2 ^ (prefixWord ++ tailWord_2318912).sum := by decide
  have hdescent : baseEnd_2318912 < baseStart_2318912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2318948 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_2318948 : Nat := 118140960795 + 2318948 * 2 ^ 59
def prefixEnd_2318948 : Nat := 4983230072969 + 3 ^ 40 * 2318948 * 2
def baseEnd_2318948 : Nat := 793823291188332225990239

theorem tailTrace_2318948 : CollatzResearch.WordTrace tailWord_2318948 prefixEnd_2318948 793823291188332225990239 := by
  unfold tailWord_2318948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42289491001427457816386749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56385988001903277088515665 42289491001427457816386749)
  ·
    refine ⟨15858559125535296681145031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42289491001427457816386749 15858559125535296681145031)
    ·
      refine ⟨23787838688302945021717547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15858559125535296681145031 23787838688302945021717547)
      ·
        refine ⟨35681758032454417532576321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23787838688302945021717547 35681758032454417532576321)
        ·
          refine ⟨26761318524340813149432241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35681758032454417532576321 26761318524340813149432241)
          ·
            refine ⟨20070988893255609862074181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26761318524340813149432241 20070988893255609862074181)
            ·
              refine ⟨3763310417485426849138909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20070988893255609862074181 3763310417485426849138909)
              ·
                refine ⟨1411241406557035068427091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3763310417485426849138909 1411241406557035068427091)
                ·
                  refine ⟨2116862109835552602640637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411241406557035068427091 2116862109835552602640637)
                  ·
                    refine ⟨793823291188332225990239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116862109835552602640637 793823291188332225990239)
                    ·
                      rfl

theorem cell22_2318948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_2318948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2318948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2318948 prefixEnd_2318948 := by exact prefixLift 2318948
  have htrace : WordTrace (prefixWord ++ tailWord_2318948) baseStart_2318948 baseEnd_2318948 := by
    simpa [prefixWord, tailWord_2318948, baseEnd_2318948] using wordTrace_append hprefix tailTrace_2318948
  have hstable : (prefixWord ++ tailWord_2318948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2318948).length < 2 ^ (prefixWord ++ tailWord_2318948).sum := by decide
  have hdescent : baseEnd_2318948 < baseStart_2318948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2318948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319023 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 4]
def baseStart_2319023 : Nat := 118140960795 + 2319023 * 2 ^ 59
def prefixEnd_2319023 : Nat := 4983230072969 + 3 ^ 40 * 2319023 * 2
def baseEnd_2319023 : Nat := 264616321740352343455003

theorem tailTrace_2319023 : CollatzResearch.WordTrace tailWord_2319023 prefixEnd_2319023 264616321740352343455003 := by
  unfold tailWord_2319023
  simp only [CollatzResearch.WordTrace]
  refine ⟨84581717477583203441753723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56387811651722135627835815 84581717477583203441753723)
  ·
    refine ⟨126872576216374805162630585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84581717477583203441753723 126872576216374805162630585)
    ·
      refine ⟨95154432162281103871972939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126872576216374805162630585 95154432162281103871972939)
      ·
        refine ⟨142731648243421655807959409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95154432162281103871972939 142731648243421655807959409)
        ·
          refine ⟨107048736182566241855969557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142731648243421655807959409 107048736182566241855969557)
          ·
            refine ⟨5017909508557792586998573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107048736182566241855969557 5017909508557792586998573)
            ·
              refine ⟨1881716065709172220124465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5017909508557792586998573 1881716065709172220124465)
              ·
                refine ⟨1411287049281879165093349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881716065709172220124465 1411287049281879165093349)
                ·
                  refine ⟨264616321740352343455003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411287049281879165093349 264616321740352343455003)
                  ·
                    rfl

theorem cell22_2319023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 4].length) (baseStart_2319023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319023 prefixEnd_2319023 := by exact prefixLift 2319023
  have htrace : WordTrace (prefixWord ++ tailWord_2319023) baseStart_2319023 baseEnd_2319023 := by
    simpa [prefixWord, tailWord_2319023, baseEnd_2319023] using wordTrace_append hprefix tailTrace_2319023
  have hstable : (prefixWord ++ tailWord_2319023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319023).length < 2 ^ (prefixWord ++ tailWord_2319023).sum := by decide
  have hdescent : baseEnd_2319023 < baseStart_2319023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319034 : List Nat := [3, 1, 1, 1, 2, 3, 4, 7]
def baseStart_2319034 : Nat := 118140960795 + 2319034 * 2 ^ 59
def prefixEnd_2319034 : Nat := 4983230072969 + 3 ^ 40 * 2319034 * 2
def baseEnd_2319034 : Nat := 88205858971761852037775

theorem tailTrace_2319034 : CollatzResearch.WordTrace tailWord_2319034 prefixEnd_2319034 88205858971761852037775 := by
  unfold tailWord_2319034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145529670135838080101039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56388079120362234880269437 21145529670135838080101039)
  ·
    refine ⟨31718294505203757120151559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21145529670135838080101039 31718294505203757120151559)
    ·
      refine ⟨47577441757805635680227339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31718294505203757120151559 47577441757805635680227339)
      ·
        refine ⟨71366162636708453520341009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47577441757805635680227339 71366162636708453520341009)
        ·
          refine ⟨53524621977531340140255757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71366162636708453520341009 53524621977531340140255757)
          ·
            refine ⟨20071733241574252552595909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53524621977531340140255757 20071733241574252552595909)
            ·
              refine ⟨3763449982795172353611733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20071733241574252552595909 3763449982795172353611733)
              ·
                refine ⟨88205858971761852037775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3763449982795172353611733 88205858971761852037775)
                ·
                  rfl

theorem cell22_2319034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_2319034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319034 prefixEnd_2319034 := by exact prefixLift 2319034
  have htrace : WordTrace (prefixWord ++ tailWord_2319034) baseStart_2319034 baseEnd_2319034 := by
    simpa [prefixWord, tailWord_2319034, baseEnd_2319034] using wordTrace_append hprefix tailTrace_2319034
  have hstable : (prefixWord ++ tailWord_2319034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319034).length < 2 ^ (prefixWord ++ tailWord_2319034).sum := by decide
  have hdescent : baseEnd_2319034 < baseStart_2319034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319038 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2319038 : Nat := 118140960795 + 2319038 * 2 ^ 59
def prefixEnd_2319038 : Nat := 4983230072969 + 3 ^ 40 * 2319038 * 2
def baseEnd_2319038 : Nat := 793854100027601991239963

theorem tailTrace_2319038 : CollatzResearch.WordTrace tailWord_2319038 prefixEnd_2319038 793854100027601991239963 := by
  unfold tailWord_2319038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572783071566107625443721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56388176381685907335699845 10572783071566107625443721)
  ·
    refine ⟨7929587303674580719082791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10572783071566107625443721 7929587303674580719082791)
    ·
      refine ⟨11894380955511871078624187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7929587303674580719082791 11894380955511871078624187)
      ·
        refine ⟨17841571433267806617936281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11894380955511871078624187 17841571433267806617936281)
        ·
          refine ⟨13381178574950854963452211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17841571433267806617936281 13381178574950854963452211)
          ·
            refine ⟨20071767862426282445178317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13381178574950854963452211 20071767862426282445178317)
            ·
              refine ⟨7526912948409855916941869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20071767862426282445178317 7526912948409855916941869)
              ·
                refine ⟨2822592355653695968853201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7526912948409855916941869 2822592355653695968853201)
                ·
                  refine ⟨2116944266740271976639901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2822592355653695968853201 2116944266740271976639901)
                  ·
                    refine ⟨793854100027601991239963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116944266740271976639901 793854100027601991239963)
                    ·
                      rfl

theorem cell22_2319038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2319038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319038 prefixEnd_2319038 := by exact prefixLift 2319038
  have htrace : WordTrace (prefixWord ++ tailWord_2319038) baseStart_2319038 baseEnd_2319038 := by
    simpa [prefixWord, tailWord_2319038, baseEnd_2319038] using wordTrace_append hprefix tailTrace_2319038
  have hstable : (prefixWord ++ tailWord_2319038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319038).length < 2 ^ (prefixWord ++ tailWord_2319038).sum := by decide
  have hdescent : baseEnd_2319038 < baseStart_2319038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319141 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2319141 : Nat := 118140960795 + 2319141 * 2 ^ 59
def prefixEnd_2319141 : Nat := 4983230072969 + 3 ^ 40 * 2319141 * 2
def baseEnd_2319141 : Nat := 264629786344181351971549

theorem tailTrace_2319141 : CollatzResearch.WordTrace tailWord_2319141 prefixEnd_2319141 264629786344181351971549 := by
  unfold tailWord_2319141
  simp only [CollatzResearch.WordTrace]
  refine ⟨84586021291155709594549277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56390680860770473063032851 84586021291155709594549277)
  ·
    refine ⟨31719757984183391097955979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84586021291155709594549277 31719757984183391097955979)
    ·
      refine ⟨47579636976275086646933969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31719757984183391097955979 47579636976275086646933969)
      ·
        refine ⟨35684727732206314985200477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47579636976275086646933969 35684727732206314985200477)
        ·
          refine ⟨13381772899577368119450179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35684727732206314985200477 13381772899577368119450179)
          ·
            refine ⟨20072659349366052179175269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13381772899577368119450179 20072659349366052179175269)
            ·
              refine ⟨3763623628006134783595363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20072659349366052179175269 3763623628006134783595363)
              ·
                refine ⟨5645435442009202175393045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763623628006134783595363 5645435442009202175393045)
                ·
                  refine ⟨264629786344181351971549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5645435442009202175393045 264629786344181351971549)
                  ·
                    rfl

theorem cell22_2319141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2319141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319141 prefixEnd_2319141 := by exact prefixLift 2319141
  have htrace : WordTrace (prefixWord ++ tailWord_2319141) baseStart_2319141 baseEnd_2319141 := by
    simpa [prefixWord, tailWord_2319141, baseEnd_2319141] using wordTrace_append hprefix tailTrace_2319141
  have hstable : (prefixWord ++ tailWord_2319141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319141).length < 2 ^ (prefixWord ++ tailWord_2319141).sum := by decide
  have hdescent : baseEnd_2319141 < baseStart_2319141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319171 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_2319171 : Nat := 118140960795 + 2319171 * 2 ^ 59
def prefixEnd_2319171 : Nat := 4983230072969 + 3 ^ 40 * 2319171 * 2
def baseEnd_2319171 : Nat := 793899628645633977664555

theorem tailTrace_2319171 : CollatzResearch.WordTrace tailWord_2319171 prefixEnd_2319171 793899628645633977664555 := by
  unfold tailWord_2319171
  simp only [CollatzResearch.WordTrace]
  refine ⟨84587115481047024718141367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56391410320698016478760911 84587115481047024718141367)
  ·
    refine ⟨126880673221570537077212051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84587115481047024718141367 126880673221570537077212051)
    ·
      refine ⟨190321009832355805615818077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126880673221570537077212051 190321009832355805615818077)
      ·
        refine ⟨71370378687133427105931779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190321009832355805615818077 71370378687133427105931779)
        ·
          refine ⟨107055568030700140658897669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71370378687133427105931779 107055568030700140658897669)
          ·
            refine ⟨20072919005756276373543313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107055568030700140658897669 20072919005756276373543313)
            ·
              refine ⟨15054689254317207280157485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20072919005756276373543313 15054689254317207280157485)
              ·
                refine ⟨5645508470368952730059057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15054689254317207280157485 5645508470368952730059057)
                ·
                  refine ⟨4234131352776714547544293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5645508470368952730059057 4234131352776714547544293)
                  ·
                    refine ⟨793899628645633977664555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4234131352776714547544293 793899628645633977664555)
                    ·
                      rfl

theorem cell22_2319171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_2319171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319171 prefixEnd_2319171 := by exact prefixLift 2319171
  have htrace : WordTrace (prefixWord ++ tailWord_2319171) baseStart_2319171 baseEnd_2319171 := by
    simpa [prefixWord, tailWord_2319171, baseEnd_2319171] using wordTrace_append hprefix tailTrace_2319171
  have hstable : (prefixWord ++ tailWord_2319171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319171).length < 2 ^ (prefixWord ++ tailWord_2319171).sum := by decide
  have hdescent : baseEnd_2319171 < baseStart_2319171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319207 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2319207 : Nat := 118140960795 + 2319207 * 2 ^ 59
def prefixEnd_2319207 : Nat := 4983230072969 + 3 ^ 40 * 2319207 * 2
def baseEnd_2319207 : Nat := 793911952181341883764445

theorem tailTrace_2319207 : CollatzResearch.WordTrace tailWord_2319207 prefixEnd_2319207 793911952181341883764445 := by
  unfold tailWord_2319207
  simp only [CollatzResearch.WordTrace]
  refine ⟨84588428508916602866451875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56392285672611068577634583 84588428508916602866451875)
  ·
    refine ⟨126882642763374904299677813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84588428508916602866451875 126882642763374904299677813)
    ·
      refine ⟨11895247759066397278094795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126882642763374904299677813 11895247759066397278094795)
      ·
        refine ⟨17842871638599595917142193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11895247759066397278094795 17842871638599595917142193)
        ·
          refine ⟨13382153728949696937856645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17842871638599595917142193 13382153728949696937856645)
          ·
            refine ⟨2509153824178068175848121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13382153728949696937856645 2509153824178068175848121)
            ·
              refine ⟨1881865368133551131886091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2509153824178068175848121 1881865368133551131886091)
              ·
                refine ⟨2822798052200326697829137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881865368133551131886091 2822798052200326697829137)
                ·
                  refine ⟨2117098539150245023371853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2822798052200326697829137 2117098539150245023371853)
                  ·
                    refine ⟨793911952181341883764445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117098539150245023371853 793911952181341883764445)
                    ·
                      rfl

theorem cell22_2319207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2319207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319207 prefixEnd_2319207 := by exact prefixLift 2319207
  have htrace : WordTrace (prefixWord ++ tailWord_2319207) baseStart_2319207 baseEnd_2319207 := by
    simpa [prefixWord, tailWord_2319207, baseEnd_2319207] using wordTrace_append hprefix tailTrace_2319207
  have hstable : (prefixWord ++ tailWord_2319207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319207).length < 2 ^ (prefixWord ++ tailWord_2319207).sum := by decide
  have hdescent : baseEnd_2319207 < baseStart_2319207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319218 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_2319218 : Nat := 118140960795 + 2319218 * 2 ^ 59
def prefixEnd_2319218 : Nat := 4983230072969 + 3 ^ 40 * 2319218 * 2
def baseEnd_2319218 : Nat := 793915717706141521739411

theorem tailTrace_2319218 : CollatzResearch.WordTrace tailWord_2319218 prefixEnd_2319218 793915717706141521739411 := by
  unfold tailWord_2319218
  simp only [CollatzResearch.WordTrace]
  refine ⟨21147207427969187936275577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56392553141251167830068205 21147207427969187936275577)
  ·
    refine ⟨15860405570976890952206683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21147207427969187936275577 15860405570976890952206683)
    ·
      refine ⟨23790608356465336428310025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15860405570976890952206683 23790608356465336428310025)
      ·
        refine ⟨17842956267349002321232519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23790608356465336428310025 17842956267349002321232519)
        ·
          refine ⟨26764434401023503481848779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17842956267349002321232519 26764434401023503481848779)
          ·
            refine ⟨40146651601535255222773169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26764434401023503481848779 40146651601535255222773169)
            ·
              refine ⟨30109988701151441417079877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40146651601535255222773169 30109988701151441417079877)
              ·
                refine ⟨5645622881465895265702477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30109988701151441417079877 5645622881465895265702477)
                ·
                  refine ⟨2117108580549710724638429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5645622881465895265702477 2117108580549710724638429)
                  ·
                    refine ⟨793915717706141521739411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117108580549710724638429 793915717706141521739411)
                    ·
                      rfl

theorem cell22_2319218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_2319218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319218 prefixEnd_2319218 := by exact prefixLift 2319218
  have htrace : WordTrace (prefixWord ++ tailWord_2319218) baseStart_2319218 baseEnd_2319218 := by
    simpa [prefixWord, tailWord_2319218, baseEnd_2319218] using wordTrace_append hprefix tailTrace_2319218
  have hstable : (prefixWord ++ tailWord_2319218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319218).length < 2 ^ (prefixWord ++ tailWord_2319218).sum := by decide
  have hdescent : baseEnd_2319218 < baseStart_2319218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319235 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 1, 3]
def baseStart_2319235 : Nat := 118140960795 + 2319235 * 2 ^ 59
def prefixEnd_2319235 : Nat := 4983230072969 + 3 ^ 40 * 2319235 * 2
def baseEnd_2319235 : Nat := 793921537153559144064359

theorem tailTrace_2319235 : CollatzResearch.WordTrace tailWord_2319235 prefixEnd_2319235 793921537153559144064359 := by
  unfold tailWord_2319235
  simp only [CollatzResearch.WordTrace]
  refine ⟨84589449752815163648471159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56392966501876775765647439 84589449752815163648471159)
  ·
    refine ⟨126884174629222745472706739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84589449752815163648471159 126884174629222745472706739)
    ·
      refine ⟨190326261943834118209060109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126884174629222745472706739 190326261943834118209060109)
      ·
        refine ⟨71372348228937794328397541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190326261943834118209060109 71372348228937794328397541)
        ·
          refine ⟨13382315292925836436574539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71372348228937794328397541 13382315292925836436574539)
          ·
            refine ⟨20073472939388754654861809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13382315292925836436574539 20073472939388754654861809)
            ·
              refine ⟨15055104704541565991146357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20073472939388754654861809 15055104704541565991146357)
              ·
                refine ⟨1411416066050771811669971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15055104704541565991146357 1411416066050771811669971)
                ·
                  refine ⟨2117124099076157717504957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411416066050771811669971 2117124099076157717504957)
                  ·
                    refine ⟨793921537153559144064359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117124099076157717504957 793921537153559144064359)
                    ·
                      rfl

theorem cell22_2319235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 1, 3].length) (baseStart_2319235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319235 prefixEnd_2319235 := by exact prefixLift 2319235
  have htrace : WordTrace (prefixWord ++ tailWord_2319235) baseStart_2319235 baseEnd_2319235 := by
    simpa [prefixWord, tailWord_2319235, baseEnd_2319235] using wordTrace_append hprefix tailTrace_2319235
  have hstable : (prefixWord ++ tailWord_2319235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319235).length < 2 ^ (prefixWord ++ tailWord_2319235).sum := by decide
  have hdescent : baseEnd_2319235 < baseStart_2319235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319252 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2319252 : Nat := 118140960795 + 2319252 * 2 ^ 59
def prefixEnd_2319252 : Nat := 4983230072969 + 3 ^ 40 * 2319252 * 2
def baseEnd_2319252 : Nat := 793927356600976766389307

theorem tailTrace_2319252 : CollatzResearch.WordTrace tailWord_2319252 prefixEnd_2319252 793927356600976766389307 := by
  unfold tailWord_2319252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42295034896876787775920005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56393379862502383701226673 42295034896876787775920005)
  ·
    refine ⟨7930319043164397707985001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42295034896876787775920005 7930319043164397707985001)
    ·
      refine ⟨5947739282373298280988751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7930319043164397707985001 5947739282373298280988751)
      ·
        refine ⟨8921608923559947421483127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947739282373298280988751 8921608923559947421483127)
        ·
          refine ⟨13382413385339921132224691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8921608923559947421483127 13382413385339921132224691)
          ·
            refine ⟨20073620078009881698337037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13382413385339921132224691 20073620078009881698337037)
            ·
              refine ⟨7527607529253705636876389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20073620078009881698337037 7527607529253705636876389)
              ·
                refine ⟨1411426411735069806914323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7527607529253705636876389 1411426411735069806914323)
                ·
                  refine ⟨2117139617602604710371485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411426411735069806914323 2117139617602604710371485)
                  ·
                    refine ⟨793927356600976766389307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117139617602604710371485 793927356600976766389307)
                    ·
                      rfl

theorem cell22_2319252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2319252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319252 prefixEnd_2319252 := by exact prefixLift 2319252
  have htrace : WordTrace (prefixWord ++ tailWord_2319252) baseStart_2319252 baseEnd_2319252 := by
    simpa [prefixWord, tailWord_2319252, baseEnd_2319252] using wordTrace_append hprefix tailTrace_2319252
  have hstable : (prefixWord ++ tailWord_2319252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319252).length < 2 ^ (prefixWord ++ tailWord_2319252).sum := by decide
  have hdescent : baseEnd_2319252 < baseStart_2319252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319263 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_2319263 : Nat := 118140960795 + 2319263 * 2 ^ 59
def prefixEnd_2319263 : Nat := 4983230072969 + 3 ^ 40 * 2319263 * 2
def baseEnd_2319263 : Nat := 793931122125776404364273

theorem tailTrace_2319263 : CollatzResearch.WordTrace tailWord_2319263 prefixEnd_2319263 793931122125776404364273 := by
  unfold tailWord_2319263
  simp only [CollatzResearch.WordTrace]
  refine ⟨84590470996713724430490443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56393647331142482953660295 84590470996713724430490443)
  ·
    refine ⟨126885706495070586645735665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84590470996713724430490443 126885706495070586645735665)
    ·
      refine ⟨95164279871302939984301749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126885706495070586645735665 95164279871302939984301749)
      ·
        refine ⟨8921651237934650623528289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95164279871302939984301749 8921651237934650623528289)
        ·
          refine ⟨6691238428450987967646217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8921651237934650623528289 6691238428450987967646217)
          ·
            refine ⟨5018428821338240975734663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6691238428450987967646217 5018428821338240975734663)
            ·
              refine ⟨7527643232007361463601995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5018428821338240975734663 7527643232007361463601995)
              ·
                refine ⟨11291464848011042195402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7527643232007361463601995 11291464848011042195402993)
                ·
                  refine ⟨8468598636008281646552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11291464848011042195402993 8468598636008281646552245)
                  ·
                    refine ⟨793931122125776404364273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8468598636008281646552245 793931122125776404364273)
                    ·
                      rfl

theorem cell22_2319263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_2319263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319263 prefixEnd_2319263 := by exact prefixLift 2319263
  have htrace : WordTrace (prefixWord ++ tailWord_2319263) baseStart_2319263 baseEnd_2319263 := by
    simpa [prefixWord, tailWord_2319263, baseEnd_2319263] using wordTrace_append hprefix tailTrace_2319263
  have hstable : (prefixWord ++ tailWord_2319263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319263).length < 2 ^ (prefixWord ++ tailWord_2319263).sum := by decide
  have hdescent : baseEnd_2319263 < baseStart_2319263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319276 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_2319276 : Nat := 118140960795 + 2319276 * 2 ^ 59
def prefixEnd_2319276 : Nat := 4983230072969 + 3 ^ 40 * 2319276 * 2
def baseEnd_2319276 : Nat := 264645190763816234596411

theorem tailTrace_2319276 : CollatzResearch.WordTrace tailWord_2319276 prefixEnd_2319276 264645190763816234596411 := by
  unfold tailWord_2319276
  simp only [CollatzResearch.WordTrace]
  refine ⟨42295472572833313825356841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56393963430444418433809121 42295472572833313825356841)
  ·
    refine ⟨31721604429624985369017631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42295472572833313825356841 31721604429624985369017631)
    ·
      refine ⟨47582406644437478053526447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31721604429624985369017631 47582406644437478053526447)
      ·
        refine ⟨71373609966656217080289671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47582406644437478053526447 71373609966656217080289671)
        ·
          refine ⟨107060414949984325620434507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71373609966656217080289671 107060414949984325620434507)
          ·
            refine ⟨160590622424976488430651761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107060414949984325620434507 160590622424976488430651761)
            ·
              refine ⟨120442966818732366322988821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160590622424976488430651761 120442966818732366322988821)
              ·
                refine ⟨5645764069628079671390101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120442966818732366322988821 5645764069628079671390101)
                ·
                  refine ⟨264645190763816234596411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5645764069628079671390101 264645190763816234596411)
                  ·
                    rfl

theorem cell22_2319276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_2319276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319276 prefixEnd_2319276 := by exact prefixLift 2319276
  have htrace : WordTrace (prefixWord ++ tailWord_2319276) baseStart_2319276 baseEnd_2319276 := by
    simpa [prefixWord, tailWord_2319276, baseEnd_2319276] using wordTrace_append hprefix tailTrace_2319276
  have hstable : (prefixWord ++ tailWord_2319276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319276).length < 2 ^ (prefixWord ++ tailWord_2319276).sum := by decide
  have hdescent : baseEnd_2319276 < baseStart_2319276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319310 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_2319310 : Nat := 118140960795 + 2319310 * 2 ^ 59
def prefixEnd_2319310 : Nat := 4983230072969 + 3 ^ 40 * 2319310 * 2
def baseEnd_2319310 : Nat := 264649070395427982813043

theorem tailTrace_2319310 : CollatzResearch.WordTrace tailWord_2319310 prefixEnd_2319310 264649070395427982813043 := by
  unfold tailWord_2319310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574023153442931432181423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56394790151695634304967589 10574023153442931432181423)
  ·
    refine ⟨15861034730164397148272135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10574023153442931432181423 15861034730164397148272135)
    ·
      refine ⟨23791552095246595722408203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15861034730164397148272135 23791552095246595722408203)
      ·
        refine ⟨35687328142869893583612305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23791552095246595722408203 35687328142869893583612305)
        ·
          refine ⟨26765496107152420187709229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35687328142869893583612305 26765496107152420187709229)
          ·
            refine ⟨10037061040182157570390961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26765496107152420187709229 10037061040182157570390961)
            ·
              refine ⟨7527795780136618177793221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10037061040182157570390961 7527795780136618177793221)
              ·
                refine ⟨1411461708775615908336229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7527795780136618177793221 1411461708775615908336229)
                ·
                  refine ⟨264649070395427982813043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1411461708775615908336229 264649070395427982813043)
                  ·
                    rfl

theorem cell22_2319310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_2319310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319310 prefixEnd_2319310 := by exact prefixLift 2319310
  have htrace : WordTrace (prefixWord ++ tailWord_2319310) baseStart_2319310 baseEnd_2319310 := by
    simpa [prefixWord, tailWord_2319310, baseEnd_2319310] using wordTrace_append hprefix tailTrace_2319310
  have hstable : (prefixWord ++ tailWord_2319310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319310).length < 2 ^ (prefixWord ++ tailWord_2319310).sum := by decide
  have hdescent : baseEnd_2319310 < baseStart_2319310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2319325 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2319325 : Nat := 118140960795 + 2319325 * 2 ^ 59
def prefixEnd_2319325 : Nat := 4983230072969 + 3 ^ 40 * 2319325 * 2
def baseEnd_2319325 : Nat := 793952345992828909314083

theorem tailTrace_2319325 : CollatzResearch.WordTrace tailWord_2319325 prefixEnd_2319325 793952345992828909314083 := by
  unfold tailWord_2319325
  simp only [CollatzResearch.WordTrace]
  refine ⟨84592732322489109019247429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56395154881659406012831619 84592732322489109019247429)
  ·
    refine ⟨15861137310466707941108893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84592732322489109019247429 15861137310466707941108893)
    ·
      refine ⟨5947926491425015477915835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15861137310466707941108893 5947926491425015477915835)
      ·
        refine ⟨8921889737137523216873753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947926491425015477915835 8921889737137523216873753)
        ·
          refine ⟨6691417302853142412655315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8921889737137523216873753 6691417302853142412655315)
          ·
            refine ⟨10037125954279713618982973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691417302853142412655315 10037125954279713618982973)
            ·
              refine ⟨3763922232854892607118615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10037125954279713618982973 3763922232854892607118615)
              ·
                refine ⟨5645883349282338910677923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763922232854892607118615 5645883349282338910677923)
                ·
                  refine ⟨8468825023923508366016885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5645883349282338910677923 8468825023923508366016885)
                  ·
                    refine ⟨793952345992828909314083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8468825023923508366016885 793952345992828909314083)
                    ·
                      rfl

theorem cell22_2319325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2319325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2319325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2319325 prefixEnd_2319325 := by exact prefixLift 2319325
  have htrace : WordTrace (prefixWord ++ tailWord_2319325) baseStart_2319325 baseEnd_2319325 := by
    simpa [prefixWord, tailWord_2319325, baseEnd_2319325] using wordTrace_append hprefix tailTrace_2319325
  have hstable : (prefixWord ++ tailWord_2319325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2319325).length < 2 ^ (prefixWord ++ tailWord_2319325).sum := by decide
  have hdescent : baseEnd_2319325 < baseStart_2319325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2319325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
