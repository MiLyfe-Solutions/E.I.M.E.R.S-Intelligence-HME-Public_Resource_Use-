import V185TrunkScan23Chunk1141

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6764145 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_6764145 : Nat := 118140960795 + 6764145 * 2 ^ 59
def prefixEnd_6764145 : Nat := 4983230072969 + 3 ^ 40 * 6764145 * 2
def baseEnd_6764145 : Nat := 3473257601706542985279769

theorem tailTrace_6764145 : CollatzResearch.WordTrace tailWord_6764145 prefixEnd_6764145 3473257601706542985279769 := by
  unfold tailWord_6764145
  simp only [CollatzResearch.WordTrace]
  refine ⟨246708636079665363839029889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164472424053110242559353259 246708636079665363839029889)
  ·
    refine ⟨185031477059749022879272417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246708636079665363839029889 185031477059749022879272417)
    ·
      refine ⟨138773607794811767159454313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185031477059749022879272417 138773607794811767159454313)
      ·
        refine ⟨104080205846108825369590735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138773607794811767159454313 104080205846108825369590735)
        ·
          refine ⟨156120308769163238054386103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104080205846108825369590735 156120308769163238054386103)
          ·
            refine ⟨234180463153744857081579155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156120308769163238054386103 234180463153744857081579155)
            ·
              refine ⟨351270694730617285622368733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234180463153744857081579155 351270694730617285622368733)
              ·
                refine ⟨131726510523981482108388275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351270694730617285622368733 131726510523981482108388275)
                ·
                  refine ⟨197589765785972223162582413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131726510523981482108388275 197589765785972223162582413)
                  ·
                    refine ⟨74096162169739583685968405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197589765785972223162582413 74096162169739583685968405)
                    ·
                      refine ⟨3473257601706542985279769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74096162169739583685968405 3473257601706542985279769)
                      ·
                        rfl

theorem cell23_6764145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_6764145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764145 prefixEnd_6764145 := by exact prefixLift 6764145
  have htrace : WordTrace (prefixWord ++ tailWord_6764145) baseStart_6764145 baseEnd_6764145 := by
    simpa [prefixWord, tailWord_6764145, baseEnd_6764145] using wordTrace_append hprefix tailTrace_6764145
  have hstable : (prefixWord ++ tailWord_6764145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764145).length < 2 ^ (prefixWord ++ tailWord_6764145).sum := by decide
  have hdescent : baseEnd_6764145 < baseStart_6764145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764149 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6764149 : Nat := 118140960795 + 6764149 * 2 ^ 59
def prefixEnd_6764149 : Nat := 4983230072969 + 3 ^ 40 * 6764149 * 2
def baseEnd_6764149 : Nat := 3473259655629160969629751

theorem tailTrace_6764149 : CollatzResearch.WordTrace tailWord_6764149 prefixEnd_6764149 3473259655629160969629751 := by
  unfold tailWord_6764149
  simp only [CollatzResearch.WordTrace]
  refine ⟨246708781971650872522175501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164472521314433915014783667 246708781971650872522175501)
  ·
    refine ⟨92515793239369077195815813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246708781971650872522175501 92515793239369077195815813)
    ·
      refine ⟨17346711232381701974215465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92515793239369077195815813 17346711232381701974215465)
      ·
        refine ⟨13010033424286276480661599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17346711232381701974215465 13010033424286276480661599)
        ·
          refine ⟨19515050136429414720992399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13010033424286276480661599 19515050136429414720992399)
          ·
            refine ⟨29272575204644122081488599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19515050136429414720992399 29272575204644122081488599)
            ·
              refine ⟨43908862806966183122232899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29272575204644122081488599 43908862806966183122232899)
              ·
                refine ⟨65863294210449274683349349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43908862806966183122232899 65863294210449274683349349)
                ·
                  refine ⟨12349367664459239003128003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65863294210449274683349349 12349367664459239003128003)
                  ·
                    refine ⟨18524051496688858504692005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12349367664459239003128003 18524051496688858504692005)
                    ·
                      refine ⟨3473259655629160969629751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18524051496688858504692005 3473259655629160969629751)
                      ·
                        rfl

theorem cell23_6764149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6764149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764149 prefixEnd_6764149 := by exact prefixLift 6764149
  have htrace : WordTrace (prefixWord ++ tailWord_6764149) baseStart_6764149 baseEnd_6764149 := by
    simpa [prefixWord, tailWord_6764149, baseEnd_6764149] using wordTrace_append hprefix tailTrace_6764149
  have hstable : (prefixWord ++ tailWord_6764149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764149).length < 2 ^ (prefixWord ++ tailWord_6764149).sum := by decide
  have hdescent : baseEnd_6764149 < baseStart_6764149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764155 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 8]
def baseStart_6764155 : Nat := 118140960795 + 6764155 * 2 ^ 59
def prefixEnd_6764155 : Nat := 4983230072969 + 3 ^ 40 * 6764155 * 2
def baseEnd_6764155 : Nat := 385918081834787549572747

theorem tailTrace_6764155 : CollatzResearch.WordTrace tailWord_6764155 prefixEnd_6764155 385918081834787549572747 := by
  unfold tailWord_6764155
  simp only [CollatzResearch.WordTrace]
  refine ⟨246709000809629135546893919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164472667206419423697929279 246709000809629135546893919)
  ·
    refine ⟨370063501214443703320340879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246709000809629135546893919 370063501214443703320340879)
    ·
      refine ⟨555095251821665554980511319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370063501214443703320340879 555095251821665554980511319)
      ·
        refine ⟨832642877732498332470766979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555095251821665554980511319 832642877732498332470766979)
        ·
          refine ⟨1248964316598747498706150469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832642877732498332470766979 1248964316598747498706150469)
          ·
            refine ⟨234180809362265156007403213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1248964316598747498706150469 234180809362265156007403213)
            ·
              refine ⟨87817803510849433502776205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234180809362265156007403213 87817803510849433502776205)
              ·
                refine ⟨32931676316568537563541077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87817803510849433502776205 32931676316568537563541077)
                ·
                  refine ⟨385918081834787549572747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32931676316568537563541077 385918081834787549572747)
                  ·
                    rfl

theorem cell23_6764155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 8].length) (baseStart_6764155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764155 prefixEnd_6764155 := by exact prefixLift 6764155
  have htrace : WordTrace (prefixWord ++ tailWord_6764155) baseStart_6764155 baseEnd_6764155 := by
    simpa [prefixWord, tailWord_6764155, baseEnd_6764155] using wordTrace_append hprefix tailTrace_6764155
  have hstable : (prefixWord ++ tailWord_6764155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764155).length < 2 ^ (prefixWord ++ tailWord_6764155).sum := by decide
  have hdescent : baseEnd_6764155 < baseStart_6764155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764172 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 6]
def baseStart_6764172 : Nat := 118140960795 + 6764172 * 2 ^ 59
def prefixEnd_6764172 : Nat := 4983230072969 + 3 ^ 40 * 6764172 * 2
def baseEnd_6764172 : Nat := 385919051742690486626905

theorem tailTrace_6764172 : CollatzResearch.WordTrace tailWord_6764172 prefixEnd_6764172 385919051742690486626905 := by
  unfold tailWord_6764172
  simp only [CollatzResearch.WordTrace]
  refine ⟨123354810425283773725131385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164473080567045031633508513 123354810425283773725131385)
  ·
    refine ⟨92516107818962830293848539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123354810425283773725131385 92516107818962830293848539)
    ·
      refine ⟨138774161728444245440772809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92516107818962830293848539 138774161728444245440772809)
      ·
        refine ⟨104080621296333184080579607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138774161728444245440772809 104080621296333184080579607)
        ·
          refine ⟨156120931944499776120869411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104080621296333184080579607 156120931944499776120869411)
          ·
            refine ⟨234181397916749664181304117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156120931944499776120869411 234181397916749664181304117)
            ·
              refine ⟨21954506054695281016997261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234181397916749664181304117 21954506054695281016997261)
              ·
                refine ⟨8232939770510730381373973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21954506054695281016997261 8232939770510730381373973)
                ·
                  refine ⟨385919051742690486626905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8232939770510730381373973 385919051742690486626905)
                  ·
                    rfl

theorem cell23_6764172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_6764172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764172 prefixEnd_6764172 := by exact prefixLift 6764172
  have htrace : WordTrace (prefixWord ++ tailWord_6764172) baseStart_6764172 baseEnd_6764172 := by
    simpa [prefixWord, tailWord_6764172, baseEnd_6764172] using wordTrace_append hprefix tailTrace_6764172
  have hstable : (prefixWord ++ tailWord_6764172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764172).length < 2 ^ (prefixWord ++ tailWord_6764172).sum := by decide
  have hdescent : baseEnd_6764172 < baseStart_6764172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764253 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6764253 : Nat := 118140960795 + 6764253 * 2 ^ 59
def prefixEnd_6764253 : Nat := 4983230072969 + 3 ^ 40 * 6764253 * 2
def baseEnd_6764253 : Nat := 1157771019205742854243091

theorem tailTrace_6764253 : CollatzResearch.WordTrace tailWord_6764253 prefixEnd_6764253 1157771019205742854243091 := by
  unfold tailWord_6764253
  simp only [CollatzResearch.WordTrace]
  refine ⟨246712575163274098283961413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164475050108849398855974275 246712575163274098283961413)
  ·
    refine ⟨46258607843113893428242765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246712575163274098283961413 46258607843113893428242765)
    ·
      refine ⟨17346977941167710035591037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46258607843113893428242765 17346977941167710035591037)
      ·
        refine ⟨6505116727937891263346639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17346977941167710035591037 6505116727937891263346639)
        ·
          refine ⟨9757675091906836895019959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505116727937891263346639 9757675091906836895019959)
          ·
            refine ⟨14636512637860255342529939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9757675091906836895019959 14636512637860255342529939)
            ·
              refine ⟨21954768956790383013794909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14636512637860255342529939 21954768956790383013794909)
              ·
                refine ⟨8233038358796393630173091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21954768956790383013794909 8233038358796393630173091)
                ·
                  refine ⟨12349557538194590445259637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233038358796393630173091 12349557538194590445259637)
                  ·
                    refine ⟨1157771019205742854243091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12349557538194590445259637 1157771019205742854243091)
                    ·
                      rfl

theorem cell23_6764253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6764253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764253 prefixEnd_6764253 := by exact prefixLift 6764253
  have htrace : WordTrace (prefixWord ++ tailWord_6764253) baseStart_6764253 baseEnd_6764253 := by
    simpa [prefixWord, tailWord_6764253, baseEnd_6764253] using wordTrace_append hprefix tailTrace_6764253
  have hstable : (prefixWord ++ tailWord_6764253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764253).length < 2 ^ (prefixWord ++ tailWord_6764253).sum := by decide
  have hdescent : baseEnd_6764253 < baseStart_6764253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764256 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4]
def baseStart_6764256 : Nat := 118140960795 + 6764256 * 2 ^ 59
def prefixEnd_6764256 : Nat := 4983230072969 + 3 ^ 40 * 6764256 * 2
def baseEnd_6764256 : Nat := 3473314598059192050991759

theorem tailTrace_6764256 : CollatzResearch.WordTrace tailWord_6764256 prefixEnd_6764256 3473314598059192050991759 := by
  unfold tailWord_6764256
  simp only [CollatzResearch.WordTrace]
  refine ⟨123356342291131614898160311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164475123054842153197547081 123356342291131614898160311)
  ·
    refine ⟨185034513436697422347240467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123356342291131614898160311 185034513436697422347240467)
    ·
      refine ⟨277551770155046133520860701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185034513436697422347240467 277551770155046133520860701)
      ·
        refine ⟨104081913808142300070322763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277551770155046133520860701 104081913808142300070322763)
        ·
          refine ⟨156122870712213450105484145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104081913808142300070322763 156122870712213450105484145)
          ·
            refine ⟨117092153034160087579113109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156122870712213450105484145 117092153034160087579113109)
            ·
              refine ⟨5488694673476254105270927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117092153034160087579113109 5488694673476254105270927)
              ·
                refine ⟨8233042010214381157906391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488694673476254105270927 8233042010214381157906391)
                ·
                  refine ⟨12349563015321571736859587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233042010214381157906391 12349563015321571736859587)
                  ·
                    refine ⟨18524344522982357605289381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12349563015321571736859587 18524344522982357605289381)
                    ·
                      refine ⟨3473314598059192050991759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18524344522982357605289381 3473314598059192050991759)
                      ·
                        rfl

theorem cell23_6764256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_6764256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764256 prefixEnd_6764256 := by exact prefixLift 6764256
  have htrace : WordTrace (prefixWord ++ tailWord_6764256) baseStart_6764256 baseEnd_6764256 := by
    simpa [prefixWord, tailWord_6764256, baseEnd_6764256] using wordTrace_append hprefix tailTrace_6764256
  have hstable : (prefixWord ++ tailWord_6764256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764256).length < 2 ^ (prefixWord ++ tailWord_6764256).sum := by decide
  have hdescent : baseEnd_6764256 < baseStart_6764256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764266 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_6764266 : Nat := 118140960795 + 6764266 * 2 ^ 59
def prefixEnd_6764266 : Nat := 4983230072969 + 3 ^ 40 * 6764266 * 2
def baseEnd_6764266 : Nat := 1157773244288579003955571

theorem tailTrace_6764266 : CollatzResearch.WordTrace tailWord_6764266 prefixEnd_6764266 1157773244288579003955571 := by
  unfold tailWord_6764266
  simp only [CollatzResearch.WordTrace]
  refine ⟨61678262328056750376046163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164475366208151334336123101 61678262328056750376046163)
  ·
    refine ⟨92517393492085125564069245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61678262328056750376046163 92517393492085125564069245)
    ·
      refine ⟨34694022559531922086525967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92517393492085125564069245 34694022559531922086525967)
      ·
        refine ⟨52041033839297883129788951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34694022559531922086525967 52041033839297883129788951)
        ·
          refine ⟨78061550758946824694683427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52041033839297883129788951 78061550758946824694683427)
          ·
            refine ⟨117092326138420237042025141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78061550758946824694683427 117092326138420237042025141)
            ·
              refine ⟨10977405575476897222689857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117092326138420237042025141 10977405575476897222689857)
              ·
                refine ⟨8233054181607672917017393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10977405575476897222689857 8233054181607672917017393)
                ·
                  refine ⟨6174790636205754687763045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233054181607672917017393 6174790636205754687763045)
                  ·
                    refine ⟨1157773244288579003955571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6174790636205754687763045 1157773244288579003955571)
                    ·
                      rfl

theorem cell23_6764266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_6764266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764266 prefixEnd_6764266 := by exact prefixLift 6764266
  have htrace : WordTrace (prefixWord ++ tailWord_6764266) baseStart_6764266 baseEnd_6764266 := by
    simpa [prefixWord, tailWord_6764266, baseEnd_6764266] using wordTrace_append hprefix tailTrace_6764266
  have hstable : (prefixWord ++ tailWord_6764266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764266).length < 2 ^ (prefixWord ++ tailWord_6764266).sum := by decide
  have hdescent : baseEnd_6764266 < baseStart_6764266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764273 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_6764273 : Nat := 118140960795 + 6764273 * 2 ^ 59
def prefixEnd_6764273 : Nat := 4983230072969 + 3 ^ 40 * 6764273 * 2
def baseEnd_6764273 : Nat := 3473323327230318484479181

theorem tailTrace_6764273 : CollatzResearch.WordTrace tailWord_6764273 prefixEnd_6764273 3473323327230318484479181 := by
  unfold tailWord_6764273
  simp only [CollatzResearch.WordTrace]
  refine ⟨246713304623201641699689473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164475536415467761133126315 246713304623201641699689473)
  ·
    refine ⟨185034978467401231274767105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246713304623201641699689473 185034978467401231274767105)
    ·
      refine ⟨138776233850550923456075329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185034978467401231274767105 138776233850550923456075329)
      ·
        refine ⟨104082175387913192592056497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138776233850550923456075329 104082175387913192592056497)
        ·
          refine ⟨78061631540934894444042373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104082175387913192592056497 78061631540934894444042373)
          ·
            refine ⟨14636555913925292708257945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78061631540934894444042373 14636555913925292708257945)
            ·
              refine ⟨10977416935443969531193459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14636555913925292708257945 10977416935443969531193459)
              ·
                refine ⟨16466125403165954296790189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10977416935443969531193459 16466125403165954296790189)
                ·
                  refine ⟨6174797026187232861296321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16466125403165954296790189 6174797026187232861296321)
                  ·
                    refine ⟨4631097769640424645972241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6174797026187232861296321 4631097769640424645972241)
                    ·
                      refine ⟨3473323327230318484479181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631097769640424645972241 3473323327230318484479181)
                      ·
                        rfl

theorem cell23_6764273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_6764273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764273 prefixEnd_6764273 := by exact prefixLift 6764273
  have htrace : WordTrace (prefixWord ++ tailWord_6764273) baseStart_6764273 baseEnd_6764273 := by
    simpa [prefixWord, tailWord_6764273, baseEnd_6764273] using wordTrace_append hprefix tailTrace_6764273
  have hstable : (prefixWord ++ tailWord_6764273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764273).length < 2 ^ (prefixWord ++ tailWord_6764273).sum := by decide
  have hdescent : baseEnd_6764273 < baseStart_6764273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764286 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6764286 : Nat := 118140960795 + 6764286 * 2 ^ 59
def prefixEnd_6764286 : Nat := 4983230072969 + 3 ^ 40 * 6764286 * 2
def baseEnd_6764286 : Nat := 3473330002478826933616621

theorem tailTrace_6764286 : CollatzResearch.WordTrace tailWord_6764286 prefixEnd_6764286 3473330002478826933616621 := by
  unfold tailWord_6764286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30839222346519318114989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164475852514769696613275141 30839222346519318114989089)
  ·
    refine ⟨23129416759889488586241817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30839222346519318114989089 23129416759889488586241817)
    ·
      refine ⟨17347062569917116439681363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23129416759889488586241817 17347062569917116439681363)
      ·
        refine ⟨26020593854875674659522045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347062569917116439681363 26020593854875674659522045)
        ·
          refine ⟨9757722695578377997320767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26020593854875674659522045 9757722695578377997320767)
          ·
            refine ⟨14636584043367566995981151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9757722695578377997320767 14636584043367566995981151)
            ·
              refine ⟨21954876065051350493971727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14636584043367566995981151 21954876065051350493971727)
              ·
                refine ⟨32932314097577025740957591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21954876065051350493971727 32932314097577025740957591)
                ·
                  refine ⟨49398471146365538611436387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32932314097577025740957591 49398471146365538611436387)
                  ·
                    refine ⟨74097706719548307917154581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49398471146365538611436387 74097706719548307917154581)
                    ·
                      refine ⟨3473330002478826933616621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74097706719548307917154581 3473330002478826933616621)
                      ·
                        rfl

theorem cell23_6764286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6764286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764286 prefixEnd_6764286 := by exact prefixLift 6764286
  have htrace : WordTrace (prefixWord ++ tailWord_6764286) baseStart_6764286 baseEnd_6764286 := by
    simpa [prefixWord, tailWord_6764286, baseEnd_6764286] using wordTrace_append hprefix tailTrace_6764286
  have hstable : (prefixWord ++ tailWord_6764286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764286).length < 2 ^ (prefixWord ++ tailWord_6764286).sum := by decide
  have hdescent : baseEnd_6764286 < baseStart_6764286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764329 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 8, 2]
def baseStart_6764329 : Nat := 118140960795 + 6764329 * 2 ^ 59
def prefixEnd_6764329 : Nat := 4983230072969 + 3 ^ 40 * 6764329 * 2
def baseEnd_6764329 : Nat := 3473352082146970265378923

theorem tailTrace_6764329 : CollatzResearch.WordTrace tailWord_6764329 prefixEnd_6764329 3473352082146970265378923 := by
  unfold tailWord_6764329
  simp only [CollatzResearch.WordTrace]
  refine ⟨246715347110998763263728041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164476898073999175509152027 246715347110998763263728041)
  ·
    refine ⟨185036510333249072447796031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246715347110998763263728041 185036510333249072447796031)
    ·
      refine ⟨277554765499873608671694047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185036510333249072447796031 277554765499873608671694047)
      ·
        refine ⟨416332148249810413007541071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277554765499873608671694047 416332148249810413007541071)
        ·
          refine ⟨624498222374715619511311607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416332148249810413007541071 624498222374715619511311607)
          ·
            refine ⟨936747333562073429266967411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624498222374715619511311607 936747333562073429266967411)
            ·
              refine ⟨1405121000343110143900451117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936747333562073429266967411 1405121000343110143900451117)
              ·
                refine ⟨526920375128666303962669169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405121000343110143900451117 526920375128666303962669169)
                ·
                  refine ⟨395190281346499727972001877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526920375128666303962669169 395190281346499727972001877)
                  ·
                    refine ⟨4631136109529293687171897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 395190281346499727972001877 4631136109529293687171897)
                    ·
                      refine ⟨3473352082146970265378923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631136109529293687171897 3473352082146970265378923)
                      ·
                        rfl

theorem cell23_6764329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8, 2].length) (baseStart_6764329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764329 prefixEnd_6764329 := by exact prefixLift 6764329
  have htrace : WordTrace (prefixWord ++ tailWord_6764329) baseStart_6764329 baseEnd_6764329 := by
    simpa [prefixWord, tailWord_6764329, baseEnd_6764329] using wordTrace_append hprefix tailTrace_6764329
  have hstable : (prefixWord ++ tailWord_6764329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764329).length < 2 ^ (prefixWord ++ tailWord_6764329).sum := by decide
  have hdescent : baseEnd_6764329 < baseStart_6764329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764340 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_6764340 : Nat := 118140960795 + 6764340 * 2 ^ 59
def prefixEnd_6764340 : Nat := 4983230072969 + 3 ^ 40 * 6764340 * 2
def baseEnd_6764340 : Nat := 3473357730434169722341373

theorem tailTrace_6764340 : CollatzResearch.WordTrace tailWord_6764340 prefixEnd_6764340 3473357730434169722341373 := by
  unfold tailWord_6764340
  simp only [CollatzResearch.WordTrace]
  refine ⟨123357874156979456071189237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164477165542639274761585649 123357874156979456071189237)
  ·
    refine ⟨11564800702216824006673991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123357874156979456071189237 11564800702216824006673991)
    ·
      refine ⟨17347201053325236010010987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564800702216824006673991 17347201053325236010010987)
      ·
        refine ⟨26020801579987854015016481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347201053325236010010987 26020801579987854015016481)
        ·
          refine ⟨19515601184990890511262361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26020801579987854015016481 19515601184990890511262361)
          ·
            refine ⟨14636700888743167883446771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19515601184990890511262361 14636700888743167883446771)
            ·
              refine ⟨21955051333114751825170157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14636700888743167883446771 21955051333114751825170157)
              ·
                refine ⟨8233144249918031934438809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21955051333114751825170157 8233144249918031934438809)
                ·
                  refine ⟨6174858187438523950829107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233144249918031934438809 6174858187438523950829107)
                  ·
                    refine ⟨9262287281157785926243661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174858187438523950829107 9262287281157785926243661)
                    ·
                      refine ⟨3473357730434169722341373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9262287281157785926243661 3473357730434169722341373)
                      ·
                        rfl

theorem cell23_6764340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_6764340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764340 prefixEnd_6764340 := by exact prefixLift 6764340
  have htrace : WordTrace (prefixWord ++ tailWord_6764340) baseStart_6764340 baseEnd_6764340 := by
    simpa [prefixWord, tailWord_6764340, baseEnd_6764340] using wordTrace_append hprefix tailTrace_6764340
  have hstable : (prefixWord ++ tailWord_6764340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764340).length < 2 ^ (prefixWord ++ tailWord_6764340).sum := by decide
  have hdescent : baseEnd_6764340 < baseStart_6764340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764350 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_6764350 : Nat := 118140960795 + 6764350 * 2 ^ 59
def prefixEnd_6764350 : Nat := 4983230072969 + 3 ^ 40 * 6764350 * 2
def baseEnd_6764350 : Nat := 3473362865240714683216327

theorem tailTrace_6764350 : CollatzResearch.WordTrace tailWord_6764350 prefixEnd_6764350 3473362865240714683216327 := by
  unfold tailWord_6764350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30839514130490335481280313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164477408695948455900161669 30839514130490335481280313)
  ·
    refine ⟨23129635597867751610960235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30839514130490335481280313 23129635597867751610960235)
    ·
      refine ⟨34694453396801627416440353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23129635597867751610960235 34694453396801627416440353)
      ·
        refine ⟨26020840047601220562330265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34694453396801627416440353 26020840047601220562330265)
        ·
          refine ⟨19515630035700915421747699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26020840047601220562330265 19515630035700915421747699)
          ·
            refine ⟨29273445053551373132621549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19515630035700915421747699 29273445053551373132621549)
            ·
              refine ⟨10977541895081764924733081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29273445053551373132621549 10977541895081764924733081)
              ·
                refine ⟨8233156421311323693549811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10977541895081764924733081 8233156421311323693549811)
                ·
                  refine ⟨12349734631966985540324717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233156421311323693549811 12349734631966985540324717)
                  ·
                    refine ⟨4631150486987619577621769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12349734631966985540324717 4631150486987619577621769)
                    ·
                      refine ⟨3473362865240714683216327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631150486987619577621769 3473362865240714683216327)
                      ·
                        rfl

theorem cell23_6764350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_6764350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764350 prefixEnd_6764350 := by exact prefixLift 6764350
  have htrace : WordTrace (prefixWord ++ tailWord_6764350) baseStart_6764350 baseEnd_6764350 := by
    simpa [prefixWord, tailWord_6764350, baseEnd_6764350] using wordTrace_append hprefix tailTrace_6764350
  have hstable : (prefixWord ++ tailWord_6764350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764350).length < 2 ^ (prefixWord ++ tailWord_6764350).sum := by decide
  have hdescent : baseEnd_6764350 < baseStart_6764350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764396 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_6764396 : Nat := 118140960795 + 6764396 * 2 ^ 59
def prefixEnd_6764396 : Nat := 4983230072969 + 3 ^ 40 * 6764396 * 2
def baseEnd_6764396 : Nat := 3473386485350821503241115

theorem tailTrace_6764396 : CollatzResearch.WordTrace tailWord_6764396 prefixEnd_6764396 3473386485350821503241115 := by
  unfold tailWord_6764396
  simp only [CollatzResearch.WordTrace]
  refine ⟨123358895400878016853208521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164478527201170689137611361 123358895400878016853208521)
  ·
    refine ⟨92519171550658512639906391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123358895400878016853208521 92519171550658512639906391)
    ·
      refine ⟨138778757325987768959859587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92519171550658512639906391 138778757325987768959859587)
      ·
        refine ⟨208168135988981653439789381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138778757325987768959859587 208168135988981653439789381)
        ·
          refine ⟨39031525497934060019960509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208168135988981653439789381 39031525497934060019960509)
          ·
            refine ⟨14636822061725272507485191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39031525497934060019960509 14636822061725272507485191)
            ·
              refine ⟨21955233092587908761227787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14636822061725272507485191 21955233092587908761227787)
              ·
                refine ⟨32932849638881863141841681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21955233092587908761227787 32932849638881863141841681)
                ·
                  refine ⟨24699637229161397356381261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32932849638881863141841681 24699637229161397356381261)
                  ·
                    refine ⟨9262363960935524008642973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24699637229161397356381261 9262363960935524008642973)
                    ·
                      refine ⟨3473386485350821503241115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9262363960935524008642973 3473386485350821503241115)
                      ·
                        rfl

theorem cell23_6764396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_6764396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764396 prefixEnd_6764396 := by exact prefixLift 6764396
  have htrace : WordTrace (prefixWord ++ tailWord_6764396) baseStart_6764396 baseEnd_6764396 := by
    simpa [prefixWord, tailWord_6764396, baseEnd_6764396] using wordTrace_append hprefix tailTrace_6764396
  have hstable : (prefixWord ++ tailWord_6764396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764396).length < 2 ^ (prefixWord ++ tailWord_6764396).sum := by decide
  have hdescent : baseEnd_6764396 < baseStart_6764396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764536 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_6764536 : Nat := 118140960795 + 6764536 * 2 ^ 59
def prefixEnd_6764536 : Nat := 4983230072969 + 3 ^ 40 * 6764536 * 2
def baseEnd_6764536 : Nat := 1157819457547483651830157

theorem tailTrace_6764536 : CollatzResearch.WordTrace tailWord_6764536 prefixEnd_6764536 1157819457547483651830157 := by
  unfold tailWord_6764536
  simp only [CollatzResearch.WordTrace]
  refine ⟨123361448510624418808256731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164481931347499225077675641 123361448510624418808256731)
  ·
    refine ⟨185042172765936628212385097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123361448510624418808256731 185042172765936628212385097)
    ·
      refine ⟨138781629574452471159288823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185042172765936628212385097 138781629574452471159288823)
      ·
        refine ⟨208172444361678706738933235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138781629574452471159288823 208172444361678706738933235)
        ·
          refine ⟨312258666542518060108399853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208172444361678706738933235 312258666542518060108399853)
          ·
            refine ⟨117096999953444272540649945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312258666542518060108399853 117096999953444272540649945)
            ·
              refine ⟨87822749965083204405487459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117096999953444272540649945 87822749965083204405487459)
              ·
                refine ⟨131734124947624806608231189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87822749965083204405487459 131734124947624806608231189)
                ·
                  refine ⟨6175037106919912809760837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131734124947624806608231189 6175037106919912809760837)
                  ·
                    refine ⟨1157819457547483651830157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175037106919912809760837 1157819457547483651830157)
                    ·
                      rfl

theorem cell23_6764536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_6764536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764536 prefixEnd_6764536 := by exact prefixLift 6764536
  have htrace : WordTrace (prefixWord ++ tailWord_6764536) baseStart_6764536 baseEnd_6764536 := by
    simpa [prefixWord, tailWord_6764536, baseEnd_6764536] using wordTrace_append hprefix tailTrace_6764536
  have hstable : (prefixWord ++ tailWord_6764536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764536).length < 2 ^ (prefixWord ++ tailWord_6764536).sum := by decide
  have hdescent : baseEnd_6764536 < baseStart_6764536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764549 : List Nat := [1, 3, 1, 1, 2, 15]
def baseStart_6764549 : Nat := 118140960795 + 6764549 * 2 ^ 59
def prefixEnd_6764549 : Nat := 4983230072969 + 3 ^ 40 * 6764549 * 2
def baseEnd_6764549 : Nat := 14294094847287898784477

theorem tailTrace_6764549 : CollatzResearch.WordTrace tailWord_6764549 prefixEnd_6764549 14294094847287898784477 := by
  unfold tailWord_6764549
  simp only [CollatzResearch.WordTrace]
  refine ⟨246723371170201740836736701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164482247446801160557824467 246723371170201740836736701)
  ·
    refine ⟨92521264188825652813776263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246723371170201740836736701 92521264188825652813776263)
    ·
      refine ⟨138781896283238479220664395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92521264188825652813776263 138781896283238479220664395)
      ·
        refine ⟨208172844424857718830996593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138781896283238479220664395 208172844424857718830996593)
        ·
          refine ⟨156129633318643289123247445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208172844424857718830996593 156129633318643289123247445)
          ·
            refine ⟨14294094847287898784477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 156129633318643289123247445 14294094847287898784477)
            ·
              rfl

theorem cell23_6764549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 15].length) (baseStart_6764549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764549 prefixEnd_6764549 := by exact prefixLift 6764549
  have htrace : WordTrace (prefixWord ++ tailWord_6764549) baseStart_6764549 baseEnd_6764549 := by
    simpa [prefixWord, tailWord_6764549, baseEnd_6764549] using wordTrace_append hprefix tailTrace_6764549
  have hstable : (prefixWord ++ tailWord_6764549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764549).length < 2 ^ (prefixWord ++ tailWord_6764549).sum := by decide
  have hdescent : baseEnd_6764549 < baseStart_6764549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764556 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6764556 : Nat := 118140960795 + 6764556 * 2 ^ 59
def prefixEnd_6764556 : Nat := 4983230072969 + 3 ^ 40 * 6764556 * 2
def baseEnd_6764556 : Nat := 3473468642255540877240379

theorem tailTrace_6764556 : CollatzResearch.WordTrace tailWord_6764556 prefixEnd_6764556 3473468642255540877240379 := by
  unfold tailWord_6764556
  simp only [CollatzResearch.WordTrace]
  refine ⟨123361813240588190516120761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164482417654117587354827681 123361813240588190516120761)
  ·
    refine ⟨92521359930441142887090571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123361813240588190516120761 92521359930441142887090571)
    ·
      refine ⟨138782039895661714330635857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92521359930441142887090571 138782039895661714330635857)
      ·
        refine ⟨104086529921746285747976893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138782039895661714330635857 104086529921746285747976893)
        ·
          refine ⟨39032448720654857155491335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104086529921746285747976893 39032448720654857155491335)
          ·
            refine ⟨58548673080982285733237003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39032448720654857155491335 58548673080982285733237003)
            ·
              refine ⟨87823009621473428599855505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58548673080982285733237003 87823009621473428599855505)
              ·
                refine ⟨65867257216105071449891629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87823009621473428599855505 65867257216105071449891629)
                ·
                  refine ⟨24700221456039401793709361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65867257216105071449891629 24700221456039401793709361)
                  ·
                    refine ⟨18525166092029551345282021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24700221456039401793709361 18525166092029551345282021)
                    ·
                      refine ⟨3473468642255540877240379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18525166092029551345282021 3473468642255540877240379)
                      ·
                        rfl

theorem cell23_6764556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6764556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764556 prefixEnd_6764556 := by exact prefixLift 6764556
  have htrace : WordTrace (prefixWord ++ tailWord_6764556) baseStart_6764556 baseEnd_6764556 := by
    simpa [prefixWord, tailWord_6764556, baseEnd_6764556] using wordTrace_append hprefix tailTrace_6764556
  have hstable : (prefixWord ++ tailWord_6764556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764556).length < 2 ^ (prefixWord ++ tailWord_6764556).sum := by decide
  have hdescent : baseEnd_6764556 < baseStart_6764556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764573 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6764573 : Nat := 118140960795 + 6764573 * 2 ^ 59
def prefixEnd_6764573 : Nat := 4983230072969 + 3 ^ 40 * 6764573 * 2
def baseEnd_6764573 : Nat := 3473477371426667310727801

theorem tailTrace_6764573 : CollatzResearch.WordTrace tailWord_6764573 prefixEnd_6764573 3473477371426667310727801 := by
  unfold tailWord_6764573
  simp only [CollatzResearch.WordTrace]
  refine ⟨246724246522114792935610373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164482831014743195290406915 246724246522114792935610373)
  ·
    refine ⟨46260796222896523675426945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246724246522114792935610373 46260796222896523675426945)
    ·
      refine ⟨34695597167172392756570209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46260796222896523675426945 34695597167172392756570209)
      ·
        refine ⟨26021697875379294567427657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34695597167172392756570209 26021697875379294567427657)
        ·
          refine ⟨19516273406534470925570743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26021697875379294567427657 19516273406534470925570743)
          ·
            refine ⟨29274410109801706388356115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19516273406534470925570743 29274410109801706388356115)
            ·
              refine ⟨43911615164702559582534173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29274410109801706388356115 43911615164702559582534173)
              ·
                refine ⟨16466855686763459843450315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43911615164702559582534173 16466855686763459843450315)
                ·
                  refine ⟨24700283530145189765175473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16466855686763459843450315 24700283530145189765175473)
                  ·
                    refine ⟨18525212647608892323881605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24700283530145189765175473 18525212647608892323881605)
                    ·
                      refine ⟨3473477371426667310727801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18525212647608892323881605 3473477371426667310727801)
                      ·
                        rfl

theorem cell23_6764573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6764573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764573 prefixEnd_6764573 := by exact prefixLift 6764573
  have htrace : WordTrace (prefixWord ++ tailWord_6764573) baseStart_6764573 baseEnd_6764573 := by
    simpa [prefixWord, tailWord_6764573, baseEnd_6764573] using wordTrace_append hprefix tailTrace_6764573
  have hstable : (prefixWord ++ tailWord_6764573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764573).length < 2 ^ (prefixWord ++ tailWord_6764573).sum := by decide
  have hdescent : baseEnd_6764573 < baseStart_6764573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764577 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6764577 : Nat := 118140960795 + 6764577 * 2 ^ 59
def prefixEnd_6764577 : Nat := 4983230072969 + 3 ^ 40 * 6764577 * 2
def baseEnd_6764577 : Nat := 3473479425349285295077783

theorem tailTrace_6764577 : CollatzResearch.WordTrace tailWord_6764577 prefixEnd_6764577 3473479425349285295077783 := by
  unfold tailWord_6764577
  simp only [CollatzResearch.WordTrace]
  refine ⟨246724392414100301618755985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164482928276066867745837323 246724392414100301618755985)
  ·
    refine ⟨185043294310575226214066989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246724392414100301618755985 185043294310575226214066989)
    ·
      refine ⟨69391235366465709830275121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185043294310575226214066989 69391235366465709830275121)
      ·
        refine ⟨52043426524849282372706341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69391235366465709830275121 52043426524849282372706341)
        ·
          refine ⟨9758142473409240444882439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52043426524849282372706341 9758142473409240444882439)
          ·
            refine ⟨14637213710113860667323659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758142473409240444882439 14637213710113860667323659)
            ·
              refine ⟨21955820565170791000985489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637213710113860667323659 21955820565170791000985489)
              ·
                refine ⟨16466865423878093250739117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21955820565170791000985489 16466865423878093250739117)
                ·
                  refine ⟨6175074533954284969027169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16466865423878093250739117 6175074533954284969027169)
                  ·
                    refine ⟨4631305900465713726770377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175074533954284969027169 4631305900465713726770377)
                    ·
                      refine ⟨3473479425349285295077783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631305900465713726770377 3473479425349285295077783)
                      ·
                        rfl

theorem cell23_6764577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6764577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764577 prefixEnd_6764577 := by exact prefixLift 6764577
  have htrace : WordTrace (prefixWord ++ tailWord_6764577) baseStart_6764577 baseEnd_6764577 := by
    simpa [prefixWord, tailWord_6764577, baseEnd_6764577] using wordTrace_append hprefix tailTrace_6764577
  have hstable : (prefixWord ++ tailWord_6764577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764577).length < 2 ^ (prefixWord ++ tailWord_6764577).sum := by decide
  have hdescent : baseEnd_6764577 < baseStart_6764577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764593 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_6764593 : Nat := 118140960795 + 6764593 * 2 ^ 59
def prefixEnd_6764593 : Nat := 4983230072969 + 3 ^ 40 * 6764593 * 2
def baseEnd_6764593 : Nat := 3473487641039757232477709

theorem tailTrace_6764593 : CollatzResearch.WordTrace tailWord_6764593 prefixEnd_6764593 3473487641039757232477709 := by
  unfold tailWord_6764593
  simp only [CollatzResearch.WordTrace]
  refine ⟨246724975982042336351338433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164483317321361557567558955 246724975982042336351338433)
  ·
    refine ⟨185043731986531752263503825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246724975982042336351338433 185043731986531752263503825)
    ·
      refine ⟨138782798989898814197627869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185043731986531752263503825 138782798989898814197627869)
      ·
        refine ⟨52043549621212055324110451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138782798989898814197627869 52043549621212055324110451)
        ·
          refine ⟨78065324431818082986165677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52043549621212055324110451 78065324431818082986165677)
          ·
            refine ⟨29274496661931781119812129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78065324431818082986165677 29274496661931781119812129)
            ·
              refine ⟨21955872496448835839859097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29274496661931781119812129 21955872496448835839859097)
              ·
                refine ⟨16466904372336626879894323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21955872496448835839859097 16466904372336626879894323)
                ·
                  refine ⟨24700356558504940319841485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16466904372336626879894323 24700356558504940319841485)
                  ·
                    refine ⟨9262633709439352619940557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24700356558504940319841485 9262633709439352619940557)
                    ·
                      refine ⟨3473487641039757232477709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9262633709439352619940557 3473487641039757232477709)
                      ·
                        rfl

theorem cell23_6764593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_6764593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764593 prefixEnd_6764593 := by exact prefixLift 6764593
  have htrace : WordTrace (prefixWord ++ tailWord_6764593) baseStart_6764593 baseEnd_6764593 := by
    simpa [prefixWord, tailWord_6764593, baseEnd_6764593] using wordTrace_append hprefix tailTrace_6764593
  have hstable : (prefixWord ++ tailWord_6764593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764593).length < 2 ^ (prefixWord ++ tailWord_6764593).sum := by decide
  have hdescent : baseEnd_6764593 < baseStart_6764593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764594 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_6764594 : Nat := 118140960795 + 6764594 * 2 ^ 59
def prefixEnd_6764594 : Nat := 4983230072969 + 3 ^ 40 * 6764594 * 2
def baseEnd_6764594 : Nat := 3473488154520411728565205

theorem tailTrace_6764594 : CollatzResearch.WordTrace tailWord_6764594 prefixEnd_6764594 3473488154520411728565205 := by
  unfold tailWord_6764594
  simp only [CollatzResearch.WordTrace]
  refine ⟨61681253113759678380531209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164483341636692475681416557 61681253113759678380531209)
  ·
    refine ⟨46260939835319758785398407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61681253113759678380531209 46260939835319758785398407)
    ·
      refine ⟨69391409752979638178097611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46260939835319758785398407 69391409752979638178097611)
      ·
        refine ⟨104087114629469457267146417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69391409752979638178097611 104087114629469457267146417)
        ·
          refine ⟨78065335972102092950359813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104087114629469457267146417 78065335972102092950359813)
          ·
            refine ⟨14637250494769142428192465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78065335972102092950359813 14637250494769142428192465)
            ·
              refine ⟨10977937871076856821144349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14637250494769142428192465 10977937871076856821144349)
              ·
                refine ⟨4116726701653821307929131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977937871076856821144349 4116726701653821307929131)
                ·
                  refine ⟨6175090052480731961893697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116726701653821307929131 6175090052480731961893697)
                  ·
                    refine ⟨4631317539360548971420273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175090052480731961893697 4631317539360548971420273)
                    ·
                      refine ⟨3473488154520411728565205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631317539360548971420273 3473488154520411728565205)
                      ·
                        rfl

theorem cell23_6764594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_6764594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764594 prefixEnd_6764594 := by exact prefixLift 6764594
  have htrace : WordTrace (prefixWord ++ tailWord_6764594) baseStart_6764594 baseEnd_6764594 := by
    simpa [prefixWord, tailWord_6764594, baseEnd_6764594] using wordTrace_append hprefix tailTrace_6764594
  have hstable : (prefixWord ++ tailWord_6764594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764594).length < 2 ^ (prefixWord ++ tailWord_6764594).sum := by decide
  have hdescent : baseEnd_6764594 < baseStart_6764594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764616 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6764616 : Nat := 118140960795 + 6764616 * 2 ^ 59
def prefixEnd_6764616 : Nat := 4983230072969 + 3 ^ 40 * 6764616 * 2
def baseEnd_6764616 : Nat := 3473499451094810642490103

theorem tailTrace_6764616 : CollatzResearch.WordTrace tailWord_6764616 prefixEnd_6764616 3473499451094810642490103 := by
  unfold tailWord_6764616
  simp only [CollatzResearch.WordTrace]
  refine ⟨123362907430479505639712851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164483876573972674186283801 123362907430479505639712851)
  ·
    refine ⟨185044361145719258459569277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123362907430479505639712851 185044361145719258459569277)
    ·
      refine ⟨69391635429644721922338479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185044361145719258459569277 69391635429644721922338479)
      ·
        refine ⟨104087453144467082883507719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69391635429644721922338479 104087453144467082883507719)
        ·
          refine ⟨156131179716700624325261579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104087453144467082883507719 156131179716700624325261579)
          ·
            refine ⟨234196769575050936487892369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156131179716700624325261579 234196769575050936487892369)
            ·
              refine ⟨175647577181288202365919277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234196769575050936487892369 175647577181288202365919277)
              ·
                refine ⟨65867841442983075887219729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175647577181288202365919277 65867841442983075887219729)
                ·
                  refine ⟨49400881082237306915414797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65867841442983075887219729 49400881082237306915414797)
                  ·
                    refine ⟨18525330405838990093280549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49400881082237306915414797 18525330405838990093280549)
                    ·
                      refine ⟨3473499451094810642490103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18525330405838990093280549 3473499451094810642490103)
                      ·
                        rfl

theorem cell23_6764616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6764616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764616 prefixEnd_6764616 := by exact prefixLift 6764616
  have htrace : WordTrace (prefixWord ++ tailWord_6764616) baseStart_6764616 baseEnd_6764616 := by
    simpa [prefixWord, tailWord_6764616, baseEnd_6764616] using wordTrace_append hprefix tailTrace_6764616
  have hstable : (prefixWord ++ tailWord_6764616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764616).length < 2 ^ (prefixWord ++ tailWord_6764616).sum := by decide
  have hdescent : baseEnd_6764616 < baseStart_6764616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764653 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6764653 : Nat := 118140960795 + 6764653 * 2 ^ 59
def prefixEnd_6764653 : Nat := 4983230072969 + 3 ^ 40 * 6764653 * 2
def baseEnd_6764653 : Nat := 3473518449879026997727433

theorem tailTrace_6764653 : CollatzResearch.WordTrace tailWord_6764653 prefixEnd_6764653 3473518449879026997727433 := by
  unfold tailWord_6764653
  simp only [CollatzResearch.WordTrace]
  refine ⟨246727164361824966598522613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164484776241216644399015075 246727164361824966598522613)
  ·
    refine ⟨23130671658921090618611495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246727164361824966598522613 23130671658921090618611495)
    ·
      refine ⟨34696007488381635927917243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23130671658921090618611495 34696007488381635927917243)
      ·
        refine ⟨52044011232572453891875865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34696007488381635927917243 52044011232572453891875865)
        ·
          refine ⟨39033008424429340418906899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52044011232572453891875865 39033008424429340418906899)
          ·
            refine ⟨58549512636644010628360349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39033008424429340418906899 58549512636644010628360349)
            ·
              refine ⟨21956067238741503985635131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58549512636644010628360349 21956067238741503985635131)
              ·
                refine ⟨32934100858112255978452697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21956067238741503985635131 32934100858112255978452697)
                ·
                  refine ⟨24700575643584191983839523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32934100858112255978452697 24700575643584191983839523)
                  ·
                    refine ⟨37050863465376287975759285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24700575643584191983839523 37050863465376287975759285)
                    ·
                      refine ⟨3473518449879026997727433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37050863465376287975759285 3473518449879026997727433)
                      ·
                        rfl

theorem cell23_6764653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6764653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764653 prefixEnd_6764653 := by exact prefixLift 6764653
  have htrace : WordTrace (prefixWord ++ tailWord_6764653) baseStart_6764653 baseEnd_6764653 := by
    simpa [prefixWord, tailWord_6764653, baseEnd_6764653] using wordTrace_append hprefix tailTrace_6764653
  have hstable : (prefixWord ++ tailWord_6764653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764653).length < 2 ^ (prefixWord ++ tailWord_6764653).sum := by decide
  have hdescent : baseEnd_6764653 < baseStart_6764653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764716 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_6764716 : Nat := 118140960795 + 6764716 * 2 ^ 59
def prefixEnd_6764716 : Nat := 4983230072969 + 3 ^ 40 * 6764716 * 2
def baseEnd_6764716 : Nat := 1157850266386753417079881

theorem tailTrace_6764716 : CollatzResearch.WordTrace tailWord_6764716 prefixEnd_6764716 1157850266386753417079881 := by
  unfold tailWord_6764716
  simp only [CollatzResearch.WordTrace]
  refine ⟨123364731080298364179033001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164486308107064485572044001 123364731080298364179033001)
  ·
    refine ⟨92523548310223773134274751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123364731080298364179033001 92523548310223773134274751)
    ·
      refine ⟨138785322465335659701412127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92523548310223773134274751 138785322465335659701412127)
      ·
        refine ⟨208177983698003489552118191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138785322465335659701412127 208177983698003489552118191)
        ·
          refine ⟨312266975547005234328177287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208177983698003489552118191 312266975547005234328177287)
          ·
            refine ⟨468400463320507851492265931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312266975547005234328177287 468400463320507851492265931)
            ·
              refine ⟨702600694980761777238398897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468400463320507851492265931 702600694980761777238398897)
              ·
                refine ⟨526950521235571332928799173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702600694980761777238398897 526950521235571332928799173)
                ·
                  refine ⟨98803222731669624924149845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526950521235571332928799173 98803222731669624924149845)
                  ·
                    refine ⟨1157850266386753417079881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98803222731669624924149845 1157850266386753417079881)
                    ·
                      rfl

theorem cell23_6764716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_6764716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764716 prefixEnd_6764716 := by exact prefixLift 6764716
  have htrace : WordTrace (prefixWord ++ tailWord_6764716) baseStart_6764716 baseEnd_6764716 := by
    simpa [prefixWord, tailWord_6764716, baseEnd_6764716] using wordTrace_append hprefix tailTrace_6764716
  have hstable : (prefixWord ++ tailWord_6764716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764716).length < 2 ^ (prefixWord ++ tailWord_6764716).sum := by decide
  have hdescent : baseEnd_6764716 < baseStart_6764716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764718 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6764718 : Nat := 118140960795 + 6764718 * 2 ^ 59
def prefixEnd_6764718 : Nat := 4983230072969 + 3 ^ 40 * 6764718 * 2
def baseEnd_6764718 : Nat := 3473551826121569243414635

theorem tailTrace_6764718 : CollatzResearch.WordTrace tailWord_6764718 prefixEnd_6764718 3473551826121569243414635 := by
  unfold tailWord_6764718
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841191888323685337454851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164486356737726321799759205 30841191888323685337454851)
  ·
    refine ⟨46261787832485528006182277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841191888323685337454851 46261787832485528006182277)
    ·
      refine ⟨8674085218591036501159177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46261787832485528006182277 8674085218591036501159177)
      ·
        refine ⟨6505563913943277375869383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8674085218591036501159177 6505563913943277375869383)
        ·
          refine ⟨9758345870914916063804075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505563913943277375869383 9758345870914916063804075)
          ·
            refine ⟨14637518806372374095706113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758345870914916063804075 14637518806372374095706113)
            ·
              refine ⟨10978139104779280571779585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14637518806372374095706113 10978139104779280571779585)
              ·
                refine ⟨8233604328584460428834689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10978139104779280571779585 8233604328584460428834689)
                ·
                  refine ⟨6175203246438345321626017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233604328584460428834689 6175203246438345321626017)
                  ·
                    refine ⟨4631402434828758991219513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175203246438345321626017 4631402434828758991219513)
                    ·
                      refine ⟨3473551826121569243414635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631402434828758991219513 3473551826121569243414635)
                      ·
                        rfl

theorem cell23_6764718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6764718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764718 prefixEnd_6764718 := by exact prefixLift 6764718
  have htrace : WordTrace (prefixWord ++ tailWord_6764718) baseStart_6764718 baseEnd_6764718 := by
    simpa [prefixWord, tailWord_6764718, baseEnd_6764718] using wordTrace_append hprefix tailTrace_6764718
  have hstable : (prefixWord ++ tailWord_6764718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764718).length < 2 ^ (prefixWord ++ tailWord_6764718).sum := by decide
  have hdescent : baseEnd_6764718 < baseStart_6764718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764750 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_6764750 : Nat := 118140960795 + 6764750 * 2 ^ 59
def prefixEnd_6764750 : Nat := 4983230072969 + 3 ^ 40 * 6764750 * 2
def baseEnd_6764750 : Nat := 1157856085834171039404829

theorem tailTrace_6764750 : CollatzResearch.WordTrace tailWord_6764750 prefixEnd_6764750 1157856085834171039404829 := by
  unfold tailWord_6764750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841337780309194020600463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164487134828315701443202469 30841337780309194020600463)
  ·
    refine ⟨46262006670463791030900695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841337780309194020600463 46262006670463791030900695)
    ·
      refine ⟨69393010005695686546351043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46262006670463791030900695 69393010005695686546351043)
      ·
        refine ⟨104089515008543529819526565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69393010005695686546351043 104089515008543529819526565)
        ·
          refine ⟨19516784064101911841161231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104089515008543529819526565 19516784064101911841161231)
          ·
            refine ⟨29275176096152867761741847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19516784064101911841161231 29275176096152867761741847)
            ·
              refine ⟨43912764144229301642612771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29275176096152867761741847 43912764144229301642612771)
              ·
                refine ⟨65869146216343952463919157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43912764144229301642612771 65869146216343952463919157)
                ·
                  refine ⟨6175232457782245543492421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65869146216343952463919157 6175232457782245543492421)
                  ·
                    refine ⟨1157856085834171039404829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175232457782245543492421 1157856085834171039404829)
                    ·
                      rfl

theorem cell23_6764750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_6764750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764750 prefixEnd_6764750 := by exact prefixLift 6764750
  have htrace : WordTrace (prefixWord ++ tailWord_6764750) baseStart_6764750 baseEnd_6764750 := by
    simpa [prefixWord, tailWord_6764750, baseEnd_6764750] using wordTrace_append hprefix tailTrace_6764750
  have hstable : (prefixWord ++ tailWord_6764750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764750).length < 2 ^ (prefixWord ++ tailWord_6764750).sum := by decide
  have hdescent : baseEnd_6764750 < baseStart_6764750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764760 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_6764760 : Nat := 118140960795 + 6764760 * 2 ^ 59
def prefixEnd_6764760 : Nat := 4983230072969 + 3 ^ 40 * 6764760 * 2
def baseEnd_6764760 : Nat := 3473573392309058079089441

theorem tailTrace_6764760 : CollatzResearch.WordTrace tailWord_6764760 prefixEnd_6764760 3473573392309058079089441 := by
  unfold tailWord_6764760
  simp only [CollatzResearch.WordTrace]
  refine ⟨123365533486218661936333867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164487377981624882581778489 123365533486218661936333867)
  ·
    refine ⟨185048300229327992904500801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123365533486218661936333867 185048300229327992904500801)
    ·
      refine ⟨138786225171995994678375601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185048300229327992904500801 138786225171995994678375601)
      ·
        refine ⟨104089668878996996008781701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138786225171995994678375601 104089668878996996008781701)
        ·
          refine ⟨19516812914811936751646569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104089668878996996008781701 19516812914811936751646569)
          ·
            refine ⟨14637609686108952563734927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19516812914811936751646569 14637609686108952563734927)
            ·
              refine ⟨21956414529163428845602391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637609686108952563734927 21956414529163428845602391)
              ·
                refine ⟨32934621793745143268403587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21956414529163428845602391 32934621793745143268403587)
                ·
                  refine ⟨49401932690617714902605381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32934621793745143268403587 49401932690617714902605381)
                  ·
                    refine ⟨9262862379490821544238509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49401932690617714902605381 9262862379490821544238509)
                    ·
                      refine ⟨3473573392309058079089441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9262862379490821544238509 3473573392309058079089441)
                      ·
                        rfl

theorem cell23_6764760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_6764760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764760 prefixEnd_6764760 := by exact prefixLift 6764760
  have htrace : WordTrace (prefixWord ++ tailWord_6764760) baseStart_6764760 baseEnd_6764760 := by
    simpa [prefixWord, tailWord_6764760, baseEnd_6764760] using wordTrace_append hprefix tailTrace_6764760
  have hstable : (prefixWord ++ tailWord_6764760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764760).length < 2 ^ (prefixWord ++ tailWord_6764760).sum := by decide
  have hdescent : baseEnd_6764760 < baseStart_6764760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764783 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_6764783 : Nat := 118140960795 + 6764783 * 2 ^ 59
def prefixEnd_6764783 : Nat := 4983230072969 + 3 ^ 40 * 6764783 * 2
def baseEnd_6764783 : Nat := 3473585202364111489101835

theorem tailTrace_6764783 : CollatzResearch.WordTrace tailWord_6764783 prefixEnd_6764783 3473585202364111489101835 := by
  unfold tailWord_6764783
  simp only [CollatzResearch.WordTrace]
  refine ⟨246731905851353998800755003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164487937234235999200503335 246731905851353998800755003)
  ·
    refine ⟨370097858777030998201132505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246731905851353998800755003 370097858777030998201132505)
    ·
      refine ⟨277573394082773248650849379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370097858777030998201132505 277573394082773248650849379)
      ·
        refine ⟨416360091124159872976274069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277573394082773248650849379 416360091124159872976274069)
        ·
          refine ⟨19516879271444994045762847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 416360091124159872976274069 19516879271444994045762847)
          ·
            refine ⟨29275318907167491068644271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19516879271444994045762847 29275318907167491068644271)
            ·
              refine ⟨43912978360751236602966407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29275318907167491068644271 43912978360751236602966407)
              ·
                refine ⟨65869467541126854904449611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43912978360751236602966407 65869467541126854904449611)
                ·
                  refine ⟨98804201311690282356674417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65869467541126854904449611 98804201311690282356674417)
                  ·
                    refine ⟨74103150983767711767505813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98804201311690282356674417 74103150983767711767505813)
                    ·
                      refine ⟨3473585202364111489101835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74103150983767711767505813 3473585202364111489101835)
                      ·
                        rfl

theorem cell23_6764783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_6764783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764783 prefixEnd_6764783 := by exact prefixLift 6764783
  have htrace : WordTrace (prefixWord ++ tailWord_6764783) baseStart_6764783 baseEnd_6764783 := by
    simpa [prefixWord, tailWord_6764783, baseEnd_6764783] using wordTrace_append hprefix tailTrace_6764783
  have hstable : (prefixWord ++ tailWord_6764783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764783).length < 2 ^ (prefixWord ++ tailWord_6764783).sum := by decide
  have hdescent : baseEnd_6764783 < baseStart_6764783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764793 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_6764793 : Nat := 118140960795 + 6764793 * 2 ^ 59
def prefixEnd_6764793 : Nat := 4983230072969 + 3 ^ 40 * 6764793 * 2
def baseEnd_6764793 : Nat := 1157863445723552149992263

theorem tailTrace_6764793 : CollatzResearch.WordTrace tailWord_6764793 prefixEnd_6764793 1157863445723552149992263 := by
  unfold tailWord_6764793
  simp only [CollatzResearch.WordTrace]
  refine ⟨246732270581317770508619033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164488180387545180339079355 246732270581317770508619033)
  ·
    refine ⟨185049202935988327881464275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246732270581317770508619033 185049202935988327881464275)
    ·
      refine ⟨277573804403982491822196413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185049202935988327881464275 277573804403982491822196413)
      ·
        refine ⟨104090176651493434433323655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277573804403982491822196413 104090176651493434433323655)
        ·
          refine ⟨156135264977240151649985483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104090176651493434433323655 156135264977240151649985483)
          ·
            refine ⟨234202897465860227474978225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156135264977240151649985483 234202897465860227474978225)
            ·
              refine ⟨175652173099395170606233669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234202897465860227474978225 175652173099395170606233669)
              ·
                refine ⟨32934782456136594488668813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175652173099395170606233669 32934782456136594488668813)
                ·
                  refine ⟨12350543421051222933250805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32934782456136594488668813 12350543421051222933250805)
                  ·
                    refine ⟨1157863445723552149992263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12350543421051222933250805 1157863445723552149992263)
                    ·
                      rfl

theorem cell23_6764793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_6764793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764793 prefixEnd_6764793 := by exact prefixLift 6764793
  have htrace : WordTrace (prefixWord ++ tailWord_6764793) baseStart_6764793 baseEnd_6764793 := by
    simpa [prefixWord, tailWord_6764793, baseEnd_6764793] using wordTrace_append hprefix tailTrace_6764793
  have hstable : (prefixWord ++ tailWord_6764793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764793).length < 2 ^ (prefixWord ++ tailWord_6764793).sum := by decide
  have hdescent : baseEnd_6764793 < baseStart_6764793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764800 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2]
def baseStart_6764800 : Nat := 118140960795 + 6764800 * 2 ^ 59
def prefixEnd_6764800 : Nat := 4983230072969 + 3 ^ 40 * 6764800 * 2
def baseEnd_6764800 : Nat := 3473593931535237922589257

theorem tailTrace_6764800 : CollatzResearch.WordTrace tailWord_6764800 prefixEnd_6764800 3473593931535237922589257 := by
  unfold tailWord_6764800
  simp only [CollatzResearch.WordTrace]
  refine ⟨123366262946146205352061927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164488350594861607136082569 123366262946146205352061927)
  ·
    refine ⟨185049394419219308028092891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123366262946146205352061927 185049394419219308028092891)
    ·
      refine ⟨277574091628828962042139337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185049394419219308028092891 277574091628828962042139337)
      ·
        refine ⟨208180568721621721531604503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277574091628828962042139337 208180568721621721531604503)
        ·
          refine ⟨312270853082432582297406755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208180568721621721531604503 312270853082432582297406755)
          ·
            refine ⟨468406279623648873446110133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312270853082432582297406755 468406279623648873446110133)
            ·
              refine ⟨43913088714717081885572825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 468406279623648873446110133 43913088714717081885572825)
              ·
                refine ⟨32934816536037811414179619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43913088714717081885572825 32934816536037811414179619)
                ·
                  refine ⟨49402224804056717121269429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32934816536037811414179619 49402224804056717121269429)
                  ·
                    refine ⟨4631458575380317230119009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49402224804056717121269429 4631458575380317230119009)
                    ·
                      refine ⟨3473593931535237922589257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631458575380317230119009 3473593931535237922589257)
                      ·
                        rfl

theorem cell23_6764800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_6764800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764800 prefixEnd_6764800 := by exact prefixLift 6764800
  have htrace : WordTrace (prefixWord ++ tailWord_6764800) baseStart_6764800 baseEnd_6764800 := by
    simpa [prefixWord, tailWord_6764800, baseEnd_6764800] using wordTrace_append hprefix tailTrace_6764800
  have hstable : (prefixWord ++ tailWord_6764800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764800).length < 2 ^ (prefixWord ++ tailWord_6764800).sum := by decide
  have hdescent : baseEnd_6764800 < baseStart_6764800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764810 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_6764810 : Nat := 118140960795 + 6764810 * 2 ^ 59
def prefixEnd_6764810 : Nat := 4983230072969 + 3 ^ 40 * 6764810 * 2
def baseEnd_6764810 : Nat := 1157866355447260961154737

theorem tailTrace_6764810 : CollatzResearch.WordTrace tailWord_6764810 prefixEnd_6764810 1157866355447260961154737 := by
  unfold tailWord_6764810
  simp only [CollatzResearch.WordTrace]
  refine ⟨61683222655564045602996971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164488593748170788274658589 61683222655564045602996971)
  ·
    refine ⟨92524833983346068404495457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61683222655564045602996971 92524833983346068404495457)
    ·
      refine ⟨69393625487509551303371593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92524833983346068404495457 69393625487509551303371593)
      ·
        refine ⟨52045219115632163477528695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69393625487509551303371593 52045219115632163477528695)
        ·
          refine ⟨78067828673448245216293043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52045219115632163477528695 78067828673448245216293043)
          ·
            refine ⟨117101743010172367824439565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78067828673448245216293043 117101743010172367824439565)
            ·
              refine ⟨43913153628814637934164837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117101743010172367824439565 43913153628814637934164837)
              ·
                refine ⟨8233716305402744612655907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43913153628814637934164837 8233716305402744612655907)
                ·
                  refine ⟨12350574458104116918983861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233716305402744612655907 12350574458104116918983861)
                  ·
                    refine ⟨1157866355447260961154737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12350574458104116918983861 1157866355447260961154737)
                    ·
                      rfl

theorem cell23_6764810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_6764810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764810 prefixEnd_6764810 := by exact prefixLift 6764810
  have htrace : WordTrace (prefixWord ++ tailWord_6764810) baseStart_6764810 baseEnd_6764810 := by
    simpa [prefixWord, tailWord_6764810, baseEnd_6764810] using wordTrace_append hprefix tailTrace_6764810
  have hstable : (prefixWord ++ tailWord_6764810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764810).length < 2 ^ (prefixWord ++ tailWord_6764810).sum := by decide
  have hdescent : baseEnd_6764810 < baseStart_6764810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764834 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_6764834 : Nat := 118140960795 + 6764834 * 2 ^ 59
def prefixEnd_6764834 : Nat := 4983230072969 + 3 ^ 40 * 6764834 * 2
def baseEnd_6764834 : Nat := 3473611389877490789564101

theorem tailTrace_6764834 : CollatzResearch.WordTrace tailWord_6764834 prefixEnd_6764834 3473611389877490789564101 := by
  unfold tailWord_6764834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61683441493542308627715389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164489177316112823007241037 61683441493542308627715389)
  ·
    refine ⟨23131290560078365735393271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61683441493542308627715389 23131290560078365735393271)
    ·
      refine ⟨34696935840117548603089907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23131290560078365735393271 34696935840117548603089907)
      ·
        refine ⟨52045403760176322904634861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34696935840117548603089907 52045403760176322904634861)
        ·
          refine ⟨19517026410066121089238073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52045403760176322904634861 19517026410066121089238073)
          ·
            refine ⟨14637769807549590816928555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19517026410066121089238073 14637769807549590816928555)
            ·
              refine ⟨21956654711324386225392833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637769807549590816928555 21956654711324386225392833)
              ·
                refine ⟨16467491033493289669044625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21956654711324386225392833 16467491033493289669044625)
                ·
                  refine ⟨12350618275119967251783469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16467491033493289669044625 12350618275119967251783469)
                  ·
                    refine ⟨4631481853169987719418801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12350618275119967251783469 4631481853169987719418801)
                    ·
                      refine ⟨3473611389877490789564101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631481853169987719418801 3473611389877490789564101)
                      ·
                        rfl

theorem cell23_6764834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_6764834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764834 prefixEnd_6764834 := by exact prefixLift 6764834
  have htrace : WordTrace (prefixWord ++ tailWord_6764834) baseStart_6764834 baseEnd_6764834 := by
    simpa [prefixWord, tailWord_6764834, baseEnd_6764834] using wordTrace_append hprefix tailTrace_6764834
  have hstable : (prefixWord ++ tailWord_6764834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764834).length < 2 ^ (prefixWord ++ tailWord_6764834).sum := by decide
  have hdescent : baseEnd_6764834 < baseStart_6764834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764860 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_6764860 : Nat := 118140960795 + 6764860 * 2 ^ 59
def prefixEnd_6764860 : Nat := 4983230072969 + 3 ^ 40 * 6764860 * 2
def baseEnd_6764860 : Nat := 3473624740374507687838981

theorem tailTrace_6764860 : CollatzResearch.WordTrace tailWord_6764860 prefixEnd_6764860 3473624740374507687838981 := by
  unfold tailWord_6764860
  simp only [CollatzResearch.WordTrace]
  refine ⟨123367357136037520475654017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164489809514716693967538689 123367357136037520475654017)
  ·
    refine ⟨92525517852028140356740513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123367357136037520475654017 92525517852028140356740513)
    ·
      refine ⟨69394138389021105267555385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92525517852028140356740513 69394138389021105267555385)
      ·
        refine ⟨52045603791765828950666539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69394138389021105267555385 52045603791765828950666539)
        ·
          refine ⟨78068405687648743425999809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52045603791765828950666539 78068405687648743425999809)
          ·
            refine ⟨58551304265736557569499857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78068405687648743425999809 58551304265736557569499857)
            ·
              refine ⟨43913478199302418177124893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58551304265736557569499857 43913478199302418177124893)
              ·
                refine ⟨16467554324738406816421835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43913478199302418177124893 16467554324738406816421835)
                ·
                  refine ⟨24701331487107610224632753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16467554324738406816421835 24701331487107610224632753)
                  ·
                    refine ⟨18525998615330707668474565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24701331487107610224632753 18525998615330707668474565)
                    ·
                      refine ⟨3473624740374507687838981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18525998615330707668474565 3473624740374507687838981)
                      ·
                        rfl

theorem cell23_6764860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_6764860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764860 prefixEnd_6764860 := by exact prefixLift 6764860
  have htrace : WordTrace (prefixWord ++ tailWord_6764860) baseStart_6764860 baseEnd_6764860 := by
    simpa [prefixWord, tailWord_6764860, baseEnd_6764860] using wordTrace_append hprefix tailTrace_6764860
  have hstable : (prefixWord ++ tailWord_6764860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764860).length < 2 ^ (prefixWord ++ tailWord_6764860).sum := by decide
  have hdescent : baseEnd_6764860 < baseStart_6764860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764867 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 3]
def baseStart_6764867 : Nat := 118140960795 + 6764867 * 2 ^ 59
def prefixEnd_6764867 : Nat := 4983230072969 + 3 ^ 40 * 6764867 * 2
def baseEnd_6764867 : Nat := 3473628334739089160451449

theorem tailTrace_6764867 : CollatzResearch.WordTrace tailWord_6764867 prefixEnd_6764867 3473628334739089160451449 := by
  unfold tailWord_6764867
  simp only [CollatzResearch.WordTrace]
  refine ⟨246734969583049681146812855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164489979722033120764541903 246734969583049681146812855)
  ·
    refine ⟨370102454374574521720219283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246734969583049681146812855 370102454374574521720219283)
    ·
      refine ⟨555153681561861782580328925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370102454374574521720219283 555153681561861782580328925)
      ·
        refine ⟨208182630585698168467623347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555153681561861782580328925 208182630585698168467623347)
        ·
          refine ⟨312273945878547252701435021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208182630585698168467623347 312273945878547252701435021)
          ·
            refine ⟨117102729704455219763038133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312273945878547252701435021 117102729704455219763038133)
            ·
              refine ⟨10978380909792676852784825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117102729704455219763038133 10978380909792676852784825)
              ·
                refine ⟨8233785682344507639588619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10978380909792676852784825 8233785682344507639588619)
                ·
                  refine ⟨12350678523516761459382929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8233785682344507639588619 12350678523516761459382929)
                  ·
                    refine ⟨9263008892637571094537197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12350678523516761459382929 9263008892637571094537197)
                    ·
                      refine ⟨3473628334739089160451449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263008892637571094537197 3473628334739089160451449)
                      ·
                        rfl

theorem cell23_6764867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_6764867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764867 prefixEnd_6764867 := by exact prefixLift 6764867
  have htrace : WordTrace (prefixWord ++ tailWord_6764867) baseStart_6764867 baseEnd_6764867 := by
    simpa [prefixWord, tailWord_6764867, baseEnd_6764867] using wordTrace_append hprefix tailTrace_6764867
  have hstable : (prefixWord ++ tailWord_6764867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764867).length < 2 ^ (prefixWord ++ tailWord_6764867).sum := by decide
  have hdescent : baseEnd_6764867 < baseStart_6764867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764880 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_6764880 : Nat := 118140960795 + 6764880 * 2 ^ 59
def prefixEnd_6764880 : Nat := 4983230072969 + 3 ^ 40 * 6764880 * 2
def baseEnd_6764880 : Nat := 3473635009987597609588889

theorem tailTrace_6764880 : CollatzResearch.WordTrace tailWord_6764880 prefixEnd_6764880 3473635009987597609588889 := by
  unfold tailWord_6764880
  simp only [CollatzResearch.WordTrace]
  refine ⟨123367721866001292183518047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164490295821335056244690729 123367721866001292183518047)
  ·
    refine ⟨185051582799001938275277071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123367721866001292183518047 185051582799001938275277071)
    ·
      refine ⟨277577374198502907412915607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185051582799001938275277071 277577374198502907412915607)
      ·
        refine ⟨416366061297754361119373411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277577374198502907412915607 416366061297754361119373411)
        ·
          refine ⟨624549091946631541679060117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416366061297754361119373411 624549091946631541679060117)
          ·
            refine ⟨29275738684998353516205943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 624549091946631541679060117 29275738684998353516205943)
            ·
              refine ⟨43913608027497530274308915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29275738684998353516205943 43913608027497530274308915)
              ·
                refine ⟨65870412041246295411463373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43913608027497530274308915 65870412041246295411463373)
                ·
                  refine ⟨24701404515467360779298765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65870412041246295411463373 24701404515467360779298765)
                  ·
                    refine ⟨9263026693300260292237037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24701404515467360779298765 9263026693300260292237037)
                    ·
                      refine ⟨3473635009987597609588889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263026693300260292237037 3473635009987597609588889)
                      ·
                        rfl

theorem cell23_6764880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_6764880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764880 prefixEnd_6764880 := by exact prefixLift 6764880
  have htrace : WordTrace (prefixWord ++ tailWord_6764880) baseStart_6764880 baseEnd_6764880 := by
    simpa [prefixWord, tailWord_6764880, baseEnd_6764880] using wordTrace_append hprefix tailTrace_6764880
  have hstable : (prefixWord ++ tailWord_6764880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764880).length < 2 ^ (prefixWord ++ tailWord_6764880).sum := by decide
  have hdescent : baseEnd_6764880 < baseStart_6764880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764892 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6764892 : Nat := 118140960795 + 6764892 * 2 ^ 59
def prefixEnd_6764892 : Nat := 4983230072969 + 3 ^ 40 * 6764892 * 2
def baseEnd_6764892 : Nat := 3473641171755451562638835

theorem tailTrace_6764892 : CollatzResearch.WordTrace tailWord_6764892 prefixEnd_6764892 3473641171755451562638835 := by
  unfold tailWord_6764892
  simp only [CollatzResearch.WordTrace]
  refine ⟨123367940703979555208236465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164490587605306073610981953 123367940703979555208236465)
  ·
    refine ⟨92525955527984666406177349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123367940703979555208236465 92525955527984666406177349)
    ·
      refine ⟨17348616661497124951158253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92525955527984666406177349 17348616661497124951158253)
      ·
        refine ⟨6505731248061421856684345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17348616661497124951158253 6505731248061421856684345)
        ·
          refine ⟨4879298436046066392513259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505731248061421856684345 4879298436046066392513259)
          ·
            refine ⟨7318947654069099588769889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879298436046066392513259 7318947654069099588769889)
            ·
              refine ⟨5489210740551824691577417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318947654069099588769889 5489210740551824691577417)
              ·
                refine ⟨4116908055413868518683063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5489210740551824691577417 4116908055413868518683063)
                ·
                  refine ⟨6175362083120802778024595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116908055413868518683063 6175362083120802778024595)
                  ·
                    refine ⟨9263043124681204167036893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6175362083120802778024595 9263043124681204167036893)
                    ·
                      refine ⟨3473641171755451562638835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263043124681204167036893 3473641171755451562638835)
                      ·
                        rfl

theorem cell23_6764892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6764892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764892 prefixEnd_6764892 := by exact prefixLift 6764892
  have htrace : WordTrace (prefixWord ++ tailWord_6764892) baseStart_6764892 baseEnd_6764892 := by
    simpa [prefixWord, tailWord_6764892, baseEnd_6764892] using wordTrace_append hprefix tailTrace_6764892
  have hstable : (prefixWord ++ tailWord_6764892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764892).length < 2 ^ (prefixWord ++ tailWord_6764892).sum := by decide
  have hdescent : baseEnd_6764892 < baseStart_6764892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764898 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6764898 : Nat := 118140960795 + 6764898 * 2 ^ 59
def prefixEnd_6764898 : Nat := 4983230072969 + 3 ^ 40 * 6764898 * 2
def baseEnd_6764898 : Nat := 3473644252639378539163807

theorem tailTrace_6764898 : CollatzResearch.WordTrace tailWord_6764898 prefixEnd_6764898 3473644252639378539163807 := by
  unfold tailWord_6764898
  simp only [CollatzResearch.WordTrace]
  refine ⟨61684025061484343360297837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164490733497291582294127565 61684025061484343360297837)
  ·
    refine ⟨23131509398056628760111689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61684025061484343360297837 23131509398056628760111689)
    ·
      refine ⟨17348632048542471570083767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23131509398056628760111689 17348632048542471570083767)
      ·
        refine ⟨26022948072813707355125651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348632048542471570083767 26022948072813707355125651)
        ·
          refine ⟨39034422109220561032688477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26022948072813707355125651 39034422109220561032688477)
          ·
            refine ⟨14637908290957710387258179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39034422109220561032688477 14637908290957710387258179)
            ·
              refine ⟨21956862436436565580887269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637908290957710387258179 21956862436436565580887269)
              ·
                refine ⟨4116911706831856046416363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21956862436436565580887269 4116911706831856046416363)
                ·
                  refine ⟨6175367560247784069624545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116911706831856046416363 6175367560247784069624545)
                  ·
                    refine ⟨4631525670185838052218409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175367560247784069624545 4631525670185838052218409)
                    ·
                      refine ⟨3473644252639378539163807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631525670185838052218409 3473644252639378539163807)
                      ·
                        rfl

theorem cell23_6764898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6764898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764898 prefixEnd_6764898 := by exact prefixLift 6764898
  have htrace : WordTrace (prefixWord ++ tailWord_6764898) baseStart_6764898 baseEnd_6764898 := by
    simpa [prefixWord, tailWord_6764898, baseEnd_6764898] using wordTrace_append hprefix tailTrace_6764898
  have hstable : (prefixWord ++ tailWord_6764898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764898).length < 2 ^ (prefixWord ++ tailWord_6764898).sum := by decide
  have hdescent : baseEnd_6764898 < baseStart_6764898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764914 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_6764914 : Nat := 118140960795 + 6764914 * 2 ^ 59
def prefixEnd_6764914 : Nat := 4983230072969 + 3 ^ 40 * 6764914 * 2
def baseEnd_6764914 : Nat := 3473652468329850476563733

theorem tailTrace_6764914 : CollatzResearch.WordTrace tailWord_6764914 prefixEnd_6764914 3473652468329850476563733 := by
  unfold tailWord_6764914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61684170953469852043443449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164491122542586272115849197 61684170953469852043443449)
  ·
    refine ⟨46263128215102389032582587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61684170953469852043443449 46263128215102389032582587)
    ·
      refine ⟨69394692322653583548873881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46263128215102389032582587 69394692322653583548873881)
      ·
        refine ⟨52046019241990187661655411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69394692322653583548873881 52046019241990187661655411)
        ·
          refine ⟨78069028862985281492483117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52046019241990187661655411 78069028862985281492483117)
          ·
            refine ⟨29275885823619480559681169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78069028862985281492483117 29275885823619480559681169)
            ·
              refine ⟨21956914367714610419760877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29275885823619480559681169 21956914367714610419760877)
              ·
                refine ⟨8233842887892978907410329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21956914367714610419760877 8233842887892978907410329)
                ·
                  refine ⟨6175382165919734180557747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233842887892978907410329 6175382165919734180557747)
                  ·
                    refine ⟨9263073248879601270836621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6175382165919734180557747 9263073248879601270836621)
                    ·
                      refine ⟨3473652468329850476563733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263073248879601270836621 3473652468329850476563733)
                      ·
                        rfl

theorem cell23_6764914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_6764914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764914 prefixEnd_6764914 := by exact prefixLift 6764914
  have htrace : WordTrace (prefixWord ++ tailWord_6764914) baseStart_6764914 baseEnd_6764914 := by
    simpa [prefixWord, tailWord_6764914, baseEnd_6764914] using wordTrace_append hprefix tailTrace_6764914
  have hstable : (prefixWord ++ tailWord_6764914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764914).length < 2 ^ (prefixWord ++ tailWord_6764914).sum := by decide
  have hdescent : baseEnd_6764914 < baseStart_6764914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764948 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6764948 : Nat := 118140960795 + 6764948 * 2 ^ 59
def prefixEnd_6764948 : Nat := 4983230072969 + 3 ^ 40 * 6764948 * 2
def baseEnd_6764948 : Nat := 3473669926672103343538577

theorem tailTrace_6764948 : CollatzResearch.WordTrace tailWord_6764948 prefixEnd_6764948 3473669926672103343538577 := by
  unfold tailWord_6764948
  simp only [CollatzResearch.WordTrace]
  refine ⟨123368961947878115990255749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164491949263837487987007665 123368961947878115990255749)
  ·
    refine ⟨23131680365227146748172953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123368961947878115990255749 23131680365227146748172953)
    ·
      refine ⟨17348760273920360061129715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23131680365227146748172953 17348760273920360061129715)
      ·
        refine ⟨26023140410880540091694573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348760273920360061129715 26023140410880540091694573)
        ·
          refine ⟨9758677654080202534385465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26023140410880540091694573 9758677654080202534385465)
          ·
            refine ⟨7319008240560151900789099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758677654080202534385465 7319008240560151900789099)
            ·
              refine ⟨10978512360840227851183649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319008240560151900789099 10978512360840227851183649)
              ·
                refine ⟨8233884270630170888387737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10978512360840227851183649 8233884270630170888387737)
                ·
                  refine ⟨6175413202972628166290803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233884270630170888387737 6175413202972628166290803)
                  ·
                    refine ⟨9263119804458942249436205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6175413202972628166290803 9263119804458942249436205)
                    ·
                      refine ⟨3473669926672103343538577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263119804458942249436205 3473669926672103343538577)
                      ·
                        rfl

theorem cell23_6764948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6764948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764948 prefixEnd_6764948 := by exact prefixLift 6764948
  have htrace : WordTrace (prefixWord ++ tailWord_6764948) baseStart_6764948 baseEnd_6764948 := by
    simpa [prefixWord, tailWord_6764948, baseEnd_6764948] using wordTrace_append hprefix tailTrace_6764948
  have hstable : (prefixWord ++ tailWord_6764948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764948).length < 2 ^ (prefixWord ++ tailWord_6764948).sum := by decide
  have hdescent : baseEnd_6764948 < baseStart_6764948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764960 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 7]
def baseStart_6764960 : Nat := 118140960795 + 6764960 * 2 ^ 59
def prefixEnd_6764960 : Nat := 4983230072969 + 3 ^ 40 * 6764960 * 2
def baseEnd_6764960 : Nat := 385964009826661921843169

theorem tailTrace_6764960 : CollatzResearch.WordTrace tailWord_6764960 prefixEnd_6764960 385964009826661921843169 := by
  unfold tailWord_6764960
  simp only [CollatzResearch.WordTrace]
  refine ⟨123369180785856379014974167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164492241047808505353298889 123369180785856379014974167)
  ·
    refine ⟨185053771178784568522461251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123369180785856379014974167 185053771178784568522461251)
    ·
      refine ⟨277580656768176852783691877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185053771178784568522461251 277580656768176852783691877)
      ·
        refine ⟨52046373144033159896942227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277580656768176852783691877 52046373144033159896942227)
        ·
          refine ⟨78069559716049739845413341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52046373144033159896942227 78069559716049739845413341)
          ·
            refine ⟨29276084893518652442030003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78069559716049739845413341 29276084893518652442030003)
            ·
              refine ⟨43914127340277978663045005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29276084893518652442030003 43914127340277978663045005)
              ·
                refine ⟨16467797752604241998641877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43914127340277978663045005 16467797752604241998641877)
                ·
                  refine ⟨385964009826661921843169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16467797752604241998641877 385964009826661921843169)
                  ·
                    rfl

theorem cell23_6764960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_6764960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764960 prefixEnd_6764960 := by exact prefixLift 6764960
  have htrace : WordTrace (prefixWord ++ tailWord_6764960) baseStart_6764960 baseEnd_6764960 := by
    simpa [prefixWord, tailWord_6764960, baseEnd_6764960] using wordTrace_append hprefix tailTrace_6764960
  have hstable : (prefixWord ++ tailWord_6764960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764960).length < 2 ^ (prefixWord ++ tailWord_6764960).sum := by decide
  have hdescent : baseEnd_6764960 < baseStart_6764960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764967 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6764967 : Nat := 118140960795 + 6764967 * 2 ^ 59
def prefixEnd_6764967 : Nat := 4983230072969 + 3 ^ 40 * 6764967 * 2
def baseEnd_6764967 : Nat := 3473679682804538769200989

theorem tailTrace_6764967 : CollatzResearch.WordTrace tailWord_6764967 prefixEnd_6764967 3473679682804538769200989 := by
  unfold tailWord_6764967
  simp only [CollatzResearch.WordTrace]
  refine ⟨246738616882687398225453155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164492411255124932150302103 246738616882687398225453155)
  ·
    refine ⟨370107925324031097338179733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246738616882687398225453155 370107925324031097338179733)
    ·
      refine ⟨17348808999563957687727175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370107925324031097338179733 17348808999563957687727175)
      ·
        refine ⟨26023213499345936531590763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348808999563957687727175 26023213499345936531590763)
        ·
          refine ⟨39034820249018904797386145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26023213499345936531590763 39034820249018904797386145)
          ·
            refine ⟨29276115186764178598039609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39034820249018904797386145 29276115186764178598039609)
            ·
              refine ⟨21957086390073133948529707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29276115186764178598039609 21957086390073133948529707)
              ·
                refine ⟨32935629585109700922794561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21957086390073133948529707 32935629585109700922794561)
                ·
                  refine ⟨24701722188832275692095921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32935629585109700922794561 24701722188832275692095921)
                  ·
                    refine ⟨18526291641624206769071941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24701722188832275692095921 18526291641624206769071941)
                    ·
                      refine ⟨3473679682804538769200989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18526291641624206769071941 3473679682804538769200989)
                      ·
                        rfl

theorem cell23_6764967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6764967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764967 prefixEnd_6764967 := by exact prefixLift 6764967
  have htrace : WordTrace (prefixWord ++ tailWord_6764967) baseStart_6764967 baseEnd_6764967 := by
    simpa [prefixWord, tailWord_6764967, baseEnd_6764967] using wordTrace_append hprefix tailTrace_6764967
  have hstable : (prefixWord ++ tailWord_6764967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764967).length < 2 ^ (prefixWord ++ tailWord_6764967).sum := by decide
  have hdescent : baseEnd_6764967 < baseStart_6764967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765050 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_6765050 : Nat := 118140960795 + 6765050 * 2 ^ 59
def prefixEnd_6765050 : Nat := 4983230072969 + 3 ^ 40 * 6765050 * 2
def baseEnd_6765050 : Nat := 385969144633206882718123

theorem tailTrace_6765050 : CollatzResearch.WordTrace tailWord_6765050 prefixEnd_6765050 385969144633206882718123 := by
  unfold tailWord_6765050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61685411035346675850181151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164494429427591135600483069 61685411035346675850181151)
  ·
    refine ⟨92528116553020013775271727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61685411035346675850181151 92528116553020013775271727)
    ·
      refine ⟨138792174829530020662907591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92528116553020013775271727 138792174829530020662907591)
      ·
        refine ⟨208188262244295030994361387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138792174829530020662907591 208188262244295030994361387)
        ·
          refine ⟨312282393366442546491542081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208188262244295030994361387 312282393366442546491542081)
          ·
            refine ⟨234211795024831909868656561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312282393366442546491542081 234211795024831909868656561)
            ·
              refine ⟨175658846268623932401492421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234211795024831909868656561 175658846268623932401492421)
              ·
                refine ⟨32936033675366987325279829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175658846268623932401492421 32936033675366987325279829)
                ·
                  refine ⟨385969144633206882718123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32936033675366987325279829 385969144633206882718123)
                  ·
                    rfl

theorem cell23_6765050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_6765050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765050 prefixEnd_6765050 := by exact prefixLift 6765050
  have htrace : WordTrace (prefixWord ++ tailWord_6765050) baseStart_6765050 baseEnd_6765050 := by
    simpa [prefixWord, tailWord_6765050, baseEnd_6765050] using wordTrace_append hprefix tailTrace_6765050
  have hstable : (prefixWord ++ tailWord_6765050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765050).length < 2 ^ (prefixWord ++ tailWord_6765050).sum := by decide
  have hdescent : baseEnd_6765050 < baseStart_6765050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765062 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6765062 : Nat := 118140960795 + 6765062 * 2 ^ 59
def prefixEnd_6765062 : Nat := 4983230072969 + 3 ^ 40 * 6765062 * 2
def baseEnd_6765062 : Nat := 385969829274079544168117

theorem tailTrace_6765062 : CollatzResearch.WordTrace tailWord_6765062 prefixEnd_6765062 385969829274079544168117 := by
  unfold tailWord_6765062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710690056791975920317545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164494721211562152966774293 7710690056791975920317545)
  ·
    refine ⟨5783017542593981940238159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7710690056791975920317545 5783017542593981940238159)
    ·
      refine ⟨8674526313890972910357239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783017542593981940238159 8674526313890972910357239)
      ·
        refine ⟨13011789470836459365535859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8674526313890972910357239 13011789470836459365535859)
        ·
          refine ⟨19517684206254689048303789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13011789470836459365535859 19517684206254689048303789)
          ·
            refine ⟨7319131577345508393113921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19517684206254689048303789 7319131577345508393113921)
            ·
              refine ⟨5489348683009131294835441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7319131577345508393113921 5489348683009131294835441)
              ·
                refine ⟨4117011512256848471126581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5489348683009131294835441 4117011512256848471126581)
                ·
                  refine ⟨385969829274079544168117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4117011512256848471126581 385969829274079544168117)
                  ·
                    rfl

theorem cell23_6765062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6765062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765062 prefixEnd_6765062 := by exact prefixLift 6765062
  have htrace : WordTrace (prefixWord ++ tailWord_6765062) baseStart_6765062 baseEnd_6765062 := by
    simpa [prefixWord, tailWord_6765062, baseEnd_6765062] using wordTrace_append hprefix tailTrace_6765062
  have hstable : (prefixWord ++ tailWord_6765062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765062).length < 2 ^ (prefixWord ++ tailWord_6765062).sum := by decide
  have hdescent : baseEnd_6765062 < baseStart_6765062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765067 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 6]
def baseStart_6765067 : Nat := 118140960795 + 6765067 * 2 ^ 59
def prefixEnd_6765067 : Nat := 4983230072969 + 3 ^ 40 * 6765067 * 2
def baseEnd_6765067 : Nat := 385970114541109819772281

theorem tailTrace_6765067 : CollatzResearch.WordTrace tailWord_6765067 prefixEnd_6765067 385970114541109819772281 := by
  unfold tailWord_6765067
  simp only [CollatzResearch.WordTrace]
  refine ⟨246742264182325115304093455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164494842788216743536062303 246742264182325115304093455)
  ·
    refine ⟨370113396273487672956140183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246742264182325115304093455 370113396273487672956140183)
    ·
      refine ⟨555170094410231509434210275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370113396273487672956140183 555170094410231509434210275)
      ·
        refine ⟨832755141615347264151315413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555170094410231509434210275 832755141615347264151315413)
        ·
          refine ⟨19517698631609701503546455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 832755141615347264151315413 19517698631609701503546455)
          ·
            refine ⟨29276547947414552255319683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19517698631609701503546455 29276547947414552255319683)
            ·
              refine ⟨43914821921121828382979525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29276547947414552255319683 43914821921121828382979525)
              ·
                refine ⟨8234029110210342821808661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43914821921121828382979525 8234029110210342821808661)
                ·
                  refine ⟨385970114541109819772281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8234029110210342821808661 385970114541109819772281)
                  ·
                    rfl

theorem cell23_6765067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 6].length) (baseStart_6765067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765067 prefixEnd_6765067 := by exact prefixLift 6765067
  have htrace : WordTrace (prefixWord ++ tailWord_6765067) baseStart_6765067 baseEnd_6765067 := by
    simpa [prefixWord, tailWord_6765067, baseEnd_6765067] using wordTrace_append hprefix tailTrace_6765067
  have hstable : (prefixWord ++ tailWord_6765067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765067).length < 2 ^ (prefixWord ++ tailWord_6765067).sum := by decide
  have hdescent : baseEnd_6765067 < baseStart_6765067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765095 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6765095 : Nat := 118140960795 + 6765095 * 2 ^ 59
def prefixEnd_6765095 : Nat := 4983230072969 + 3 ^ 40 * 6765095 * 2
def baseEnd_6765095 : Nat := 3473745408328314268400401

theorem tailTrace_6765095 : CollatzResearch.WordTrace tailWord_6765095 prefixEnd_6765095 3473745408328314268400401 := by
  unfold tailWord_6765095
  simp only [CollatzResearch.WordTrace]
  refine ⟨246743285426223676086112739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164495523617482450724075159 246743285426223676086112739)
  ·
    refine ⟨370114928139335514129169109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246743285426223676086112739 370114928139335514129169109)
    ·
      refine ⟨8674568628265676112402401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 370114928139335514129169109 8674568628265676112402401)
      ·
        refine ⟨6505926471199257084301801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8674568628265676112402401 6505926471199257084301801)
        ·
          refine ⟨4879444853399442813226351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505926471199257084301801 4879444853399442813226351)
          ·
            refine ⟨7319167280099164219839527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879444853399442813226351 7319167280099164219839527)
            ·
              refine ⟨10978750920148746329759291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319167280099164219839527 10978750920148746329759291)
              ·
                refine ⟨16468126380223119494638937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10978750920148746329759291 16468126380223119494638937)
                ·
                  refine ⟨12351094785167339620979203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16468126380223119494638937 12351094785167339620979203)
                  ·
                    refine ⟨18526642177751009431468805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12351094785167339620979203 18526642177751009431468805)
                    ·
                      refine ⟨3473745408328314268400401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18526642177751009431468805 3473745408328314268400401)
                      ·
                        rfl

theorem cell23_6765095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6765095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765095 prefixEnd_6765095 := by exact prefixLift 6765095
  have htrace : WordTrace (prefixWord ++ tailWord_6765095) baseStart_6765095 baseEnd_6765095 := by
    simpa [prefixWord, tailWord_6765095, baseEnd_6765095] using wordTrace_append hprefix tailTrace_6765095
  have hstable : (prefixWord ++ tailWord_6765095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765095).length < 2 ^ (prefixWord ++ tailWord_6765095).sum := by decide
  have hdescent : baseEnd_6765095 < baseStart_6765095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765114 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_6765114 : Nat := 118140960795 + 6765114 * 2 ^ 59
def prefixEnd_6765114 : Nat := 4983230072969 + 3 ^ 40 * 6765114 * 2
def baseEnd_6765114 : Nat := 1157918388153583231354271

theorem tailTrace_6765114 : CollatzResearch.WordTrace tailWord_6765114 prefixEnd_6765114 1157918388153583231354271 := by
  unfold tailWord_6765114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61685994603288710582763599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164495985608769894887369597 61685994603288710582763599)
  ·
    refine ⟨92528991904933065874145399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61685994603288710582763599 92528991904933065874145399)
    ·
      refine ⟨138793487857399598811218099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92528991904933065874145399 138793487857399598811218099)
      ·
        refine ⟨208190231786099398216827149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138793487857399598811218099 208190231786099398216827149)
        ·
          refine ⟨78071336919787274331310181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208190231786099398216827149 78071336919787274331310181)
          ·
            refine ⟨14638375672460113937120659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78071336919787274331310181 14638375672460113937120659)
            ·
              refine ⟨21957563508690170905680989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14638375672460113937120659 21957563508690170905680989)
              ·
                refine ⟨8234086315758814089630371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21957563508690170905680989 8234086315758814089630371)
                ·
                  refine ⟨12351129473638221134445557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234086315758814089630371 12351129473638221134445557)
                  ·
                    refine ⟨1157918388153583231354271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12351129473638221134445557 1157918388153583231354271)
                    ·
                      rfl

theorem cell23_6765114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_6765114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765114 prefixEnd_6765114 := by exact prefixLift 6765114
  have htrace : WordTrace (prefixWord ++ tailWord_6765114) baseStart_6765114 baseEnd_6765114 := by
    simpa [prefixWord, tailWord_6765114, baseEnd_6765114] using wordTrace_append hprefix tailTrace_6765114
  have hstable : (prefixWord ++ tailWord_6765114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765114).length < 2 ^ (prefixWord ++ tailWord_6765114).sum := by decide
  have hdescent : baseEnd_6765114 < baseStart_6765114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765118 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_6765118 : Nat := 118140960795 + 6765118 * 2 ^ 59
def prefixEnd_6765118 : Nat := 4983230072969 + 3 ^ 40 * 6765118 * 2
def baseEnd_6765118 : Nat := 385973024264818630934755

theorem tailTrace_6765118 : CollatzResearch.WordTrace tailWord_6765118 prefixEnd_6765118 385973024264818630934755 := by
  unfold tailWord_6765118
  simp only [CollatzResearch.WordTrace]
  refine ⟨30843015538142543876775001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164496082870093567342800005 30843015538142543876775001)
  ·
    refine ⟨23132261653606907907581251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30843015538142543876775001 23132261653606907907581251)
    ·
      refine ⟨34698392480410361861371877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23132261653606907907581251 34698392480410361861371877)
      ·
        refine ⟨6505948590076942849007227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34698392480410361861371877 6505948590076942849007227)
        ·
          refine ⟨9758922885115414273510841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505948590076942849007227 9758922885115414273510841)
          ·
            refine ⟨7319192163836560705133131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758922885115414273510841 7319192163836560705133131)
            ·
              refine ⟨10978788245754841057699697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319192163836560705133131 10978788245754841057699697)
              ·
                refine ⟨8234091184316130793274773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10978788245754841057699697 8234091184316130793274773)
                ·
                  refine ⟨385973024264818630934755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8234091184316130793274773 385973024264818630934755)
                  ·
                    rfl

theorem cell23_6765118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_6765118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765118 prefixEnd_6765118 := by exact prefixLift 6765118
  have htrace : WordTrace (prefixWord ++ tailWord_6765118) baseStart_6765118 baseEnd_6765118 := by
    simpa [prefixWord, tailWord_6765118, baseEnd_6765118] using wordTrace_append hprefix tailTrace_6765118
  have hstable : (prefixWord ++ tailWord_6765118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765118).length < 2 ^ (prefixWord ++ tailWord_6765118).sum := by decide
  have hdescent : baseEnd_6765118 < baseStart_6765118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765137 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_6765137 : Nat := 118140960795 + 6765137 * 2 ^ 59
def prefixEnd_6765137 : Nat := 4983230072969 + 3 ^ 40 * 6765137 * 2
def baseEnd_6765137 : Nat := 3473766974515803104075207

theorem tailTrace_6765137 : CollatzResearch.WordTrace tailWord_6765137 prefixEnd_6765137 3473766974515803104075207 := by
  unfold tailWord_6765137
  simp only [CollatzResearch.WordTrace]
  refine ⟨246744817292071517259141665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164496544861381011506094443 246744817292071517259141665)
  ·
    refine ⟨185058612969053637944356249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246744817292071517259141665 185058612969053637944356249)
    ·
      refine ⟨138793959726790228458267187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185058612969053637944356249 138793959726790228458267187)
      ·
        refine ⟨208190939590185342687400781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138793959726790228458267187 208190939590185342687400781)
        ·
          refine ⟨78071602346319503507775293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208190939590185342687400781 78071602346319503507775293)
          ·
            refine ⟨29276850879869813815415735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78071602346319503507775293 29276850879869813815415735)
            ·
              refine ⟨43915276319804720723123603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29276850879869813815415735 43915276319804720723123603)
              ·
                refine ⟨65872914479707081084685405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43915276319804720723123603 65872914479707081084685405)
                ·
                  refine ⟨24702342929890155406757027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65872914479707081084685405 24702342929890155406757027)
                  ·
                    refine ⟨37053514394835233110135541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24702342929890155406757027 37053514394835233110135541)
                    ·
                      refine ⟨3473766974515803104075207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37053514394835233110135541 3473766974515803104075207)
                      ·
                        rfl

theorem cell23_6765137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_6765137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765137 prefixEnd_6765137 := by exact prefixLift 6765137
  have htrace : WordTrace (prefixWord ++ tailWord_6765137) baseStart_6765137 baseEnd_6765137 := by
    simpa [prefixWord, tailWord_6765137, baseEnd_6765137] using wordTrace_append hprefix tailTrace_6765137
  have hstable : (prefixWord ++ tailWord_6765137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765137).length < 2 ^ (prefixWord ++ tailWord_6765137).sum := by decide
  have hdescent : baseEnd_6765137 < baseStart_6765137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765144 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_6765144 : Nat := 118140960795 + 6765144 * 2 ^ 59
def prefixEnd_6765144 : Nat := 4983230072969 + 3 ^ 40 * 6765144 * 2
def baseEnd_6765144 : Nat := 1157923522960128192229225

theorem tailTrace_6765144 : CollatzResearch.WordTrace tailWord_6765144 prefixEnd_6765144 1157923522960128192229225 := by
  unfold tailWord_6765144
  simp only [CollatzResearch.WordTrace]
  refine ⟨123372536301523078727323243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164496715068697438303097657 123372536301523078727323243)
  ·
    refine ⟨185058804452284618090984865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123372536301523078727323243 185058804452284618090984865)
    ·
      refine ⟨138794103339213463568238649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185058804452284618090984865 138794103339213463568238649)
      ·
        refine ⟨104095577504410097676178987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138794103339213463568238649 104095577504410097676178987)
        ·
          refine ⟨156143366256615146514268481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104095577504410097676178987 156143366256615146514268481)
          ·
            refine ⟨117107524692461359885701361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156143366256615146514268481 117107524692461359885701361)
            ·
              refine ⟨87830643519346019914276021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117107524692461359885701361 87830643519346019914276021)
              ·
                refine ⟨8234122829938689366963377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87830643519346019914276021 8234122829938689366963377)
                ·
                  refine ⟨6175592122454017025222533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8234122829938689366963377 6175592122454017025222533)
                  ·
                    refine ⟨1157923522960128192229225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175592122454017025222533 1157923522960128192229225)
                    ·
                      rfl

theorem cell23_6765144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_6765144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765144 prefixEnd_6765144 := by exact prefixLift 6765144
  have htrace : WordTrace (prefixWord ++ tailWord_6765144) baseStart_6765144 baseEnd_6765144 := by
    simpa [prefixWord, tailWord_6765144, baseEnd_6765144] using wordTrace_append hprefix tailTrace_6765144
  have hstable : (prefixWord ++ tailWord_6765144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765144).length < 2 ^ (prefixWord ++ tailWord_6765144).sum := by decide
  have hdescent : baseEnd_6765144 < baseStart_6765144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765244 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6765244 : Nat := 118140960795 + 6765244 * 2 ^ 59
def prefixEnd_6765244 : Nat := 4983230072969 + 3 ^ 40 * 6765244 * 2
def baseEnd_6765244 : Nat := 3473821916945834185437215

theorem tailTrace_6765244 : CollatzResearch.WordTrace tailWord_6765244 prefixEnd_6765244 3473821916945834185437215 := by
  unfold tailWord_6765244
  simp only [CollatzResearch.WordTrace]
  refine ⟨123374359951341937266643393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164499146601789249688857857 123374359951341937266643393)
  ·
    refine ⟨92530769963506452949982545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123374359951341937266643393 92530769963506452949982545)
    ·
      refine ⟨69398077472629839712486909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92530769963506452949982545 69398077472629839712486909)
      ·
        refine ⟨26024279052236189892182591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69398077472629839712486909 26024279052236189892182591)
        ·
          refine ⟨39036418578354284838273887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26024279052236189892182591 39036418578354284838273887)
          ·
            refine ⟨58554627867531427257410831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39036418578354284838273887 58554627867531427257410831)
            ·
              refine ⟨87831941801297140886116247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58554627867531427257410831 87831941801297140886116247)
              ·
                refine ⟨131747912701945711329174371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87831941801297140886116247 131747912701945711329174371)
                ·
                  refine ⟨197621869052918566993761557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131747912701945711329174371 197621869052918566993761557)
                  ·
                    refine ⟨9263525111855557827832573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197621869052918566993761557 9263525111855557827832573)
                    ·
                      refine ⟨3473821916945834185437215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263525111855557827832573 3473821916945834185437215)
                      ·
                        rfl

theorem cell23_6765244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6765244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765244 prefixEnd_6765244 := by exact prefixLift 6765244
  have htrace : WordTrace (prefixWord ++ tailWord_6765244) baseStart_6765244 baseEnd_6765244 := by
    simpa [prefixWord, tailWord_6765244, baseEnd_6765244] using wordTrace_append hprefix tailTrace_6765244
  have hstable : (prefixWord ++ tailWord_6765244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765244).length < 2 ^ (prefixWord ++ tailWord_6765244).sum := by decide
  have hdescent : baseEnd_6765244 < baseStart_6765244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765258 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_6765258 : Nat := 118140960795 + 6765258 * 2 ^ 59
def prefixEnd_6765258 : Nat := 4983230072969 + 3 ^ 40 * 6765258 * 2
def baseEnd_6765258 : Nat := 3473829105674997130662151

theorem tailTrace_6765258 : CollatzResearch.WordTrace tailWord_6765258 prefixEnd_6765258 3473829105674997130662151 := by
  unfold tailWord_6765258
  simp only [CollatzResearch.WordTrace]
  refine ⟨61687307631158288731074107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164499487016422103282864285 61687307631158288731074107)
  ·
    refine ⟨92530961446737433096611161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61687307631158288731074107 92530961446737433096611161)
    ·
      refine ⟨69398221085053074822458371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92530961446737433096611161 69398221085053074822458371)
      ·
        refine ⟨104097331627579612233687557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69398221085053074822458371 104097331627579612233687557)
        ·
          refine ⟨19518249680171177293816417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104097331627579612233687557 19518249680171177293816417)
          ·
            refine ⟨14638687260128382970362313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19518249680171177293816417 14638687260128382970362313)
            ·
              refine ⟨10979015445096287227771735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14638687260128382970362313 10979015445096287227771735)
              ·
                refine ⟨16468523167644430841657603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10979015445096287227771735 16468523167644430841657603)
                ·
                  refine ⟨24702784751466646262486405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16468523167644430841657603 24702784751466646262486405)
                  ·
                    refine ⟨4631772140899996174216201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24702784751466646262486405 4631772140899996174216201)
                    ·
                      refine ⟨3473829105674997130662151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631772140899996174216201 3473829105674997130662151)
                      ·
                        rfl

theorem cell23_6765258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_6765258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765258 prefixEnd_6765258 := by exact prefixLift 6765258
  have htrace : WordTrace (prefixWord ++ tailWord_6765258) baseStart_6765258 baseEnd_6765258 := by
    simpa [prefixWord, tailWord_6765258, baseEnd_6765258] using wordTrace_append hprefix tailTrace_6765258
  have hstable : (prefixWord ++ tailWord_6765258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765258).length < 2 ^ (prefixWord ++ tailWord_6765258).sum := by decide
  have hdescent : baseEnd_6765258 < baseStart_6765258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765274 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_6765274 : Nat := 118140960795 + 6765274 * 2 ^ 59
def prefixEnd_6765274 : Nat := 4983230072969 + 3 ^ 40 * 6765274 * 2
def baseEnd_6765274 : Nat := 3473837321365469068062077

theorem tailTrace_6765274 : CollatzResearch.WordTrace tailWord_6765274 prefixEnd_6765274 3473837321365469068062077 := by
  unfold tailWord_6765274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61687453523143797414219719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164499876061716793104585917 61687453523143797414219719)
  ·
    refine ⟨92531180284715696121329579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61687453523143797414219719 92531180284715696121329579)
    ·
      refine ⟨138796770427073544181994369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92531180284715696121329579 138796770427073544181994369)
      ·
        refine ⟨104097577820305158136495777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138796770427073544181994369 104097577820305158136495777)
        ·
          refine ⟨78073183365228868602371833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104097577820305158136495777 78073183365228868602371833)
          ·
            refine ⟨58554887523921651451778875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78073183365228868602371833 58554887523921651451778875)
            ·
              refine ⟨87832331285882477177668313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58554887523921651451778875 87832331285882477177668313)
              ·
                refine ⟨65874248464411857883251235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87832331285882477177668313 65874248464411857883251235)
                ·
                  refine ⟨98811372696617786824876853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65874248464411857883251235 98811372696617786824876853)
                  ·
                    refine ⟨9263566190307917514832205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98811372696617786824876853 9263566190307917514832205)
                    ·
                      refine ⟨3473837321365469068062077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263566190307917514832205 3473837321365469068062077)
                      ·
                        rfl

theorem cell23_6765274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_6765274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765274 prefixEnd_6765274 := by exact prefixLift 6765274
  have htrace : WordTrace (prefixWord ++ tailWord_6765274) baseStart_6765274 baseEnd_6765274 := by
    simpa [prefixWord, tailWord_6765274, baseEnd_6765274] using wordTrace_append hprefix tailTrace_6765274
  have hstable : (prefixWord ++ tailWord_6765274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765274).length < 2 ^ (prefixWord ++ tailWord_6765274).sum := by decide
  have hdescent : baseEnd_6765274 < baseStart_6765274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765281 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 5]
def baseStart_6765281 : Nat := 118140960795 + 6765281 * 2 ^ 59
def prefixEnd_6765281 : Nat := 4983230072969 + 3 ^ 40 * 6765281 * 2
def baseEnd_6765281 : Nat := 385982323970005615630505

theorem tailTrace_6765281 : CollatzResearch.WordTrace tailWord_6765281 prefixEnd_6765281 385982323970005615630505 := by
  unfold tailWord_6765281
  simp only [CollatzResearch.WordTrace]
  refine ⟨246750069403549829852383697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164500046269033219901589131 246750069403549829852383697)
  ·
    refine ⟨185062552052662372389287773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246750069403549829852383697 185062552052662372389287773)
    ·
      refine ⟨69398457019748389645982915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185062552052662372389287773 69398457019748389645982915)
      ·
        refine ⟨104097685529622584468974373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69398457019748389645982915 104097685529622584468974373)
        ·
          refine ⟨19518316036804234587932695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104097685529622584468974373 19518316036804234587932695)
          ·
            refine ⟨29277474055206351881899043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19518316036804234587932695 29277474055206351881899043)
            ·
              refine ⟨43916211082809527822848565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29277474055206351881899043 43916211082809527822848565)
              ·
                refine ⟨4117144789013393233392053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43916211082809527822848565 4117144789013393233392053)
                ·
                  refine ⟨385982323970005615630505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4117144789013393233392053 385982323970005615630505)
                  ·
                    rfl

theorem cell23_6765281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 5].length) (baseStart_6765281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765281 prefixEnd_6765281 := by exact prefixLift 6765281
  have htrace : WordTrace (prefixWord ++ tailWord_6765281) baseStart_6765281 baseEnd_6765281 := by
    simpa [prefixWord, tailWord_6765281, baseEnd_6765281] using wordTrace_append hprefix tailTrace_6765281
  have hstable : (prefixWord ++ tailWord_6765281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765281).length < 2 ^ (prefixWord ++ tailWord_6765281).sum := by decide
  have hdescent : baseEnd_6765281 < baseStart_6765281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765348 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_6765348 : Nat := 118140960795 + 6765348 * 2 ^ 59
def prefixEnd_6765348 : Nat := 4983230072969 + 3 ^ 40 * 6765348 * 2
def baseEnd_6765348 : Nat := 3473875318933901778536737

theorem tailTrace_6765348 : CollatzResearch.WordTrace tailWord_6765348 prefixEnd_6765348 3473875318933901778536737 := by
  unfold tailWord_6765348
  simp only [CollatzResearch.WordTrace]
  refine ⟨123376256547153550147536349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164501675396204733530048465 123376256547153550147536349)
  ·
    refine ⟨46266096205182581305326131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123376256547153550147536349 46266096205182581305326131)
    ·
      refine ⟨69399144307773871957989197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46266096205182581305326131 69399144307773871957989197)
      ·
        refine ⟨26024679115415201984245949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69399144307773871957989197 26024679115415201984245949)
        ·
          refine ⟨9759254668280700744092231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26024679115415201984245949 9759254668280700744092231)
          ·
            refine ⟨14638882002421051116138347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759254668280700744092231 14638882002421051116138347)
            ·
              refine ⟨21958323003631576674207521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14638882002421051116138347 21958323003631576674207521)
              ·
                refine ⟨16468742252723682505655641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21958323003631576674207521 16468742252723682505655641)
                ·
                  refine ⟨12351556689542761879241731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16468742252723682505655641 12351556689542761879241731)
                  ·
                    refine ⟨18527335034314142818862597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12351556689542761879241731 18527335034314142818862597)
                    ·
                      refine ⟨3473875318933901778536737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18527335034314142818862597 3473875318933901778536737)
                      ·
                        rfl

theorem cell23_6765348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_6765348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765348 prefixEnd_6765348 := by exact prefixLift 6765348
  have htrace : WordTrace (prefixWord ++ tailWord_6765348) baseStart_6765348 baseEnd_6765348 := by
    simpa [prefixWord, tailWord_6765348, baseEnd_6765348] using wordTrace_append hprefix tailTrace_6765348
  have hstable : (prefixWord ++ tailWord_6765348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765348).length < 2 ^ (prefixWord ++ tailWord_6765348).sum := by decide
  have hdescent : baseEnd_6765348 < baseStart_6765348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765382 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6765382 : Nat := 118140960795 + 6765382 * 2 ^ 59
def prefixEnd_6765382 : Nat := 4983230072969 + 3 ^ 40 * 6765382 * 2
def baseEnd_6765382 : Nat := 3473892777276154645511581

theorem tailTrace_6765382 : CollatzResearch.WordTrace tailWord_6765382 prefixEnd_6765382 3473892777276154645511581 := by
  unfold tailWord_6765382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711054786755747628181575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164502502117455949401206933 7711054786755747628181575)
  ·
    refine ⟨11566582180133621442272363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711054786755747628181575 11566582180133621442272363)
    ·
      refine ⟨17349873270200432163408545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566582180133621442272363 17349873270200432163408545)
      ·
        refine ⟨13012404952650324122556409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17349873270200432163408545 13012404952650324122556409)
        ·
          refine ⟨9759303714487743091917307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13012404952650324122556409 9759303714487743091917307)
          ·
            refine ⟨14638955571731614637875961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759303714487743091917307 14638955571731614637875961)
            ·
              refine ⟨10979216678798710978406971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14638955571731614637875961 10979216678798710978406971)
              ·
                refine ⟨16468825018198066467610457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10979216678798710978406971 16468825018198066467610457)
                ·
                  refine ⟨12351618763648549850707843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16468825018198066467610457 12351618763648549850707843)
                  ·
                    refine ⟨18527428145472824776061765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12351618763648549850707843 18527428145472824776061765)
                    ·
                      refine ⟨3473892777276154645511581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18527428145472824776061765 3473892777276154645511581)
                      ·
                        rfl

theorem cell23_6765382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6765382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765382 prefixEnd_6765382 := by exact prefixLift 6765382
  have htrace : WordTrace (prefixWord ++ tailWord_6765382) baseStart_6765382 baseEnd_6765382 := by
    simpa [prefixWord, tailWord_6765382, baseEnd_6765382] using wordTrace_append hprefix tailTrace_6765382
  have hstable : (prefixWord ++ tailWord_6765382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765382).length < 2 ^ (prefixWord ++ tailWord_6765382).sum := by decide
  have hdescent : baseEnd_6765382 < baseStart_6765382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765408 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2]
def baseStart_6765408 : Nat := 118140960795 + 6765408 * 2 ^ 59
def prefixEnd_6765408 : Nat := 4983230072969 + 3 ^ 40 * 6765408 * 2
def baseEnd_6765408 : Nat := 3473906127773171543786461

theorem tailTrace_6765408 : CollatzResearch.WordTrace tailWord_6765408 prefixEnd_6765408 3473906127773171543786461 := by
  unfold tailWord_6765408
  simp only [CollatzResearch.WordTrace]
  refine ⟨123377350737044865271128439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164503134316059820361504585 123377350737044865271128439)
  ·
    refine ⟨185066026105567297906692659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123377350737044865271128439 185066026105567297906692659)
    ·
      refine ⟨277599039158350946860038989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185066026105567297906692659 277599039158350946860038989)
      ·
        refine ⟨104099639684381605072514621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277599039158350946860038989 104099639684381605072514621)
        ·
          refine ⟨39037364881643101902192983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104099639684381605072514621 39037364881643101902192983)
          ·
            refine ⟨58556047322464652853289475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39037364881643101902192983 58556047322464652853289475)
            ·
              refine ⟨87834070983696979279934213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58556047322464652853289475 87834070983696979279934213)
              ·
                refine ⟨16468888309443183614987665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87834070983696979279934213 16468888309443183614987665)
                ·
                  refine ⟨12351666232082387711240749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16468888309443183614987665 12351666232082387711240749)
                  ·
                    refine ⟨4631874837030895391715281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12351666232082387711240749 4631874837030895391715281)
                    ·
                      refine ⟨3473906127773171543786461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631874837030895391715281 3473906127773171543786461)
                      ·
                        rfl

theorem cell23_6765408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_6765408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765408 prefixEnd_6765408 := by exact prefixLift 6765408
  have htrace : WordTrace (prefixWord ++ tailWord_6765408) baseStart_6765408 baseEnd_6765408 := by
    simpa [prefixWord, tailWord_6765408, baseEnd_6765408] using wordTrace_append hprefix tailTrace_6765408
  have hstable : (prefixWord ++ tailWord_6765408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765408).length < 2 ^ (prefixWord ++ tailWord_6765408).sum := by decide
  have hdescent : baseEnd_6765408 < baseStart_6765408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765451 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4]
def baseStart_6765451 : Nat := 118140960795 + 6765451 * 2 ^ 59
def prefixEnd_6765451 : Nat := 4983230072969 + 3 ^ 40 * 6765451 * 2
def baseEnd_6765451 : Nat := 3473928207441314875548763

theorem tailTrace_6765451 : CollatzResearch.WordTrace tailWord_6765451 prefixEnd_6765451 3473928207441314875548763 := by
  unfold tailWord_6765451
  simp only [CollatzResearch.WordTrace]
  refine ⟨246756269812933948886072207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164504179875289299257381471 246756269812933948886072207)
  ·
    refine ⟨370134404719400923329108311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246756269812933948886072207 370134404719400923329108311)
    ·
      refine ⟨555201607079101384993662467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370134404719400923329108311 555201607079101384993662467)
      ·
        refine ⟨832802410618652077490493701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555201607079101384993662467 832802410618652077490493701)
        ·
          refine ⟨156150451990997264529467569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 832802410618652077490493701 156150451990997264529467569)
          ·
            refine ⟨117112838993247948397100677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156150451990997264529467569 117112838993247948397100677)
            ·
              refine ⟨21958657311233990324456377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117112838993247948397100677 21958657311233990324456377)
              ·
                refine ⟨16468992983425492743342283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21958657311233990324456377 16468992983425492743342283)
                ·
                  refine ⟨24703489475138239115013425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16468992983425492743342283 24703489475138239115013425)
                  ·
                    refine ⟨18527617106353679336260069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24703489475138239115013425 18527617106353679336260069)
                    ·
                      refine ⟨3473928207441314875548763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18527617106353679336260069 3473928207441314875548763)
                      ·
                        rfl

theorem cell23_6765451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_6765451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765451 prefixEnd_6765451 := by exact prefixLift 6765451
  have htrace : WordTrace (prefixWord ++ tailWord_6765451) baseStart_6765451 baseEnd_6765451 := by
    simpa [prefixWord, tailWord_6765451, baseEnd_6765451] using wordTrace_append hprefix tailTrace_6765451
  have hstable : (prefixWord ++ tailWord_6765451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765451).length < 2 ^ (prefixWord ++ tailWord_6765451).sum := by decide
  have hdescent : baseEnd_6765451 < baseStart_6765451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765472 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 1, 2, 2]
def baseStart_6765472 : Nat := 118140960795 + 6765472 * 2 ^ 59
def prefixEnd_6765472 : Nat := 4983230072969 + 3 ^ 40 * 6765472 * 2
def baseEnd_6765472 : Nat := 3473938990535059293386167

theorem tailTrace_6765472 : CollatzResearch.WordTrace tailWord_6765472 prefixEnd_6765472 3473938990535059293386167 := by
  unfold tailWord_6765472
  simp only [CollatzResearch.WordTrace]
  refine ⟨123378517872928934736293335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164504690497238579648391113 123378517872928934736293335)
  ·
    refine ⟨185067776809393402104440003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123378517872928934736293335 185067776809393402104440003)
    ·
      refine ⟨277601665214090103156660005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185067776809393402104440003 277601665214090103156660005)
      ·
        refine ⟨52050312227641894341873751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277601665214090103156660005 52050312227641894341873751)
        ·
          refine ⟨78075468341462841512810627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52050312227641894341873751 78075468341462841512810627)
          ·
            refine ⟨117113202512194262269215941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78075468341462841512810627 117113202512194262269215941)
            ·
              refine ⟨21958725471036424175477989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117113202512194262269215941 21958725471036424175477989)
              ·
                refine ⟨4117261025819329532902123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21958725471036424175477989 4117261025819329532902123)
                ·
                  refine ⟨6175891538728994299353185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117261025819329532902123 6175891538728994299353185)
                  ·
                    refine ⟨4631918654046745724514889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6175891538728994299353185 4631918654046745724514889)
                    ·
                      refine ⟨3473938990535059293386167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631918654046745724514889 3473938990535059293386167)
                      ·
                        rfl

theorem cell23_6765472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_6765472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765472 prefixEnd_6765472 := by exact prefixLift 6765472
  have htrace : WordTrace (prefixWord ++ tailWord_6765472) baseStart_6765472 baseEnd_6765472 := by
    simpa [prefixWord, tailWord_6765472, baseEnd_6765472] using wordTrace_append hprefix tailTrace_6765472
  have hstable : (prefixWord ++ tailWord_6765472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765472).length < 2 ^ (prefixWord ++ tailWord_6765472).sum := by decide
  have hdescent : baseEnd_6765472 < baseStart_6765472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765485 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6765485 : Nat := 118140960795 + 6765485 * 2 ^ 59
def prefixEnd_6765485 : Nat := 4983230072969 + 3 ^ 40 * 6765485 * 2
def baseEnd_6765485 : Nat := 3473945665783567742523607

theorem tailTrace_6765485 : CollatzResearch.WordTrace tailWord_6765485 prefixEnd_6765485 3473945665783567742523607 := by
  unfold tailWord_6765485
  simp only [CollatzResearch.WordTrace]
  refine ⟨246757509894810772692809909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164505006596540515128539939 246757509894810772692809909)
  ·
    refine ⟨23133516552638509939950929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246757509894810772692809909 23133516552638509939950929)
    ·
      refine ⟨17350137414478882454963197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23133516552638509939950929 17350137414478882454963197)
      ·
        refine ⟨6506301530429580920611199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17350137414478882454963197 6506301530429580920611199)
        ·
          refine ⟨9759452295644371380916799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506301530429580920611199 9759452295644371380916799)
          ·
            refine ⟨14639178443466557071375199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759452295644371380916799 14639178443466557071375199)
            ·
              refine ⟨21958767665199835607062799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14639178443466557071375199 21958767665199835607062799)
              ·
                refine ⟨32938151497799753410594199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21958767665199835607062799 32938151497799753410594199)
                ·
                  refine ⟨49407227246699630115891299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32938151497799753410594199 49407227246699630115891299)
                  ·
                    refine ⟨74110840870049445173836949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49407227246699630115891299 74110840870049445173836949)
                    ·
                      refine ⟨3473945665783567742523607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74110840870049445173836949 3473945665783567742523607)
                      ·
                        rfl

theorem cell23_6765485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6765485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765485 prefixEnd_6765485 := by exact prefixLift 6765485
  have htrace : WordTrace (prefixWord ++ tailWord_6765485) baseStart_6765485 baseEnd_6765485 := by
    simpa [prefixWord, tailWord_6765485, baseEnd_6765485] using wordTrace_append hprefix tailTrace_6765485
  have hstable : (prefixWord ++ tailWord_6765485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765485).length < 2 ^ (prefixWord ++ tailWord_6765485).sum := by decide
  have hdescent : baseEnd_6765485 < baseStart_6765485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765492 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6765492 : Nat := 118140960795 + 6765492 * 2 ^ 59
def prefixEnd_6765492 : Nat := 4983230072969 + 3 ^ 40 * 6765492 * 2
def baseEnd_6765492 : Nat := 3473949260148149215136075

theorem tailTrace_6765492 : CollatzResearch.WordTrace tailWord_6765492 prefixEnd_6765492 3473949260148149215136075 := by
  unfold tailWord_6765492
  simp only [CollatzResearch.WordTrace]
  refine ⟨123378882602892706444157365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164505176803856941925543153 123378882602892706444157365)
  ·
    refine ⟨11566770244021191229139753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123378882602892706444157365 11566770244021191229139753)
    ·
      refine ⟨8675077683015893421854815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11566770244021191229139753 8675077683015893421854815)
      ·
        refine ⟨13012616524523840132782223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675077683015893421854815 13012616524523840132782223)
        ·
          refine ⟨19518924786785760199173335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13012616524523840132782223 19518924786785760199173335)
          ·
            refine ⟨29278387180178640298760003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19518924786785760199173335 29278387180178640298760003)
            ·
              refine ⟨43917580770267960448140005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29278387180178640298760003 43917580770267960448140005)
              ·
                refine ⟨8234546394425242584026251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43917580770267960448140005 8234546394425242584026251)
                ·
                  refine ⟨12351819591637863876039377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234546394425242584026251 12351819591637863876039377)
                  ·
                    refine ⟨9263864693728397907029533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12351819591637863876039377 9263864693728397907029533)
                    ·
                      refine ⟨3473949260148149215136075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263864693728397907029533 3473949260148149215136075)
                      ·
                        rfl

theorem cell23_6765492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6765492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765492 prefixEnd_6765492 := by exact prefixLift 6765492
  have htrace : WordTrace (prefixWord ++ tailWord_6765492) baseStart_6765492 baseEnd_6765492 := by
    simpa [prefixWord, tailWord_6765492, baseEnd_6765492] using wordTrace_append hprefix tailTrace_6765492
  have hstable : (prefixWord ++ tailWord_6765492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765492).length < 2 ^ (prefixWord ++ tailWord_6765492).sum := by decide
  have hdescent : baseEnd_6765492 < baseStart_6765492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765515 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 1, 3, 2]
def baseStart_6765515 : Nat := 118140960795 + 6765515 * 2 ^ 59
def prefixEnd_6765515 : Nat := 4983230072969 + 3 ^ 40 * 6765515 * 2
def baseEnd_6765515 : Nat := 3473961070203202625148469

theorem tailTrace_6765515 : CollatzResearch.WordTrace tailWord_6765515 prefixEnd_6765515 3473961070203202625148469 := by
  unfold tailWord_6765515
  simp only [CollatzResearch.WordTrace]
  refine ⟨246758604084702087816401999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164505736056468058544267999 246758604084702087816401999)
  ·
    refine ⟨370137906127053131724602999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246758604084702087816401999 370137906127053131724602999)
    ·
      refine ⟨555206859190579697586904499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370137906127053131724602999 555206859190579697586904499)
      ·
        refine ⟨832810288785869546380356749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555206859190579697586904499 832810288785869546380356749)
        ·
          refine ⟨312303858294701079892633781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 832810288785869546380356749 312303858294701079892633781)
          ·
            refine ⟨29278486715128226239934417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312303858294701079892633781 29278486715128226239934417)
            ·
              refine ⟨21958865036346169679950813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29278486715128226239934417 21958865036346169679950813)
              ·
                refine ⟨8234574388629813629981555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21958865036346169679950813 8234574388629813629981555)
                ·
                  refine ⟨12351861582944720444972333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234574388629813629981555 12351861582944720444972333)
                  ·
                    refine ⟨4631948093604270166864625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12351861582944720444972333 4631948093604270166864625)
                    ·
                      refine ⟨3473961070203202625148469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631948093604270166864625 3473961070203202625148469)
                      ·
                        rfl

theorem cell23_6765515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3, 2].length) (baseStart_6765515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765515 prefixEnd_6765515 := by exact prefixLift 6765515
  have htrace : WordTrace (prefixWord ++ tailWord_6765515) baseStart_6765515 baseEnd_6765515 := by
    simpa [prefixWord, tailWord_6765515, baseEnd_6765515] using wordTrace_append hprefix tailTrace_6765515
  have hstable : (prefixWord ++ tailWord_6765515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765515).length < 2 ^ (prefixWord ++ tailWord_6765515).sum := by decide
  have hdescent : baseEnd_6765515 < baseStart_6765515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765556 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6765556 : Nat := 118140960795 + 6765556 * 2 ^ 59
def prefixEnd_6765556 : Nat := 4983230072969 + 3 ^ 40 * 6765556 * 2
def baseEnd_6765556 : Nat := 3473982122910036964735781

theorem tailTrace_6765556 : CollatzResearch.WordTrace tailWord_6765556 prefixEnd_6765556 3473982122910036964735781 := by
  unfold tailWord_6765556
  simp only [CollatzResearch.WordTrace]
  refine ⟨123380049738776775909322261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164506732985035701212429681 123380049738776775909322261)
  ·
    refine ⟨5783439831505161370749481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123380049738776775909322261 5783439831505161370749481)
    ·
      refine ⟨4337579873628871028062111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5783439831505161370749481 4337579873628871028062111)
      ·
        refine ⟨6506369810443306542093167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337579873628871028062111 6506369810443306542093167)
        ·
          refine ⟨9759554715664959813139751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506369810443306542093167 9759554715664959813139751)
          ·
            refine ⟨14639332073497439719709627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759554715664959813139751 14639332073497439719709627)
            ·
              refine ⟨21958998110246159579564441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14639332073497439719709627 21958998110246159579564441)
              ·
                refine ⟨16469248582684619684673331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21958998110246159579564441 16469248582684619684673331)
                ·
                  refine ⟨24703872874026929527009997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16469248582684619684673331 24703872874026929527009997)
                  ·
                    refine ⟨9263952327760098572628749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24703872874026929527009997 9263952327760098572628749)
                    ·
                      refine ⟨3473982122910036964735781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9263952327760098572628749 3473982122910036964735781)
                      ·
                        rfl

theorem cell23_6765556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6765556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765556 prefixEnd_6765556 := by exact prefixLift 6765556
  have htrace : WordTrace (prefixWord ++ tailWord_6765556) baseStart_6765556 baseEnd_6765556 := by
    simpa [prefixWord, tailWord_6765556, baseEnd_6765556] using wordTrace_append hprefix tailTrace_6765556
  have hstable : (prefixWord ++ tailWord_6765556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765556).length < 2 ^ (prefixWord ++ tailWord_6765556).sum := by decide
  have hdescent : baseEnd_6765556 < baseStart_6765556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765566 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6765566 : Nat := 118140960795 + 6765566 * 2 ^ 59
def prefixEnd_6765566 : Nat := 4983230072969 + 3 ^ 40 * 6765566 * 2
def baseEnd_6765566 : Nat := 3473987257716581925610735

theorem tailTrace_6765566 : CollatzResearch.WordTrace tailWord_6765566 prefixEnd_6765566 3473987257716581925610735 := by
  unfold tailWord_6765566
  simp only [CollatzResearch.WordTrace]
  refine ⟨30845058025939665440813569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164506976138344882351005701 30845058025939665440813569)
  ·
    refine ⟨23133793519454749080610177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30845058025939665440813569 23133793519454749080610177)
    ·
      refine ⟨17350345139591061810457633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23133793519454749080610177 17350345139591061810457633)
      ·
        refine ⟨13012758854693296357843225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17350345139591061810457633 13012758854693296357843225)
        ·
          refine ⟨9759569141019972268382419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13012758854693296357843225 9759569141019972268382419)
          ·
            refine ⟨14639353711529958402573629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759569141019972268382419 14639353711529958402573629)
            ·
              refine ⟨5489757641823734400965111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14639353711529958402573629 5489757641823734400965111)
              ·
                refine ⟨8234636462735601601447667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489757641823734400965111 8234636462735601601447667)
                ·
                  refine ⟨12351954694103402402171501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234636462735601601447667 12351954694103402402171501)
                  ·
                    refine ⟨4631983010288775900814313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12351954694103402402171501 4631983010288775900814313)
                    ·
                      refine ⟨3473987257716581925610735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4631983010288775900814313 3473987257716581925610735)
                      ·
                        rfl

theorem cell23_6765566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6765566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765566 prefixEnd_6765566 := by exact prefixLift 6765566
  have htrace : WordTrace (prefixWord ++ tailWord_6765566) baseStart_6765566 baseEnd_6765566 := by
    simpa [prefixWord, tailWord_6765566, baseEnd_6765566] using wordTrace_append hprefix tailTrace_6765566
  have hstable : (prefixWord ++ tailWord_6765566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765566).length < 2 ^ (prefixWord ++ tailWord_6765566).sum := by decide
  have hdescent : baseEnd_6765566 < baseStart_6765566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765618 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_6765618 : Nat := 118140960795 + 6765618 * 2 ^ 59
def prefixEnd_6765618 : Nat := 4983230072969 + 3 ^ 40 * 6765618 * 2
def baseEnd_6765618 : Nat := 3474013958710615722160495

theorem tailTrace_6765618 : CollatzResearch.WordTrace tailWord_6765618 prefixEnd_6765618 3474013958710615722160495 := by
  unfold tailWord_6765618
  simp only [CollatzResearch.WordTrace]
  refine ⟨61690590200832234101850377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164508240535552624271601005 61690590200832234101850377)
  ·
    refine ⟨46267942650624175576387783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61690590200832234101850377 46267942650624175576387783)
    ·
      refine ⟨69401913975936263364581675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46267942650624175576387783 69401913975936263364581675)
      ·
        refine ⟨104102870963904395046872513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69401913975936263364581675 104102870963904395046872513)
        ·
          refine ⟨78077153222928296285154385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104102870963904395046872513 78077153222928296285154385)
          ·
            refine ⟨58557864917196222213865789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78077153222928296285154385 58557864917196222213865789)
            ·
              refine ⟨21959199343948583330199671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58557864917196222213865789 21959199343948583330199671)
              ·
                refine ⟨32938799015922874995299507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21959199343948583330199671 32938799015922874995299507)
                ·
                  refine ⟨49408198523884312492949261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32938799015922874995299507 49408198523884312492949261)
                  ·
                    refine ⟨18528074446456617184855973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49408198523884312492949261 18528074446456617184855973)
                    ·
                      refine ⟨3474013958710615722160495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18528074446456617184855973 3474013958710615722160495)
                      ·
                        rfl

theorem cell23_6765618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_6765618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765618 prefixEnd_6765618 := by exact prefixLift 6765618
  have htrace : WordTrace (prefixWord ++ tailWord_6765618) baseStart_6765618 baseEnd_6765618 := by
    simpa [prefixWord, tailWord_6765618, baseEnd_6765618] using wordTrace_append hprefix tailTrace_6765618
  have hstable : (prefixWord ++ tailWord_6765618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765618).length < 2 ^ (prefixWord ++ tailWord_6765618).sum := by decide
  have hdescent : baseEnd_6765618 < baseStart_6765618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765668 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_6765668 : Nat := 118140960795 + 6765668 * 2 ^ 59
def prefixEnd_6765668 : Nat := 4983230072969 + 3 ^ 40 * 6765668 * 2
def baseEnd_6765668 : Nat := 3474039632743340526535265

theorem tailTrace_6765668 : CollatzResearch.WordTrace tailWord_6765668 prefixEnd_6765668 3474039632743340526535265 := by
  unfold tailWord_6765668
  simp only [CollatzResearch.WordTrace]
  refine ⟨123382092226573897473360829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164509456302098529964481105 123382092226573897473360829)
  ·
    refine ⟨46268284584965211552510311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123382092226573897473360829 46268284584965211552510311)
    ·
      refine ⟨69402426877447817328765467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46268284584965211552510311 69402426877447817328765467)
      ·
        refine ⟨104103640316171725993148201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69402426877447817328765467 104103640316171725993148201)
        ·
          refine ⟨78077730237128794494861151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104103640316171725993148201 78077730237128794494861151)
          ·
            refine ⟨117116595355693191742291727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78077730237128794494861151 117116595355693191742291727)
            ·
              refine ⟨175674893033539787613437591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117116595355693191742291727 175674893033539787613437591)
              ·
                refine ⟨263512339550309681420156387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175674893033539787613437591 263512339550309681420156387)
                ·
                  refine ⟨395268509325464522130234581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263512339550309681420156387 395268509325464522130234581)
                  ·
                    refine ⟨9264105687315574737427373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 395268509325464522130234581 9264105687315574737427373)
                    ·
                      refine ⟨3474039632743340526535265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9264105687315574737427373 3474039632743340526535265)
                      ·
                        rfl

theorem cell23_6765668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_6765668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765668 prefixEnd_6765668 := by exact prefixLift 6765668
  have htrace : WordTrace (prefixWord ++ tailWord_6765668) baseStart_6765668 baseEnd_6765668 := by
    simpa [prefixWord, tailWord_6765668, baseEnd_6765668] using wordTrace_append hprefix tailTrace_6765668
  have hstable : (prefixWord ++ tailWord_6765668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765668).length < 2 ^ (prefixWord ++ tailWord_6765668).sum := by decide
  have hdescent : baseEnd_6765668 < baseStart_6765668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765722 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_6765722 : Nat := 118140960795 + 6765722 * 2 ^ 59
def prefixEnd_6765722 : Nat := 4983230072969 + 3 ^ 40 * 6765722 * 2
def baseEnd_6765722 : Nat := 1158022453566227771753339

theorem tailTrace_6765722 : CollatzResearch.WordTrace tailWord_6765722 prefixEnd_6765722 1158022453566227771753339 := by
  unfold tailWord_6765722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61691538498738040542296855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164510769329968108112791613 61691538498738040542296855)
  ·
    refine ⟨92537307748107060813445283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61691538498738040542296855 92537307748107060813445283)
    ·
      refine ⟨138805961622160591220167925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92537307748107060813445283 138805961622160591220167925)
      ·
        refine ⟨13013058902077555426890743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138805961622160591220167925 13013058902077555426890743)
        ·
          refine ⟨19519588353116333140336115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013058902077555426890743 19519588353116333140336115)
          ·
            refine ⟨29279382529674499710504173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19519588353116333140336115 29279382529674499710504173)
            ·
              refine ⟨10979768448627937391439065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29279382529674499710504173 10979768448627937391439065)
              ·
                refine ⟨8234826336470953043579299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10979768448627937391439065 8234826336470953043579299)
                ·
                  refine ⟨12352239504706429565368949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234826336470953043579299 12352239504706429565368949)
                  ·
                    refine ⟨1158022453566227771753339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12352239504706429565368949 1158022453566227771753339)
                    ·
                      rfl

theorem cell23_6765722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_6765722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765722 prefixEnd_6765722 := by exact prefixLift 6765722
  have htrace : WordTrace (prefixWord ++ tailWord_6765722) baseStart_6765722 baseEnd_6765722 := by
    simpa [prefixWord, tailWord_6765722, baseEnd_6765722] using wordTrace_append hprefix tailTrace_6765722
  have hstable : (prefixWord ++ tailWord_6765722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765722).length < 2 ^ (prefixWord ++ tailWord_6765722).sum := by decide
  have hdescent : baseEnd_6765722 < baseStart_6765722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765725 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6765725 : Nat := 118140960795 + 6765725 * 2 ^ 59
def prefixEnd_6765725 : Nat := 4983230072969 + 3 ^ 40 * 6765725 * 2
def baseEnd_6765725 : Nat := 3474068901140646803522503

theorem tailTrace_6765725 : CollatzResearch.WordTrace tailWord_6765725 prefixEnd_6765725 3474068901140646803522503 := by
  unfold tailWord_6765725
  simp only [CollatzResearch.WordTrace]
  refine ⟨246766263413941293681546629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164510842275960862454364419 246766263413941293681546629)
  ·
    refine ⟨46268674390113992565289993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246766263413941293681546629 46268674390113992565289993)
    ·
      refine ⟨34701505792585494423967495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46268674390113992565289993 34701505792585494423967495)
      ·
        refine ⟨52052258688878241635951243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34701505792585494423967495 52052258688878241635951243)
        ·
          refine ⟨78078388033317362453926865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52052258688878241635951243 78078388033317362453926865)
          ·
            refine ⟨58558791024988021840445149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78078388033317362453926865 58558791024988021840445149)
            ·
              refine ⟨21959546634370508190166931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58558791024988021840445149 21959546634370508190166931)
              ·
                refine ⟨32939319951555762285250397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21959546634370508190166931 32939319951555762285250397)
                ·
                  refine ⟨12352244981833410856968899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32939319951555762285250397 12352244981833410856968899)
                  ·
                    refine ⟨18528367472750116285453349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12352244981833410856968899 18528367472750116285453349)
                    ·
                      refine ⟨3474068901140646803522503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18528367472750116285453349 3474068901140646803522503)
                      ·
                        rfl

theorem cell23_6765725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6765725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765725 prefixEnd_6765725 := by exact prefixLift 6765725
  have htrace : WordTrace (prefixWord ++ tailWord_6765725) baseStart_6765725 baseEnd_6765725 := by
    simpa [prefixWord, tailWord_6765725, baseEnd_6765725] using wordTrace_append hprefix tailTrace_6765725
  have hstable : (prefixWord ++ tailWord_6765725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765725).length < 2 ^ (prefixWord ++ tailWord_6765725).sum := by decide
  have hdescent : baseEnd_6765725 < baseStart_6765725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765735 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6765735 : Nat := 118140960795 + 6765735 * 2 ^ 59
def prefixEnd_6765735 : Nat := 4983230072969 + 3 ^ 40 * 6765735 * 2
def baseEnd_6765735 : Nat := 1158024678649063921465819

theorem tailTrace_6765735 : CollatzResearch.WordTrace tailWord_6765735 prefixEnd_6765735 1158024678649063921465819 := by
  unfold tailWord_6765735
  simp only [CollatzResearch.WordTrace]
  refine ⟨246766628143905065389410659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164511085429270043592940439 246766628143905065389410659)
  ·
    refine ⟨370149942215857598084115989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246766628143905065389410659 370149942215857598084115989)
    ·
      refine ⟨17350778541368324910192937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370149942215857598084115989 17350778541368324910192937)
      ·
        refine ⟨13013083906026243682644703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17350778541368324910192937 13013083906026243682644703)
        ·
          refine ⟨19519625859039365523967055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013083906026243682644703 19519625859039365523967055)
          ·
            refine ⟨29279438788559048285950583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19519625859039365523967055 29279438788559048285950583)
            ·
              refine ⟨43919158182838572428925875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29279438788559048285950583 43919158182838572428925875)
              ·
                refine ⟨65878737274257858643388813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43919158182838572428925875 65878737274257858643388813)
                ·
                  refine ⟨24704526477846696991270805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65878737274257858643388813 24704526477846696991270805)
                  ·
                    refine ⟨1158024678649063921465819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24704526477846696991270805 1158024678649063921465819)
                    ·
                      rfl

theorem cell23_6765735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6765735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765735 prefixEnd_6765735 := by exact prefixLift 6765735
  have htrace : WordTrace (prefixWord ++ tailWord_6765735) baseStart_6765735 baseEnd_6765735 := by
    simpa [prefixWord, tailWord_6765735, baseEnd_6765735] using wordTrace_append hprefix tailTrace_6765735
  have hstable : (prefixWord ++ tailWord_6765735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765735).length < 2 ^ (prefixWord ++ tailWord_6765735).sum := by decide
  have hdescent : baseEnd_6765735 < baseStart_6765735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765768 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6765768 : Nat := 118140960795 + 6765768 * 2 ^ 59
def prefixEnd_6765768 : Nat := 4983230072969 + 3 ^ 40 * 6765768 * 2
def baseEnd_6765768 : Nat := 3474090980808790135284805

theorem tailTrace_6765768 : CollatzResearch.WordTrace tailWord_6765768 prefixEnd_6765768 3474090980808790135284805 := by
  unfold tailWord_6765768
  simp only [CollatzResearch.WordTrace]
  refine ⟨123383915876392756012680979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164511887835190341350241305 123383915876392756012680979)
  ·
    refine ⟨185075873814589134019021469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123383915876392756012680979 185075873814589134019021469)
    ·
      refine ⟨69403452680470925257133051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185075873814589134019021469 69403452680470925257133051)
      ·
        refine ⟨104105179020706387885699577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69403452680470925257133051 104105179020706387885699577)
        ·
          refine ⟨78078884265529790914274683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104105179020706387885699577 78078884265529790914274683)
          ·
            refine ⟨117118326398294686371412025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78078884265529790914274683 117118326398294686371412025)
            ·
              refine ⟨87838744798721014778559019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117118326398294686371412025 87838744798721014778559019)
              ·
                refine ⟨131758117198081522167838529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87838744798721014778559019 131758117198081522167838529)
                ·
                  refine ⟨98818587898561141625878897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131758117198081522167838529 98818587898561141625878897)
                  ·
                    refine ⟨74113940923920856219409173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98818587898561141625878897 74113940923920856219409173)
                    ·
                      refine ⟨3474090980808790135284805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74113940923920856219409173 3474090980808790135284805)
                      ·
                        rfl

theorem cell23_6765768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6765768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765768 prefixEnd_6765768 := by exact prefixLift 6765768
  have htrace : WordTrace (prefixWord ++ tailWord_6765768) baseStart_6765768 baseEnd_6765768 := by
    simpa [prefixWord, tailWord_6765768, baseEnd_6765768] using wordTrace_append hprefix tailTrace_6765768
  have hstable : (prefixWord ++ tailWord_6765768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765768).length < 2 ^ (prefixWord ++ tailWord_6765768).sum := by decide
  have hdescent : baseEnd_6765768 < baseStart_6765768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765825 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6765825 : Nat := 118140960795 + 6765825 * 2 ^ 59
def prefixEnd_6765825 : Nat := 4983230072969 + 3 ^ 40 * 6765825 * 2
def baseEnd_6765825 : Nat := 1158040083068698804090681

theorem tailTrace_6765825 : CollatzResearch.WordTrace tailWord_6765825 prefixEnd_6765825 1158040083068698804090681 := by
  unfold tailWord_6765825
  simp only [CollatzResearch.WordTrace]
  refine ⟨246769910713579010760186929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164513273809052673840124619 246769910713579010760186929)
  ·
    refine ⟨185077433035184258070140197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246769910713579010760186929 185077433035184258070140197)
    ·
      refine ⟨34702018694097048388151287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185077433035184258070140197 34702018694097048388151287)
      ·
        refine ⟨52053028041145572582226931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34702018694097048388151287 52053028041145572582226931)
        ·
          refine ⟨78079542061718358873340397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52053028041145572582226931 78079542061718358873340397)
          ·
            refine ⟨29279828273144384577502649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78079542061718358873340397 29279828273144384577502649)
            ·
              refine ⟨21959871204858288433126987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29279828273144384577502649 21959871204858288433126987)
              ·
                refine ⟨32939806807287432649690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21959871204858288433126987 32939806807287432649690481)
                ·
                  refine ⟨24704855105465574487267861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32939806807287432649690481 24704855105465574487267861)
                  ·
                    refine ⟨1158040083068698804090681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24704855105465574487267861 1158040083068698804090681)
                    ·
                      rfl

theorem cell23_6765825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6765825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765825 prefixEnd_6765825 := by exact prefixLift 6765825
  have htrace : WordTrace (prefixWord ++ tailWord_6765825) baseStart_6765825 baseEnd_6765825 := by
    simpa [prefixWord, tailWord_6765825, baseEnd_6765825] using wordTrace_append hprefix tailTrace_6765825
  have hstable : (prefixWord ++ tailWord_6765825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765825).length < 2 ^ (prefixWord ++ tailWord_6765825).sum := by decide
  have hdescent : baseEnd_6765825 < baseStart_6765825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765826 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_6765826 : Nat := 118140960795 + 6765826 * 2 ^ 59
def prefixEnd_6765826 : Nat := 4983230072969 + 3 ^ 40 * 6765826 * 2
def baseEnd_6765826 : Nat := 3474120762686750908359539

theorem tailTrace_6765826 : CollatzResearch.WordTrace tailWord_6765826 prefixEnd_6765826 3474120762686750908359539 := by
  unfold tailWord_6765826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61692486796643846982743333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164513298124383591953982221 61692486796643846982743333)
  ·
    refine ⟨11567341274370721309264375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61692486796643846982743333 11567341274370721309264375)
    ·
      refine ⟨17351011911556081963896563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11567341274370721309264375 17351011911556081963896563)
      ·
        refine ⟨26026517867334122945844845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17351011911556081963896563 26026517867334122945844845)
        ·
          refine ⟨9759944200250296104691817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26026517867334122945844845 9759944200250296104691817)
          ·
            refine ⟨7319958150187722078518863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9759944200250296104691817 7319958150187722078518863)
            ·
              refine ⟨10979937225281583117778295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319958150187722078518863 10979937225281583117778295)
              ·
                refine ⟨16469905837922374676667443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10979937225281583117778295 16469905837922374676667443)
                ·
                  refine ⟨24704858756883562015001165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16469905837922374676667443 24704858756883562015001165)
                  ·
                    refine ⟨9264322033831335755625437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24704858756883562015001165 9264322033831335755625437)
                    ·
                      refine ⟨3474120762686750908359539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9264322033831335755625437 3474120762686750908359539)
                      ·
                        rfl

theorem cell23_6765826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_6765826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765826 prefixEnd_6765826 := by exact prefixLift 6765826
  have htrace : WordTrace (prefixWord ++ tailWord_6765826) baseStart_6765826 baseEnd_6765826 := by
    simpa [prefixWord, tailWord_6765826, baseEnd_6765826] using wordTrace_append hprefix tailTrace_6765826
  have hstable : (prefixWord ++ tailWord_6765826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765826).length < 2 ^ (prefixWord ++ tailWord_6765826).sum := by decide
  have hdescent : baseEnd_6765826 < baseStart_6765826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765866 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6765866 : Nat := 118140960795 + 6765866 * 2 ^ 59
def prefixEnd_6765866 : Nat := 4983230072969 + 3 ^ 40 * 6765866 * 2
def baseEnd_6765866 : Nat := 3474141301912930751859355

theorem tailTrace_6765866 : CollatzResearch.WordTrace tailWord_6765866 prefixEnd_6765866 3474141301912930751859355 := by
  unfold tailWord_6765866
  simp only [CollatzResearch.WordTrace]
  refine ⟨61692851526607618690607363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164514270737620316508286301 61692851526607618690607363)
  ·
    refine ⟨92539277289911428035911045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61692851526607618690607363 92539277289911428035911045)
    ·
      refine ⟨17351114491858392756733321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92539277289911428035911045 17351114491858392756733321)
      ·
        refine ⟨13013335868893794567549991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17351114491858392756733321 13013335868893794567549991)
        ·
          refine ⟨19520003803340691851324987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013335868893794567549991 19520003803340691851324987)
          ·
            refine ⟨29280005705011037776987481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19520003803340691851324987 29280005705011037776987481)
            ·
              refine ⟨21960004278758278332740611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29280005705011037776987481 21960004278758278332740611)
              ·
                refine ⟨32940006418137417499110917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21960004278758278332740611 32940006418137417499110917)
                ·
                  refine ⟨6176251203400765781083297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32940006418137417499110917 6176251203400765781083297)
                  ·
                    refine ⟨4632188402550574335812473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6176251203400765781083297 4632188402550574335812473)
                    ·
                      refine ⟨3474141301912930751859355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632188402550574335812473 3474141301912930751859355)
                      ·
                        rfl

theorem cell23_6765866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6765866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765866 prefixEnd_6765866 := by exact prefixLift 6765866
  have htrace : WordTrace (prefixWord ++ tailWord_6765866) baseStart_6765866 baseEnd_6765866 := by
    simpa [prefixWord, tailWord_6765866, baseEnd_6765866] using wordTrace_append hprefix tailTrace_6765866
  have hstable : (prefixWord ++ tailWord_6765866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765866).length < 2 ^ (prefixWord ++ tailWord_6765866).sum := by decide
  have hdescent : baseEnd_6765866 < baseStart_6765866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765902 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_6765902 : Nat := 118140960795 + 6765902 * 2 ^ 59
def prefixEnd_6765902 : Nat := 4983230072969 + 3 ^ 40 * 6765902 * 2
def baseEnd_6765902 : Nat := 1158053262405497537003063

theorem tailTrace_6765902 : CollatzResearch.WordTrace tailWord_6765902 prefixEnd_6765902 1158053262405497537003063 := by
  unfold tailWord_6765902
  simp only [CollatzResearch.WordTrace]
  refine ⟨30846589891787506613842495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164515146089533368607159973 30846589891787506613842495)
  ·
    refine ⟨46269884837681259920763743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30846589891787506613842495 46269884837681259920763743)
    ·
      refine ⟨69404827256521889881145615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46269884837681259920763743 69404827256521889881145615)
      ·
        refine ⟨104107240884782834821718423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69404827256521889881145615 104107240884782834821718423)
        ·
          refine ⟨156160861327174252232577635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104107240884782834821718423 156160861327174252232577635)
          ·
            refine ⟨234241291990761378348866453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156160861327174252232577635 234241291990761378348866453)
            ·
              refine ⟨10980060562066939610103115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234241291990761378348866453 10980060562066939610103115)
              ·
                refine ⟨16470090843100409415154673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10980060562066939610103115 16470090843100409415154673)
                ·
                  refine ⟨12352568132325307061366005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16470090843100409415154673 12352568132325307061366005)
                  ·
                    refine ⟨1158053262405497537003063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12352568132325307061366005 1158053262405497537003063)
                    ·
                      rfl

theorem cell23_6765902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_6765902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765902 prefixEnd_6765902 := by exact prefixLift 6765902
  have htrace : WordTrace (prefixWord ++ tailWord_6765902) baseStart_6765902 baseEnd_6765902 := by
    simpa [prefixWord, tailWord_6765902, baseEnd_6765902] using wordTrace_append hprefix tailTrace_6765902
  have hstable : (prefixWord ++ tailWord_6765902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765902).length < 2 ^ (prefixWord ++ tailWord_6765902).sum := by decide
  have hdescent : baseEnd_6765902 < baseStart_6765902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765917 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6765917 : Nat := 118140960795 + 6765917 * 2 ^ 59
def prefixEnd_6765917 : Nat := 4983230072969 + 3 ^ 40 * 6765917 * 2
def baseEnd_6765917 : Nat := 3474167489426310052321621

theorem tailTrace_6765917 : CollatzResearch.WordTrace tailWord_6765917 prefixEnd_6765917 3474167489426310052321621 := by
  unfold tailWord_6765917
  simp only [CollatzResearch.WordTrace]
  refine ⟨246773266229245710472536005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164515510819497140315024003 246773266229245710472536005)
  ·
    refine ⟨46269987417983570713600501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246773266229245710472536005 46269987417983570713600501)
    ·
      refine ⟨4337811320435959754400047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46269987417983570713600501 4337811320435959754400047)
      ·
        refine ⟨6506716980653939631600071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337811320435959754400047 6506716980653939631600071)
        ·
          refine ⟨9760075470980909447400107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506716980653939631600071 9760075470980909447400107)
          ·
            refine ⟨14640113206471364171100161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9760075470980909447400107 14640113206471364171100161)
            ·
              refine ⟨10980084904853523128325121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14640113206471364171100161 10980084904853523128325121)
              ·
                refine ⟨8235063678640142346243841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10980084904853523128325121 8235063678640142346243841)
                ·
                  refine ⟨6176297758980106759682881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8235063678640142346243841 6176297758980106759682881)
                  ·
                    refine ⟨4632223319235080069762161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6176297758980106759682881 4632223319235080069762161)
                    ·
                      refine ⟨3474167489426310052321621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632223319235080069762161 3474167489426310052321621)
                      ·
                        rfl

theorem cell23_6765917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6765917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765917 prefixEnd_6765917 := by exact prefixLift 6765917
  have htrace : WordTrace (prefixWord ++ tailWord_6765917) baseStart_6765917 baseEnd_6765917 := by
    simpa [prefixWord, tailWord_6765917, baseEnd_6765917] using wordTrace_append hprefix tailTrace_6765917
  have hstable : (prefixWord ++ tailWord_6765917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765917).length < 2 ^ (prefixWord ++ tailWord_6765917).sum := by decide
  have hdescent : baseEnd_6765917 < baseStart_6765917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765925 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6765925 : Nat := 118140960795 + 6765925 * 2 ^ 59
def prefixEnd_6765925 : Nat := 4983230072969 + 3 ^ 40 * 6765925 * 2
def baseEnd_6765925 : Nat := 3474171597271546021021583

theorem tailTrace_6765925 : CollatzResearch.WordTrace tailWord_6765925 prefixEnd_6765925 3474171597271546021021583 := by
  unfold tailWord_6765925
  simp only [CollatzResearch.WordTrace]
  refine ⟨246773558013216727838827229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164515705342144485225884819 246773558013216727838827229)
  ·
    refine ⟨92540084254956272939560211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246773558013216727838827229 92540084254956272939560211)
    ·
      refine ⟨138810126382434409409340317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92540084254956272939560211 138810126382434409409340317)
      ·
        refine ⟨52053797393412903528502619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138810126382434409409340317 52053797393412903528502619)
        ·
          refine ⟨78080696090119355292753929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52053797393412903528502619 78080696090119355292753929)
          ·
            refine ⟨58560522067589516469565447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78080696090119355292753929 58560522067589516469565447)
            ·
              refine ⟨87840783101384274704348171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58560522067589516469565447 87840783101384274704348171)
              ·
                refine ⟨131761174652076412056522257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87840783101384274704348171 131761174652076412056522257)
                ·
                  refine ⟨98820880989057309042391693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131761174652076412056522257 98820880989057309042391693)
                  ·
                    refine ⟨37057830370896490890896885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98820880989057309042391693 37057830370896490890896885)
                    ·
                      refine ⟨3474171597271546021021583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37057830370896490890896885 3474171597271546021021583)
                      ·
                        rfl

theorem cell23_6765925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6765925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765925 prefixEnd_6765925 := by exact prefixLift 6765925
  have htrace : WordTrace (prefixWord ++ tailWord_6765925) baseStart_6765925 baseEnd_6765925 := by
    simpa [prefixWord, tailWord_6765925, baseEnd_6765925] using wordTrace_append hprefix tailTrace_6765925
  have hstable : (prefixWord ++ tailWord_6765925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765925).length < 2 ^ (prefixWord ++ tailWord_6765925).sum := by decide
  have hdescent : baseEnd_6765925 < baseStart_6765925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6765959 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_6765959 : Nat := 118140960795 + 6765959 * 2 ^ 59
def prefixEnd_6765959 : Nat := 4983230072969 + 3 ^ 40 * 6765959 * 2
def baseEnd_6765959 : Nat := 3474189055613798887996427

theorem tailTrace_6765959 : CollatzResearch.WordTrace tailWord_6765959 prefixEnd_6765959 3474189055613798887996427 := by
  unfold tailWord_6765959
  simp only [CollatzResearch.WordTrace]
  refine ⟨246774798095093551645564931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164516532063395701097043287 246774798095093551645564931)
  ·
    refine ⟨370162197142640327468347397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246774798095093551645564931 370162197142640327468347397)
    ·
      refine ⟨69405411964245061400315137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370162197142640327468347397 69405411964245061400315137)
      ·
        refine ⟨52054058973183796050236353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69405411964245061400315137 52054058973183796050236353)
        ·
          refine ⟨39040544229887847037677265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52054058973183796050236353 39040544229887847037677265)
          ·
            refine ⟨29280408172415885278257949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39040544229887847037677265 29280408172415885278257949)
            ·
              refine ⟨10980153064655956979346731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29280408172415885278257949 10980153064655956979346731)
              ·
                refine ⟨16470229596983935469020097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10980153064655956979346731 16470229596983935469020097)
                ·
                  refine ⟨12352672197737951601765073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16470229596983935469020097 12352672197737951601765073)
                  ·
                    refine ⟨9264504148303463701323805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12352672197737951601765073 9264504148303463701323805)
                    ·
                      refine ⟨3474189055613798887996427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9264504148303463701323805 3474189055613798887996427)
                      ·
                        rfl

theorem cell23_6765959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_6765959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6765959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6765959 prefixEnd_6765959 := by exact prefixLift 6765959
  have htrace : WordTrace (prefixWord ++ tailWord_6765959) baseStart_6765959 baseEnd_6765959 := by
    simpa [prefixWord, tailWord_6765959, baseEnd_6765959] using wordTrace_append hprefix tailTrace_6765959
  have hstable : (prefixWord ++ tailWord_6765959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6765959).length < 2 ^ (prefixWord ++ tailWord_6765959).sum := by decide
  have hdescent : baseEnd_6765959 < baseStart_6765959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6765959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766042 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_6766042 : Nat := 118140960795 + 6766042 * 2 ^ 59
def prefixEnd_6766042 : Nat := 4983230072969 + 3 ^ 40 * 6766042 * 2
def baseEnd_6766042 : Nat := 3474231674508122063258545

theorem tailTrace_6766042 : CollatzResearch.WordTrace tailWord_6766042 prefixEnd_6766042 3474231674508122063258545 := by
  unfold tailWord_6766042
  simp only [CollatzResearch.WordTrace]
  refine ⟨61694456338448214205209095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164518550235861904547224253 61694456338448214205209095)
  ·
    refine ⟨92541684507672321307813643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61694456338448214205209095 92541684507672321307813643)
    ·
      refine ⟨138812526761508481961720465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92541684507672321307813643 138812526761508481961720465)
      ·
        refine ⟨104109395071131361471290349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138812526761508481961720465 104109395071131361471290349)
        ·
          refine ⟨39041023151674260551733881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104109395071131361471290349 39041023151674260551733881)
          ·
            refine ⟨29280767363755695413800411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39041023151674260551733881 29280767363755695413800411)
            ·
              refine ⟨43921151045633543120700617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29280767363755695413800411 43921151045633543120700617)
              ·
                refine ⟨32940863284225157340525463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43921151045633543120700617 32940863284225157340525463)
                ·
                  refine ⟨49411294926337736010788195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32940863284225157340525463 49411294926337736010788195)
                  ·
                    refine ⟨74116942389506604016182293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49411294926337736010788195 74116942389506604016182293)
                    ·
                      refine ⟨3474231674508122063258545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74116942389506604016182293 3474231674508122063258545)
                      ·
                        rfl

theorem cell23_6766042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_6766042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766042 prefixEnd_6766042 := by exact prefixLift 6766042
  have htrace : WordTrace (prefixWord ++ tailWord_6766042) baseStart_6766042 baseEnd_6766042 := by
    simpa [prefixWord, tailWord_6766042, baseEnd_6766042] using wordTrace_append hprefix tailTrace_6766042
  have hstable : (prefixWord ++ tailWord_6766042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766042).length < 2 ^ (prefixWord ++ tailWord_6766042).sum := by decide
  have hdescent : baseEnd_6766042 < baseStart_6766042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766066 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6766066 : Nat := 118140960795 + 6766066 * 2 ^ 59
def prefixEnd_6766066 : Nat := 4983230072969 + 3 ^ 40 * 6766066 * 2
def baseEnd_6766066 : Nat := 3474243998043829969358435

theorem tailTrace_6766066 : CollatzResearch.WordTrace tailWord_6766066 prefixEnd_6766066 3474243998043829969358435 := by
  unfold tailWord_6766066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61694675176426477229927513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164519133803803939279806701 61694675176426477229927513)
  ·
    refine ⟨46271006382319857922445635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61694675176426477229927513 46271006382319857922445635)
    ·
      refine ⟨69406509573479786883668453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46271006382319857922445635 69406509573479786883668453)
      ·
        refine ⟨13013720545027460040687835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69406509573479786883668453 13013720545027460040687835)
        ·
          refine ⟨19520580817541190061031753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013720545027460040687835 19520580817541190061031753)
          ·
            refine ⟨14640435613155892545773815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19520580817541190061031753 14640435613155892545773815)
            ·
              refine ⟨21960653419733838818660723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14640435613155892545773815 21960653419733838818660723)
              ·
                refine ⟨32940980129600758227991085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21960653419733838818660723 32940980129600758227991085)
                ·
                  refine ⟨12352867548600284335496657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32940980129600758227991085 12352867548600284335496657)
                  ·
                    refine ⟨9264650661450213251622493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12352867548600284335496657 9264650661450213251622493)
                    ·
                      refine ⟨3474243998043829969358435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9264650661450213251622493 3474243998043829969358435)
                      ·
                        rfl

theorem cell23_6766066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6766066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766066 prefixEnd_6766066 := by exact prefixLift 6766066
  have htrace : WordTrace (prefixWord ++ tailWord_6766066) baseStart_6766066 baseEnd_6766066 := by
    simpa [prefixWord, tailWord_6766066, baseEnd_6766066] using wordTrace_append hprefix tailTrace_6766066
  have hstable : (prefixWord ++ tailWord_6766066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766066).length < 2 ^ (prefixWord ++ tailWord_6766066).sum := by decide
  have hdescent : baseEnd_6766066 < baseStart_6766066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766069 : List Nat := [1, 3, 5, 1, 1, 1, 2, 9]
def baseStart_6766069 : Nat := 118140960795 + 6766069 * 2 ^ 59
def prefixEnd_6766069 : Nat := 4983230072969 + 3 ^ 40 * 6766069 * 2
def baseEnd_6766069 : Nat := 128675760684659016948923

theorem tailTrace_6766069 : CollatzResearch.WordTrace tailWord_6766069 prefixEnd_6766069 128675760684659016948923 := by
  unfold tailWord_6766069
  simp only [CollatzResearch.WordTrace]
  refine ⟨246778810124695040432069261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164519206749796693621379507 246778810124695040432069261)
  ·
    refine ⟨92542053796760640162025973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246778810124695040432069261 92542053796760640162025973)
    ·
      refine ⟨8675817543446310015189935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92542053796760640162025973 8675817543446310015189935)
      ·
        refine ⟨13013726315169465022784903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675817543446310015189935 13013726315169465022784903)
        ·
          refine ⟨19520589472754197534177355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013726315169465022784903 19520589472754197534177355)
          ·
            refine ⟨29280884209131296301266033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19520589472754197534177355 29280884209131296301266033)
            ·
              refine ⟨21960663156848472225949525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29280884209131296301266033 21960663156848472225949525)
              ·
                refine ⟨128675760684659016948923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21960663156848472225949525 128675760684659016948923)
                ·
                  rfl

theorem cell23_6766069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 9].length) (baseStart_6766069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766069 prefixEnd_6766069 := by exact prefixLift 6766069
  have htrace : WordTrace (prefixWord ++ tailWord_6766069) baseStart_6766069 baseEnd_6766069 := by
    simpa [prefixWord, tailWord_6766069, baseEnd_6766069] using wordTrace_append hprefix tailTrace_6766069
  have hstable : (prefixWord ++ tailWord_6766069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766069).length < 2 ^ (prefixWord ++ tailWord_6766069).sum := by decide
  have hdescent : baseEnd_6766069 < baseStart_6766069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766079 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 3]
def baseStart_6766079 : Nat := 118140960795 + 6766079 * 2 ^ 59
def prefixEnd_6766079 : Nat := 4983230072969 + 3 ^ 40 * 6766079 * 2
def baseEnd_6766079 : Nat := 3474250673292338418495875

theorem tailTrace_6766079 : CollatzResearch.WordTrace tailWord_6766079 prefixEnd_6766079 3474250673292338418495875 := by
  unfold tailWord_6766079
  simp only [CollatzResearch.WordTrace]
  refine ⟨246779174854658812139933291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164519449903105874759955527 246779174854658812139933291)
  ·
    refine ⟨370168762281988218209899937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246779174854658812139933291 370168762281988218209899937)
    ·
      refine ⟨277626571711491163657424953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370168762281988218209899937 277626571711491163657424953)
      ·
        refine ⟨208219928783618372743068715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277626571711491163657424953 208219928783618372743068715)
        ·
          refine ⟨312329893175427559114603073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208219928783618372743068715 312329893175427559114603073)
          ·
            refine ⟨234247419881570669335952305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312329893175427559114603073 234247419881570669335952305)
            ·
              refine ⟨175685564911178002001964229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234247419881570669335952305 175685564911178002001964229)
              ·
                refine ⟨32941043420845875375368293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175685564911178002001964229 32941043420845875375368293)
                ·
                  refine ⟨6176445641408601632881555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32941043420845875375368293 6176445641408601632881555)
                  ·
                    refine ⟨9264668462112902449322333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6176445641408601632881555 9264668462112902449322333)
                    ·
                      refine ⟨3474250673292338418495875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9264668462112902449322333 3474250673292338418495875)
                      ·
                        rfl

theorem cell23_6766079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_6766079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766079 prefixEnd_6766079 := by exact prefixLift 6766079
  have htrace : WordTrace (prefixWord ++ tailWord_6766079) baseStart_6766079 baseEnd_6766079 := by
    simpa [prefixWord, tailWord_6766079, baseEnd_6766079] using wordTrace_append hprefix tailTrace_6766079
  have hstable : (prefixWord ++ tailWord_6766079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766079).length < 2 ^ (prefixWord ++ tailWord_6766079).sum := by decide
  have hdescent : baseEnd_6766079 < baseStart_6766079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766086 : List Nat := [6, 2, 1, 1, 13]
def baseStart_6766086 : Nat := 118140960795 + 6766086 * 2 ^ 59
def prefixEnd_6766086 : Nat := 4983230072969 + 3 ^ 40 * 6766086 * 2
def baseEnd_6766086 : Nat := 4765780888418271455567

theorem tailTrace_6766086 : CollatzResearch.WordTrace tailWord_6766086 prefixEnd_6766086 4765780888418271455567 := by
  unfold tailWord_6766086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711857192676045385482441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164519620110422301556958741 7711857192676045385482441)
  ·
    refine ⟨5783892894507034039111831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7711857192676045385482441 5783892894507034039111831)
    ·
      refine ⟨8675839341760551058667747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783892894507034039111831 8675839341760551058667747)
      ·
        refine ⟨13013759012640826588001621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675839341760551058667747 13013759012640826588001621)
        ·
          refine ⟨4765780888418271455567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13013759012640826588001621 4765780888418271455567)
          ·
            rfl

theorem cell23_6766086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 13].length) (baseStart_6766086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766086 prefixEnd_6766086 := by exact prefixLift 6766086
  have htrace : WordTrace (prefixWord ++ tailWord_6766086) baseStart_6766086 baseEnd_6766086 := by
    simpa [prefixWord, tailWord_6766086, baseEnd_6766086] using wordTrace_append hprefix tailTrace_6766086
  have hstable : (prefixWord ++ tailWord_6766086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766086).length < 2 ^ (prefixWord ++ tailWord_6766086).sum := by decide
  have hdescent : baseEnd_6766086 < baseStart_6766086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766136 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_6766136 : Nat := 118140960795 + 6766136 * 2 ^ 59
def prefixEnd_6766136 : Nat := 4983230072969 + 3 ^ 40 * 6766136 * 2
def baseEnd_6766136 : Nat := 3474279941689644695483113

theorem tailTrace_6766136 : CollatzResearch.WordTrace tailWord_6766136 prefixEnd_6766136 3474279941689644695483113 := by
  unfold tailWord_6766136
  simp only [CollatzResearch.WordTrace]
  refine ⟨123390626907726155437379131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164520835876968207249838841 123390626907726155437379131)
  ·
    refine ⟨185085940361589233156068697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123390626907726155437379131 185085940361589233156068697)
    ·
      refine ⟨138814455271191924867051523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185085940361589233156068697 138814455271191924867051523)
      ·
        refine ⟨208221682906787887300577285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138814455271191924867051523 208221682906787887300577285)
        ·
          refine ⟨39041565545022728868858241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208221682906787887300577285 39041565545022728868858241)
          ·
            refine ⟨29281174158767046651643681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39041565545022728868858241 29281174158767046651643681)
            ·
              refine ⟨21960880619075284988732761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29281174158767046651643681 21960880619075284988732761)
              ·
                refine ⟨16470660464306463741549571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21960880619075284988732761 16470660464306463741549571)
                ·
                  refine ⟨24705990696459695612324357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16470660464306463741549571 24705990696459695612324357)
                  ·
                    refine ⟨4632373255586192927310817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24705990696459695612324357 4632373255586192927310817)
                    ·
                      refine ⟨3474279941689644695483113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632373255586192927310817 3474279941689644695483113)
                      ·
                        rfl

theorem cell23_6766136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_6766136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766136 prefixEnd_6766136 := by exact prefixLift 6766136
  have htrace : WordTrace (prefixWord ++ tailWord_6766136) baseStart_6766136 baseEnd_6766136 := by
    simpa [prefixWord, tailWord_6766136, baseEnd_6766136] using wordTrace_append hprefix tailTrace_6766136
  have hstable : (prefixWord ++ tailWord_6766136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766136).length < 2 ^ (prefixWord ++ tailWord_6766136).sum := by decide
  have hdescent : baseEnd_6766136 < baseStart_6766136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766229 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_6766229 : Nat := 118140960795 + 6766229 * 2 ^ 59
def prefixEnd_6766229 : Nat := 4983230072969 + 3 ^ 40 * 6766229 * 2
def baseEnd_6766229 : Nat := 3474327695390512831620185

theorem tailTrace_6766229 : CollatzResearch.WordTrace tailWord_6766229 prefixEnd_6766229 3474327695390512831620185 := by
  unfold tailWord_6766229
  simp only [CollatzResearch.WordTrace]
  refine ⟨246784645804115387757893741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164523097202743591838595827 246784645804115387757893741)
  ·
    refine ⟨92544242176543270409210153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246784645804115387757893741 92544242176543270409210153)
    ·
      refine ⟨69408181632407452806907615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92544242176543270409210153 69408181632407452806907615)
      ·
        refine ⟨104112272448611179210361423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69408181632407452806907615 104112272448611179210361423)
        ·
          refine ⟨156168408672916768815542135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104112272448611179210361423 156168408672916768815542135)
          ·
            refine ⟨234252613009375153223313203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156168408672916768815542135 234252613009375153223313203)
            ·
              refine ⟨351378919514062729834969805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234252613009375153223313203 351378919514062729834969805)
              ·
                refine ⟨131767094817773523688113677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351378919514062729834969805 131767094817773523688113677)
                ·
                  refine ⟨49412660556665071383042629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131767094817773523688113677 49412660556665071383042629)
                  ·
                    refine ⟨9264873854374700884320493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49412660556665071383042629 9264873854374700884320493)
                    ·
                      refine ⟨3474327695390512831620185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9264873854374700884320493 3474327695390512831620185)
                      ·
                        rfl

theorem cell23_6766229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_6766229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766229 prefixEnd_6766229 := by exact prefixLift 6766229
  have htrace : WordTrace (prefixWord ++ tailWord_6766229) baseStart_6766229 baseEnd_6766229 := by
    simpa [prefixWord, tailWord_6766229, baseEnd_6766229] using wordTrace_append hprefix tailTrace_6766229
  have hstable : (prefixWord ++ tailWord_6766229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766229).length < 2 ^ (prefixWord ++ tailWord_6766229).sum := by decide
  have hdescent : baseEnd_6766229 < baseStart_6766229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766266 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_6766266 : Nat := 118140960795 + 6766266 * 2 ^ 59
def prefixEnd_6766266 : Nat := 4983230072969 + 3 ^ 40 * 6766266 * 2
def baseEnd_6766266 : Nat := 386038521574969909650835

theorem tailTrace_6766266 : CollatzResearch.WordTrace tailWord_6766266 prefixEnd_6766266 386038521574969909650835 := by
  unfold tailWord_6766266
  simp only [CollatzResearch.WordTrace]
  refine ⟨61696498826245335769247663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164523996869987562051327101 61696498826245335769247663)
  ·
    refine ⟨92544748239368003653871495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61696498826245335769247663 92544748239368003653871495)
    ·
      refine ⟨138817122359052005480807243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92544748239368003653871495 138817122359052005480807243)
      ·
        refine ⟨208225683538578008221210865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138817122359052005480807243 208225683538578008221210865)
        ·
          refine ⟨156169262653933506165908149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208225683538578008221210865 156169262653933506165908149)
          ·
            refine ⟨14640868373806266203053889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156169262653933506165908149 14640868373806266203053889)
            ·
              refine ⟨10980651280354699652290417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14640868373806266203053889 10980651280354699652290417)
              ·
                refine ⟨8235488460266024739217813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10980651280354699652290417 8235488460266024739217813)
                ·
                  refine ⟨386038521574969909650835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8235488460266024739217813 386038521574969909650835)
                  ·
                    rfl

theorem cell23_6766266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_6766266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766266 prefixEnd_6766266 := by exact prefixLift 6766266
  have htrace : WordTrace (prefixWord ++ tailWord_6766266) baseStart_6766266 baseEnd_6766266 := by
    simpa [prefixWord, tailWord_6766266, baseEnd_6766266] using wordTrace_append hprefix tailTrace_6766266
  have hstable : (prefixWord ++ tailWord_6766266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766266).length < 2 ^ (prefixWord ++ tailWord_6766266).sum := by decide
  have hdescent : baseEnd_6766266 < baseStart_6766266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766269 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6766269 : Nat := 118140960795 + 6766269 * 2 ^ 59
def prefixEnd_6766269 : Nat := 4983230072969 + 3 ^ 40 * 6766269 * 2
def baseEnd_6766269 : Nat := 3474348234616692675120001

theorem tailTrace_6766269 : CollatzResearch.WordTrace tailWord_6766269 prefixEnd_6766269 3474348234616692675120001 := by
  unfold tailWord_6766269
  simp only [CollatzResearch.WordTrace]
  refine ⟨246786104723970474589349861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164524069815980316392899907 246786104723970474589349861)
  ·
    refine ⟨46272394635744463985503099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246786104723970474589349861 46272394635744463985503099)
    ·
      refine ⟨69408591953616695978254649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46272394635744463985503099 69408591953616695978254649)
      ·
        refine ⟨52056443965212521983690987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69408591953616695978254649 52056443965212521983690987)
        ·
          refine ⟨78084665947818782975536481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52056443965212521983690987 78084665947818782975536481)
          ·
            refine ⟨58563499460864087231652361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78084665947818782975536481 58563499460864087231652361)
            ·
              refine ⟨43922624595648065423739271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58563499460864087231652361 43922624595648065423739271)
              ·
                refine ⟨65883936893472098135608907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43922624595648065423739271 65883936893472098135608907)
                ·
                  refine ⟨98825905340208147203413361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65883936893472098135608907 98825905340208147203413361)
                  ·
                    refine ⟨74119429005156110402560021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98825905340208147203413361 74119429005156110402560021)
                    ·
                      refine ⟨3474348234616692675120001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74119429005156110402560021 3474348234616692675120001)
                      ·
                        rfl

theorem cell23_6766269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6766269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766269 prefixEnd_6766269 := by exact prefixLift 6766269
  have htrace : WordTrace (prefixWord ++ tailWord_6766269) baseStart_6766269 baseEnd_6766269 := by
    simpa [prefixWord, tailWord_6766269, baseEnd_6766269] using wordTrace_append hprefix tailTrace_6766269
  have hstable : (prefixWord ++ tailWord_6766269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766269).length < 2 ^ (prefixWord ++ tailWord_6766269).sum := by decide
  have hdescent : baseEnd_6766269 < baseStart_6766269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766270 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6766270 : Nat := 118140960795 + 6766270 * 2 ^ 59
def prefixEnd_6766270 : Nat := 4983230072969 + 3 ^ 40 * 6766270 * 2
def baseEnd_6766270 : Nat := 1158116249365782390402499

theorem tailTrace_6766270 : CollatzResearch.WordTrace tailWord_6766270 prefixEnd_6766270 1158116249365782390402499 := by
  unfold tailWord_6766270
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848267649620856470017033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164524094131311234506757509 30848267649620856470017033)
  ·
    refine ⟨23136200737215642352512775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30848267649620856470017033 23136200737215642352512775)
    ·
      refine ⟨34704301105823463528769163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23136200737215642352512775 34704301105823463528769163)
      ·
        refine ⟨52056451658735195293153745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34704301105823463528769163 52056451658735195293153745)
        ·
          refine ⟨39042338744051396469865309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52056451658735195293153745 39042338744051396469865309)
          ·
            refine ⟨14640877029019273676199491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39042338744051396469865309 14640877029019273676199491)
            ·
              refine ⟨21961315543528910514299237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14640877029019273676199491 21961315543528910514299237)
              ·
                refine ⟨4117746664411670721431107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21961315543528910514299237 4117746664411670721431107)
                ·
                  refine ⟨6176619996617506082146661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117746664411670721431107 6176619996617506082146661)
                  ·
                    refine ⟨1158116249365782390402499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6176619996617506082146661 1158116249365782390402499)
                    ·
                      rfl

theorem cell23_6766270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6766270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766270 prefixEnd_6766270 := by exact prefixLift 6766270
  have htrace : WordTrace (prefixWord ++ tailWord_6766270) baseStart_6766270 baseEnd_6766270 := by
    simpa [prefixWord, tailWord_6766270, baseEnd_6766270] using wordTrace_append hprefix tailTrace_6766270
  have hstable : (prefixWord ++ tailWord_6766270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766270).length < 2 ^ (prefixWord ++ tailWord_6766270).sum := by decide
  have hdescent : baseEnd_6766270 < baseStart_6766270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766279 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 5, 5]
def baseStart_6766279 : Nat := 118140960795 + 6766279 * 2 ^ 59
def prefixEnd_6766279 : Nat := 4983230072969 + 3 ^ 40 * 6766279 * 2
def baseEnd_6766279 : Nat := 1158117789807745878664985

theorem tailTrace_6766279 : CollatzResearch.WordTrace tailWord_6766279 prefixEnd_6766279 1158117789807745878664985 := by
  unfold tailWord_6766279
  simp only [CollatzResearch.WordTrace]
  refine ⟨246786469453934246297213891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164524312969289497531475927 246786469453934246297213891)
  ·
    refine ⟨370179704180901369445820837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246786469453934246297213891 370179704180901369445820837)
    ·
      refine ⟨69408694533919006771091407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370179704180901369445820837 69408694533919006771091407)
      ·
        refine ⟨104113041800878510156637111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69408694533919006771091407 104113041800878510156637111)
        ·
          refine ⟨156169562701317765234955667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104113041800878510156637111 156169562701317765234955667)
          ·
            refine ⟨234254344051976647852433501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156169562701317765234955667 234254344051976647852433501)
            ·
              refine ⟨87845379019491242944662563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234254344051976647852433501 87845379019491242944662563)
              ·
                refine ⟨131768068529236864416993845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87845379019491242944662563 131768068529236864416993845)
                ·
                  refine ⟨12353256424615956039093173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131768068529236864416993845 12353256424615956039093173)
                  ·
                    refine ⟨1158117789807745878664985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12353256424615956039093173 1158117789807745878664985)
                    ·
                      rfl

theorem cell23_6766279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_6766279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766279 prefixEnd_6766279 := by exact prefixLift 6766279
  have htrace : WordTrace (prefixWord ++ tailWord_6766279) baseStart_6766279 baseEnd_6766279 := by
    simpa [prefixWord, tailWord_6766279, baseEnd_6766279] using wordTrace_append hprefix tailTrace_6766279
  have hstable : (prefixWord ++ tailWord_6766279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766279).length < 2 ^ (prefixWord ++ tailWord_6766279).sum := by decide
  have hdescent : baseEnd_6766279 < baseStart_6766279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766294 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6766294 : Nat := 118140960795 + 6766294 * 2 ^ 59
def prefixEnd_6766294 : Nat := 4983230072969 + 3 ^ 40 * 6766294 * 2
def baseEnd_6766294 : Nat := 3474361071633055077307387

theorem tailTrace_6766294 : CollatzResearch.WordTrace tailWord_6766294 prefixEnd_6766294 3474361071633055077307387 := by
  unfold tailWord_6766294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424188534304993991188121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164524677699253269239339957 15424188534304993991188121)
  ·
    refine ⟨11568141400728745493391091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15424188534304993991188121 11568141400728745493391091)
    ·
      refine ⟨17352212101093118240086637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11568141400728745493391091 17352212101093118240086637)
      ·
        refine ⟨6507079537909919340032489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17352212101093118240086637 6507079537909919340032489)
        ·
          refine ⟨4880309653432439505024367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6507079537909919340032489 4880309653432439505024367)
          ·
            refine ⟨7320464480148659257536551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880309653432439505024367 7320464480148659257536551)
            ·
              refine ⟨10980696720222988886304827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7320464480148659257536551 10980696720222988886304827)
              ·
                refine ⟨16471045080334483329457241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10980696720222988886304827 16471045080334483329457241)
                ·
                  refine ⟨12353283810250862497092931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16471045080334483329457241 12353283810250862497092931)
                  ·
                    refine ⟨18529925715376293745639397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12353283810250862497092931 18529925715376293745639397)
                    ·
                      refine ⟨3474361071633055077307387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18529925715376293745639397 3474361071633055077307387)
                      ·
                        rfl

theorem cell23_6766294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6766294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766294 prefixEnd_6766294 := by exact prefixLift 6766294
  have htrace : WordTrace (prefixWord ++ tailWord_6766294) baseStart_6766294 baseEnd_6766294 := by
    simpa [prefixWord, tailWord_6766294, baseEnd_6766294] using wordTrace_append hprefix tailTrace_6766294
  have hstable : (prefixWord ++ tailWord_6766294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766294).length < 2 ^ (prefixWord ++ tailWord_6766294).sum := by decide
  have hdescent : baseEnd_6766294 < baseStart_6766294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766296 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_6766296 : Nat := 118140960795 + 6766296 * 2 ^ 59
def prefixEnd_6766296 : Nat := 4983230072969 + 3 ^ 40 * 6766296 * 2
def baseEnd_6766296 : Nat := 1158120699531454689827459

theorem tailTrace_6766296 : CollatzResearch.WordTrace tailWord_6766296 prefixEnd_6766296 1158120699531454689827459 := by
  unfold tailWord_6766296
  simp only [CollatzResearch.WordTrace]
  refine ⟨123393544747436329100291371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164524726329915105467055161 123393544747436329100291371)
  ·
    refine ⟨185090317121154493650437057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123393544747436329100291371 185090317121154493650437057)
    ·
      refine ⟨138817737840865870237827793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185090317121154493650437057 138817737840865870237827793)
      ·
        refine ⟨104113303380649402678370845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138817737840865870237827793 104113303380649402678370845)
        ·
          refine ⟨39042488767743526004389067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104113303380649402678370845 39042488767743526004389067)
          ·
            refine ⟨58563733151615289006583601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39042488767743526004389067 58563733151615289006583601)
            ·
              refine ⟨43922799863711466754937701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58563733151615289006583601 43922799863711466754937701)
              ·
                refine ⟨8235524974445900016550819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43922799863711466754937701 8235524974445900016550819)
                ·
                  refine ⟨12353287461668850024826229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8235524974445900016550819 12353287461668850024826229)
                  ·
                    refine ⟨1158120699531454689827459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12353287461668850024826229 1158120699531454689827459)
                    ·
                      rfl

theorem cell23_6766296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_6766296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766296 prefixEnd_6766296 := by exact prefixLift 6766296
  have htrace : WordTrace (prefixWord ++ tailWord_6766296) baseStart_6766296 baseEnd_6766296 := by
    simpa [prefixWord, tailWord_6766296, baseEnd_6766296] using wordTrace_append hprefix tailTrace_6766296
  have hstable : (prefixWord ++ tailWord_6766296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766296).length < 2 ^ (prefixWord ++ tailWord_6766296).sum := by decide
  have hdescent : baseEnd_6766296 < baseStart_6766296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766329 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6766329 : Nat := 118140960795 + 6766329 * 2 ^ 59
def prefixEnd_6766329 : Nat := 4983230072969 + 3 ^ 40 * 6766329 * 2
def baseEnd_6766329 : Nat := 3474379043455962440369725

theorem tailTrace_6766329 : CollatzResearch.WordTrace tailWord_6766329 prefixEnd_6766329 3474379043455962440369725 := by
  unfold tailWord_6766329
  simp only [CollatzResearch.WordTrace]
  refine ⟨246788293103753104836534041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164525528735835403224356027 246788293103753104836534041)
  ·
    refine ⟨185091219827814828627400531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246788293103753104836534041 185091219827814828627400531)
    ·
      refine ⟨277636829741722242941100797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185091219827814828627400531 277636829741722242941100797)
      ·
        refine ⟨104113811153145841102912799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277636829741722242941100797 104113811153145841102912799)
        ·
          refine ⟨156170716729718761654369199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104113811153145841102912799 156170716729718761654369199)
          ·
            refine ⟨234256075094578142481553799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156170716729718761654369199 234256075094578142481553799)
            ·
              refine ⟨351384112641867213722330699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234256075094578142481553799 351384112641867213722330699)
              ·
                refine ⟨527076168962800820583496049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351384112641867213722330699 527076168962800820583496049)
                ·
                  refine ⟨395307126722100615437622037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527076168962800820583496049 395307126722100615437622037)
                  ·
                    refine ⟨18530021565098466348638533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 395307126722100615437622037 18530021565098466348638533)
                    ·
                      refine ⟨3474379043455962440369725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18530021565098466348638533 3474379043455962440369725)
                      ·
                        rfl

theorem cell23_6766329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6766329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766329 prefixEnd_6766329 := by exact prefixLift 6766329
  have htrace : WordTrace (prefixWord ++ tailWord_6766329) baseStart_6766329 baseEnd_6766329 := by
    simpa [prefixWord, tailWord_6766329, baseEnd_6766329] using wordTrace_append hprefix tailTrace_6766329
  have hstable : (prefixWord ++ tailWord_6766329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766329).length < 2 ^ (prefixWord ++ tailWord_6766329).sum := by decide
  have hdescent : baseEnd_6766329 < baseStart_6766329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766346 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_6766346 : Nat := 118140960795 + 6766346 * 2 ^ 59
def prefixEnd_6766346 : Nat := 4983230072969 + 3 ^ 40 * 6766346 * 2
def baseEnd_6766346 : Nat := 3474387772627088873857147

theorem tailTrace_6766346 : CollatzResearch.WordTrace tailWord_6766346 prefixEnd_6766346 3474387772627088873857147 := by
  unfold tailWord_6766346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61697228286172879184975723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164525942096461011159935261 61697228286172879184975723)
  ·
    refine ⟨92545842429259318777463585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61697228286172879184975723 92545842429259318777463585)
    ·
      refine ⟨69409381821944489083097689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92545842429259318777463585 69409381821944489083097689)
      ·
        refine ⟨52057036366458366812323267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69409381821944489083097689 52057036366458366812323267)
        ·
          refine ⟨78085554549687550218484901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52057036366458366812323267 78085554549687550218484901)
          ·
            refine ⟨14641041478066415665965919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78085554549687550218484901 14641041478066415665965919)
            ·
              refine ⟨21961562217099623498948879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14641041478066415665965919 21961562217099623498948879)
              ·
                refine ⟨32942343325649435248423319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21961562217099623498948879 32942343325649435248423319)
                ·
                  refine ⟨49413514988474152872634979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32942343325649435248423319 49413514988474152872634979)
                  ·
                    refine ⟨74120272482711229308952469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49413514988474152872634979 74120272482711229308952469)
                    ·
                      refine ⟨3474387772627088873857147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74120272482711229308952469 3474387772627088873857147)
                      ·
                        rfl

theorem cell23_6766346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_6766346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766346 prefixEnd_6766346 := by exact prefixLift 6766346
  have htrace : WordTrace (prefixWord ++ tailWord_6766346) baseStart_6766346 baseEnd_6766346 := by
    simpa [prefixWord, tailWord_6766346, baseEnd_6766346] using wordTrace_append hprefix tailTrace_6766346
  have hstable : (prefixWord ++ tailWord_6766346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766346).length < 2 ^ (prefixWord ++ tailWord_6766346).sum := by decide
  have hdescent : baseEnd_6766346 < baseStart_6766346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766350 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6766350 : Nat := 118140960795 + 6766350 * 2 ^ 59
def prefixEnd_6766350 : Nat := 4983230072969 + 3 ^ 40 * 6766350 * 2
def baseEnd_6766350 : Nat := 3474389826549706858207129

theorem tailTrace_6766350 : CollatzResearch.WordTrace tailWord_6766350 prefixEnd_6766350 3474389826549706858207129 := by
  unfold tailWord_6766350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848632379584628177881063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164526039357784683615365669 30848632379584628177881063)
  ·
    refine ⟨46272948569376942266821595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30848632379584628177881063 46272948569376942266821595)
    ·
      refine ⟨69409422854065413400232393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46272948569376942266821595 69409422854065413400232393)
      ·
        refine ⟨52057067140549060050174295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69409422854065413400232393 52057067140549060050174295)
        ·
          refine ⟨78085600710823590075261443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52057067140549060050174295 78085600710823590075261443)
          ·
            refine ⟨117128401066235385112892165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78085600710823590075261443 117128401066235385112892165)
            ·
              refine ⟨21961575199919134708667281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117128401066235385112892165 21961575199919134708667281)
              ·
                refine ⟨16471181399939351031500461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21961575199919134708667281 16471181399939351031500461)
                ·
                  refine ⟨6176693024977256636812673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16471181399939351031500461 6176693024977256636812673)
                  ·
                    refine ⟨4632519768732942477609505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6176693024977256636812673 4632519768732942477609505)
                    ·
                      refine ⟨3474389826549706858207129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632519768732942477609505 3474389826549706858207129)
                      ·
                        rfl

theorem cell23_6766350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6766350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766350 prefixEnd_6766350 := by exact prefixLift 6766350
  have htrace : WordTrace (prefixWord ++ tailWord_6766350) baseStart_6766350 baseEnd_6766350 := by
    simpa [prefixWord, tailWord_6766350, baseEnd_6766350] using wordTrace_append hprefix tailTrace_6766350
  have hstable : (prefixWord ++ tailWord_6766350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766350).length < 2 ^ (prefixWord ++ tailWord_6766350).sum := by decide
  have hdescent : baseEnd_6766350 < baseStart_6766350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766379 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_6766379 : Nat := 118140960795 + 6766379 * 2 ^ 59
def prefixEnd_6766379 : Nat := 4983230072969 + 3 ^ 40 * 6766379 * 2
def baseEnd_6766379 : Nat := 3474404717488687244744495

theorem tailTrace_6766379 : CollatzResearch.WordTrace tailWord_6766379 prefixEnd_6766379 3474404717488687244744495 := by
  unfold tailWord_6766379
  simp only [CollatzResearch.WordTrace]
  refine ⟨246790116753571963375854191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164526744502381308917236127 246790116753571963375854191)
  ·
    refine ⟨370185175130357945063781287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246790116753571963375854191 370185175130357945063781287)
    ·
      refine ⟨555277762695536917595671931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370185175130357945063781287 555277762695536917595671931)
      ·
        refine ⟨832916644043305376393507897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555277762695536917595671931 832916644043305376393507897)
        ·
          refine ⟨624687483032479032295130923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832916644043305376393507897 624687483032479032295130923)
          ·
            refine ⟨937031224548718548442696385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624687483032479032295130923 937031224548718548442696385)
            ·
              refine ⟨702773418411538911332022289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937031224548718548442696385 702773418411538911332022289)
              ·
                refine ⟨527080063808654183499016717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702773418411538911332022289 527080063808654183499016717)
                ·
                  refine ⟨197655023928245318812131269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527080063808654183499016717 197655023928245318812131269)
                  ·
                    refine ⟨37060316986545997277274613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197655023928245318812131269 37060316986545997277274613)
                    ·
                      refine ⟨3474404717488687244744495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37060316986545997277274613 3474404717488687244744495)
                      ·
                        rfl

theorem cell23_6766379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_6766379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766379 prefixEnd_6766379 := by exact prefixLift 6766379
  have htrace : WordTrace (prefixWord ++ tailWord_6766379) baseStart_6766379 baseEnd_6766379 := by
    simpa [prefixWord, tailWord_6766379, baseEnd_6766379] using wordTrace_append hprefix tailTrace_6766379
  have hstable : (prefixWord ++ tailWord_6766379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766379).length < 2 ^ (prefixWord ++ tailWord_6766379).sum := by decide
  have hdescent : baseEnd_6766379 < baseStart_6766379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766426 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_6766426 : Nat := 118140960795 + 6766426 * 2 ^ 59
def prefixEnd_6766426 : Nat := 4983230072969 + 3 ^ 40 * 6766426 * 2
def baseEnd_6766426 : Nat := 3474428851079448560856779

theorem tailTrace_6766426 : CollatzResearch.WordTrace tailWord_6766426 prefixEnd_6766426 3474428851079448560856779 := by
  unfold tailWord_6766426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61697957746100422600703783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164527887322934460268543421 61697957746100422600703783)
  ·
    refine ⟨92546936619150633901055675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61697957746100422600703783 92546936619150633901055675)
    ·
      refine ⟨138820404928725950851583513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92546936619150633901055675 138820404928725950851583513)
      ·
        refine ⟨104115303696544463138687635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138820404928725950851583513 104115303696544463138687635)
        ·
          refine ⟨156172955544816694708031453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104115303696544463138687635 156172955544816694708031453)
          ·
            refine ⟨58564858329306260515511795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156172955544816694708031453 58564858329306260515511795)
            ·
              refine ⟨87847287493959390773267693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58564858329306260515511795 87847287493959390773267693)
              ·
                refine ⟨32942732810234771539975385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87847287493959390773267693 32942732810234771539975385)
                ·
                  refine ⟨24707049607676078654981539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32942732810234771539975385 24707049607676078654981539)
                  ·
                    refine ⟨37060574411514117982472309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24707049607676078654981539 37060574411514117982472309)
                    ·
                      refine ⟨3474428851079448560856779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37060574411514117982472309 3474428851079448560856779)
                      ·
                        rfl

theorem cell23_6766426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_6766426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766426 prefixEnd_6766426 := by exact prefixLift 6766426
  have htrace : WordTrace (prefixWord ++ tailWord_6766426) baseStart_6766426 baseEnd_6766426 := by
    simpa [prefixWord, tailWord_6766426, baseEnd_6766426] using wordTrace_append hprefix tailTrace_6766426
  have hstable : (prefixWord ++ tailWord_6766426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766426).length < 2 ^ (prefixWord ++ tailWord_6766426).sum := by decide
  have hdescent : baseEnd_6766426 < baseStart_6766426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766453 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6766453 : Nat := 118140960795 + 6766453 * 2 ^ 59
def prefixEnd_6766453 : Nat := 4983230072969 + 3 ^ 40 * 6766453 * 2
def baseEnd_6766453 : Nat := 3474442715057119955219155

theorem tailTrace_6766453 : CollatzResearch.WordTrace tailWord_6766453 prefixEnd_6766453 3474442715057119955219155 := by
  unfold tailWord_6766453
  simp only [CollatzResearch.WordTrace]
  refine ⟨246792815755303874014048013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164528543836869249342698675 246792815755303874014048013)
  ·
    refine ⟨92547305908238952755268005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246792815755303874014048013 92547305908238952755268005)
    ·
      refine ⟨17352619857794803641612751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92547305908238952755268005 17352619857794803641612751)
      ·
        refine ⟨26028929786692205462419127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17352619857794803641612751 26028929786692205462419127)
        ·
          refine ⟨39043394680038308193628691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26028929786692205462419127 39043394680038308193628691)
          ·
            refine ⟨58565092020057462290443037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39043394680038308193628691 58565092020057462290443037)
            ·
              refine ⟨21961909507521548358916139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58565092020057462290443037 21961909507521548358916139)
              ·
                refine ⟨32942864261282322538374209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21961909507521548358916139 32942864261282322538374209)
                ·
                  refine ⟨24707148195961741903780657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32942864261282322538374209 24707148195961741903780657)
                  ·
                    refine ⟨18530361146971306427835493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24707148195961741903780657 18530361146971306427835493)
                    ·
                      refine ⟨3474442715057119955219155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18530361146971306427835493 3474442715057119955219155)
                      ·
                        rfl

theorem cell23_6766453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6766453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766453 prefixEnd_6766453 := by exact prefixLift 6766453
  have htrace : WordTrace (prefixWord ++ tailWord_6766453) baseStart_6766453 baseEnd_6766453 := by
    simpa [prefixWord, tailWord_6766453, baseEnd_6766453] using wordTrace_append hprefix tailTrace_6766453
  have hstable : (prefixWord ++ tailWord_6766453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766453).length < 2 ^ (prefixWord ++ tailWord_6766453).sum := by decide
  have hdescent : baseEnd_6766453 < baseStart_6766453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766478 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6766478 : Nat := 118140960795 + 6766478 * 2 ^ 59
def prefixEnd_6766478 : Nat := 4983230072969 + 3 ^ 40 * 6766478 * 2
def baseEnd_6766478 : Nat := 3474455552073482357406541

theorem tailTrace_6766478 : CollatzResearch.WordTrace tailWord_6766478 prefixEnd_6766478 3474455552073482357406541 := by
  unfold tailWord_6766478
  simp only [CollatzResearch.WordTrace]
  refine ⟨30849215947526662910463511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164529151720142202189138725 30849215947526662910463511)
  ·
    refine ⟨46273823921289994365695267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30849215947526662910463511 46273823921289994365695267)
    ·
      refine ⟨69410735881934991548542901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46273823921289994365695267 69410735881934991548542901)
      ·
        refine ⟨6507256488931405457675897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69410735881934991548542901 6507256488931405457675897)
        ·
          refine ⟨4880442366698554093256923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6507256488931405457675897 4880442366698554093256923)
          ·
            refine ⟨7320663550047831139885385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880442366698554093256923 7320663550047831139885385)
            ·
              refine ⟨5490497662535873354914039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320663550047831139885385 5490497662535873354914039)
              ·
                refine ⟨8235746493803810032371059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490497662535873354914039 8235746493803810032371059)
                ·
                  refine ⟨12353619740705715048556589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8235746493803810032371059 12353619740705715048556589)
                  ·
                    refine ⟨4632607402764643143208721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12353619740705715048556589 4632607402764643143208721)
                    ·
                      refine ⟨3474455552073482357406541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632607402764643143208721 3474455552073482357406541)
                      ·
                        rfl

theorem cell23_6766478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6766478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766478 prefixEnd_6766478 := by exact prefixLift 6766478
  have htrace : WordTrace (prefixWord ++ tailWord_6766478) baseStart_6766478 baseEnd_6766478 := by
    simpa [prefixWord, tailWord_6766478, baseEnd_6766478] using wordTrace_append hprefix tailTrace_6766478
  have hstable : (prefixWord ++ tailWord_6766478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766478).length < 2 ^ (prefixWord ++ tailWord_6766478).sum := by decide
  have hdescent : baseEnd_6766478 < baseStart_6766478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766513 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6766513 : Nat := 118140960795 + 6766513 * 2 ^ 59
def prefixEnd_6766513 : Nat := 4983230072969 + 3 ^ 40 * 6766513 * 2
def baseEnd_6766513 : Nat := 3474473523896389720468879

theorem tailTrace_6766513 : CollatzResearch.WordTrace tailWord_6766513 prefixEnd_6766513 3474473523896389720468879 := by
  unfold tailWord_6766513
  simp only [CollatzResearch.WordTrace]
  refine ⟨246795004135086504261232193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164530002756724336174154795 246795004135086504261232193)
  ·
    refine ⟨185096253101314878195924145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246795004135086504261232193 185096253101314878195924145)
    ·
      refine ⟨138822189825986158646943109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185096253101314878195924145 138822189825986158646943109)
      ·
        refine ⟨26029160592372404746301833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138822189825986158646943109 26029160592372404746301833)
        ·
          refine ⟨19521870444279303559726375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26029160592372404746301833 19521870444279303559726375)
          ·
            refine ⟨29282805666418955339589563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19521870444279303559726375 29282805666418955339589563)
            ·
              refine ⟨43924208499628433009384345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29282805666418955339589563 43924208499628433009384345)
              ·
                refine ⟨32943156374721324757038259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43924208499628433009384345 32943156374721324757038259)
                ·
                  refine ⟨49414734562081987135557389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32943156374721324757038259 49414734562081987135557389)
                  ·
                    refine ⟨18530525460780745175834021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49414734562081987135557389 18530525460780745175834021)
                    ·
                      refine ⟨3474473523896389720468879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18530525460780745175834021 3474473523896389720468879)
                      ·
                        rfl

theorem cell23_6766513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6766513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766513 prefixEnd_6766513 := by exact prefixLift 6766513
  have htrace : WordTrace (prefixWord ++ tailWord_6766513) baseStart_6766513 baseEnd_6766513 := by
    simpa [prefixWord, tailWord_6766513, baseEnd_6766513] using wordTrace_append hprefix tailTrace_6766513
  have hstable : (prefixWord ++ tailWord_6766513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766513).length < 2 ^ (prefixWord ++ tailWord_6766513).sum := by decide
  have hdescent : baseEnd_6766513 < baseStart_6766513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766620 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6766620 : Nat := 118140960795 + 6766620 * 2 ^ 59
def prefixEnd_6766620 : Nat := 4983230072969 + 3 ^ 40 * 6766620 * 2
def baseEnd_6766620 : Nat := 3474528466326420801830887

theorem tailTrace_6766620 : CollatzResearch.WordTrace tailWord_6766620 prefixEnd_6766620 3474528466326420801830887 := by
  unfold tailWord_6766620
  simp only [CollatzResearch.WordTrace]
  refine ⟨123399453372849430767688657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164532604497132574356918209 123399453372849430767688657)
  ·
    refine ⟨92549590029637073075766493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123399453372849430767688657 92549590029637073075766493)
    ·
      refine ⟨34706096261113902403412435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92549590029637073075766493 34706096261113902403412435)
      ·
        refine ⟨52059144391670853605118653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34706096261113902403412435 52059144391670853605118653)
        ·
          refine ⟨19522179146876570101919495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52059144391670853605118653 19522179146876570101919495)
          ·
            refine ⟨29283268720314855152879243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19522179146876570101919495 29283268720314855152879243)
            ·
              refine ⟨43924903080472282729318865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29283268720314855152879243 43924903080472282729318865)
              ·
                refine ⟨32943677310354212046989149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43924903080472282729318865 32943677310354212046989149)
                ·
                  refine ⟨12353878991382829517620931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32943677310354212046989149 12353878991382829517620931)
                  ·
                    refine ⟨18530818487074244276431397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12353878991382829517620931 18530818487074244276431397)
                    ·
                      refine ⟨3474528466326420801830887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18530818487074244276431397 3474528466326420801830887)
                      ·
                        rfl

theorem cell23_6766620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6766620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766620 prefixEnd_6766620 := by exact prefixLift 6766620
  have htrace : WordTrace (prefixWord ++ tailWord_6766620) baseStart_6766620 baseEnd_6766620 := by
    simpa [prefixWord, tailWord_6766620, baseEnd_6766620] using wordTrace_append hprefix tailTrace_6766620
  have hstable : (prefixWord ++ tailWord_6766620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766620).length < 2 ^ (prefixWord ++ tailWord_6766620).sum := by decide
  have hdescent : baseEnd_6766620 < baseStart_6766620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766623 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_6766623 : Nat := 118140960795 + 6766623 * 2 ^ 59
def prefixEnd_6766623 : Nat := 4983230072969 + 3 ^ 40 * 6766623 * 2
def baseEnd_6766623 : Nat := 3474530006768384290093373

theorem tailTrace_6766623 : CollatzResearch.WordTrace tailWord_6766623 prefixEnd_6766623 3474530006768384290093373 := by
  unfold tailWord_6766623
  simp only [CollatzResearch.WordTrace]
  refine ⟨246799016164687993047736523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164532677443125328698491015 246799016164687993047736523)
  ·
    refine ⟨370198524247031989571604785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246799016164687993047736523 370198524247031989571604785)
    ·
      refine ⟨277648893185273992178703589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370198524247031989571604785 277648893185273992178703589)
      ·
        refine ⟨52059167472238873533506923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277648893185273992178703589 52059167472238873533506923)
        ·
          refine ⟨78088751208358310300260385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52059167472238873533506923 78088751208358310300260385)
          ·
            refine ⟨58566563406268732725195289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78088751208358310300260385 58566563406268732725195289)
            ·
              refine ⟨43924922554701549543896467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58566563406268732725195289 43924922554701549543896467)
              ·
                refine ⟨65887383832052324315844701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43924922554701549543896467 65887383832052324315844701)
                ·
                  refine ⟨24707768937019621618441763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65887383832052324315844701 24707768937019621618441763)
                  ·
                    refine ⟨37061653405529432427662645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24707768937019621618441763 37061653405529432427662645)
                    ·
                      refine ⟨3474530006768384290093373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37061653405529432427662645 3474530006768384290093373)
                      ·
                        rfl

theorem cell23_6766623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_6766623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766623 prefixEnd_6766623 := by exact prefixLift 6766623
  have htrace : WordTrace (prefixWord ++ tailWord_6766623) baseStart_6766623 baseEnd_6766623 := by
    simpa [prefixWord, tailWord_6766623, baseEnd_6766623] using wordTrace_append hprefix tailTrace_6766623
  have hstable : (prefixWord ++ tailWord_6766623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766623).length < 2 ^ (prefixWord ++ tailWord_6766623).sum := by decide
  have hdescent : baseEnd_6766623 < baseStart_6766623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766640 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_6766640 : Nat := 118140960795 + 6766640 * 2 ^ 59
def prefixEnd_6766640 : Nat := 4983230072969 + 3 ^ 40 * 6766640 * 2
def baseEnd_6766640 : Nat := 3474538735939510723580795

theorem tailTrace_6766640 : CollatzResearch.WordTrace tailWord_6766640 prefixEnd_6766640 3474538735939510723580795 := by
  unfold tailWord_6766640
  simp only [CollatzResearch.WordTrace]
  refine ⟨123399818102813202475552687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164533090803750936634070249 123399818102813202475552687)
  ·
    refine ⟨185099727154219803713329031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123399818102813202475552687 185099727154219803713329031)
    ·
      refine ⟨277649590731329705569993547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185099727154219803713329031 277649590731329705569993547)
      ·
        refine ⟨416474386096994558354990321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277649590731329705569993547 416474386096994558354990321)
        ·
          refine ⟨312355789572745918766242741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416474386096994558354990321 312355789572745918766242741)
          ·
            refine ⟨29283355272444929884335257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312355789572745918766242741 29283355272444929884335257)
            ·
              refine ⟨21962516454333697413251443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29283355272444929884335257 21962516454333697413251443)
              ·
                refine ⟨32943774681500546119877165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21962516454333697413251443 32943774681500546119877165)
                ·
                  refine ⟨12353915505562704794953937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32943774681500546119877165 12353915505562704794953937)
                  ·
                    refine ⟨9265436629172028596215453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12353915505562704794953937 9265436629172028596215453)
                    ·
                      refine ⟨3474538735939510723580795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9265436629172028596215453 3474538735939510723580795)
                      ·
                        rfl

theorem cell23_6766640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_6766640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766640 prefixEnd_6766640 := by exact prefixLift 6766640
  have htrace : WordTrace (prefixWord ++ tailWord_6766640) baseStart_6766640 baseEnd_6766640 := by
    simpa [prefixWord, tailWord_6766640, baseEnd_6766640] using wordTrace_append hprefix tailTrace_6766640
  have hstable : (prefixWord ++ tailWord_6766640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766640).length < 2 ^ (prefixWord ++ tailWord_6766640).sum := by decide
  have hdescent : baseEnd_6766640 < baseStart_6766640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766654 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6766654 : Nat := 118140960795 + 6766654 * 2 ^ 59
def prefixEnd_6766654 : Nat := 4983230072969 + 3 ^ 40 * 6766654 * 2
def baseEnd_6766654 : Nat := 3474545924668673668805731

theorem tailTrace_6766654 : CollatzResearch.WordTrace tailWord_6766654 prefixEnd_6766654 3474545924668673668805731 := by
  unfold tailWord_6766654
  simp only [CollatzResearch.WordTrace]
  refine ⟨30850018353446960667764377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164533431218383790228076677 30850018353446960667764377)
  ·
    refine ⟨23137513765085220500823283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30850018353446960667764377 23137513765085220500823283)
    ·
      refine ⟨34706270647627830751234925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23137513765085220500823283 34706270647627830751234925)
      ·
        refine ⟨13014851492860436531713097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34706270647627830751234925 13014851492860436531713097)
        ·
          refine ⟨9761138619645327398784823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13014851492860436531713097 9761138619645327398784823)
          ·
            refine ⟨14641707929467991098177235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9761138619645327398784823 14641707929467991098177235)
            ·
              refine ⟨21962561894201986647265853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14641707929467991098177235 21962561894201986647265853)
              ·
                refine ⟨8235960710325744992724695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21962561894201986647265853 8235960710325744992724695)
                ·
                  refine ⟨12353941065488617489087043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8235960710325744992724695 12353941065488617489087043)
                  ·
                    refine ⟨18530911598232926233630565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12353941065488617489087043 18530911598232926233630565)
                    ·
                      refine ⟨3474545924668673668805731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18530911598232926233630565 3474545924668673668805731)
                      ·
                        rfl

theorem cell23_6766654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6766654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766654 prefixEnd_6766654 := by exact prefixLift 6766654
  have htrace : WordTrace (prefixWord ++ tailWord_6766654) baseStart_6766654 baseEnd_6766654 := by
    simpa [prefixWord, tailWord_6766654, baseEnd_6766654] using wordTrace_append hprefix tailTrace_6766654
  have hstable : (prefixWord ++ tailWord_6766654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766654).length < 2 ^ (prefixWord ++ tailWord_6766654).sum := by decide
  have hdescent : baseEnd_6766654 < baseStart_6766654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766742 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6766742 : Nat := 118140960795 + 6766742 * 2 ^ 59
def prefixEnd_6766742 : Nat := 4983230072969 + 3 ^ 40 * 6766742 * 2
def baseEnd_6766742 : Nat := 3474591110966269324505327

theorem tailTrace_6766742 : CollatzResearch.WordTrace tailWord_6766742 prefixEnd_6766742 3474591110966269324505327 := by
  unfold tailWord_6766742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15425209778203554773207405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164535570967504584247545653 15425209778203554773207405)
  ·
    refine ⟨5784453666826333039952777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15425209778203554773207405 5784453666826333039952777)
    ·
      refine ⟨4338340250119749779964583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5784453666826333039952777 4338340250119749779964583)
      ·
        refine ⟨6507510375179624669946875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338340250119749779964583 6507510375179624669946875)
        ·
          refine ⟨9761265562769437004920313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507510375179624669946875 9761265562769437004920313)
          ·
            refine ⟨7320949172077077753690235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9761265562769437004920313 7320949172077077753690235)
            ·
              refine ⟨10981423758115616630535353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7320949172077077753690235 10981423758115616630535353)
              ·
                refine ⟨8236067818586712472901515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10981423758115616630535353 8236067818586712472901515)
                ·
                  refine ⟨12354101727880068709352273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236067818586712472901515 12354101727880068709352273)
                  ·
                    refine ⟨9265576295910051532014205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12354101727880068709352273 9265576295910051532014205)
                    ·
                      refine ⟨3474591110966269324505327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9265576295910051532014205 3474591110966269324505327)
                      ·
                        rfl

theorem cell23_6766742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6766742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766742 prefixEnd_6766742 := by exact prefixLift 6766742
  have htrace : WordTrace (prefixWord ++ tailWord_6766742) baseStart_6766742 baseEnd_6766742 := by
    simpa [prefixWord, tailWord_6766742, baseEnd_6766742] using wordTrace_append hprefix tailTrace_6766742
  have hstable : (prefixWord ++ tailWord_6766742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766742).length < 2 ^ (prefixWord ++ tailWord_6766742).sum := by decide
  have hdescent : baseEnd_6766742 < baseStart_6766742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766763 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 7]
def baseStart_6766763 : Nat := 118140960795 + 6766763 * 2 ^ 59
def prefixEnd_6766763 : Nat := 4983230072969 + 3 ^ 40 * 6766763 * 2
def baseEnd_6766763 : Nat := 1158200631353337914114243

theorem tailTrace_6766763 : CollatzResearch.WordTrace tailWord_6766763 prefixEnd_6766763 1158200631353337914114243 := by
  unfold tailWord_6766763
  simp only [CollatzResearch.WordTrace]
  refine ⟨246804122384180796957832943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164536081589453864638555295 246804122384180796957832943)
  ·
    refine ⟨370206183576271195436749415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246804122384180796957832943 370206183576271195436749415)
    ·
      refine ⟨555309275364406793155124123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370206183576271195436749415 555309275364406793155124123)
      ·
        refine ⟨832963913046610189732686185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555309275364406793155124123 832963913046610189732686185)
        ·
          refine ⟨624722934784957642299514639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832963913046610189732686185 624722934784957642299514639)
          ·
            refine ⟨937084402177436463449271959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624722934784957642299514639 937084402177436463449271959)
            ·
              refine ⟨1405626603266154695173907939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937084402177436463449271959 1405626603266154695173907939)
              ·
                refine ⟨2108439904899232042760861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405626603266154695173907939 2108439904899232042760861909)
                ·
                  refine ⟨49416560271075751002207701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2108439904899232042760861909 49416560271075751002207701)
                  ·
                    refine ⟨1158200631353337914114243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49416560271075751002207701 1158200631353337914114243)
                    ·
                      rfl

theorem cell23_6766763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_6766763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766763 prefixEnd_6766763 := by exact prefixLift 6766763
  have htrace : WordTrace (prefixWord ++ tailWord_6766763) baseStart_6766763 baseEnd_6766763 := by
    simpa [prefixWord, tailWord_6766763, baseEnd_6766763] using wordTrace_append hprefix tailTrace_6766763
  have hstable : (prefixWord ++ tailWord_6766763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766763).length < 2 ^ (prefixWord ++ tailWord_6766763).sum := by decide
  have hdescent : baseEnd_6766763 < baseStart_6766763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766784 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 5]
def baseStart_6766784 : Nat := 118140960795 + 6766784 * 2 ^ 59
def prefixEnd_6766784 : Nat := 4983230072969 + 3 ^ 40 * 6766784 * 2
def baseEnd_6766784 : Nat := 386068075239306462242237

theorem tailTrace_6766784 : CollatzResearch.WordTrace tailWord_6766784 prefixEnd_6766784 386068075239306462242237 := by
  unfold tailWord_6766784
  simp only [CollatzResearch.WordTrace]
  refine ⟨123402444158552358772173703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164536592211403145029564937 123402444158552358772173703)
  ·
    refine ⟨185103666237828538158260555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123402444158552358772173703 185103666237828538158260555)
    ·
      refine ⟨277655499356742807237390833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185103666237828538158260555 277655499356742807237390833)
      ·
        refine ⟨208241624517557105428043125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277655499356742807237390833 208241624517557105428043125)
        ·
          refine ⟨19522652298520978633879043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208241624517557105428043125 19522652298520978633879043)
          ·
            refine ⟨29283978447781467950818565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19522652298520978633879043 29283978447781467950818565)
            ·
              refine ⟨5490745958959025240778481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29283978447781467950818565 5490745958959025240778481)
              ·
                refine ⟨4118059469219268930583861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5490745958959025240778481 4118059469219268930583861)
                ·
                  refine ⟨386068075239306462242237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4118059469219268930583861 386068075239306462242237)
                  ·
                    rfl

theorem cell23_6766784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 5].length) (baseStart_6766784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766784 prefixEnd_6766784 := by exact prefixLift 6766784
  have htrace : WordTrace (prefixWord ++ tailWord_6766784) baseStart_6766784 baseEnd_6766784 := by
    simpa [prefixWord, tailWord_6766784, baseEnd_6766784] using wordTrace_append hprefix tailTrace_6766784
  have hstable : (prefixWord ++ tailWord_6766784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766784).length < 2 ^ (prefixWord ++ tailWord_6766784).sum := by decide
  have hdescent : baseEnd_6766784 < baseStart_6766784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766817 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_6766817 : Nat := 118140960795 + 6766817 * 2 ^ 59
def prefixEnd_6766817 : Nat := 4983230072969 + 3 ^ 40 * 6766817 * 2
def baseEnd_6766817 : Nat := 3474629622015356531067481

theorem tailTrace_6766817 : CollatzResearch.WordTrace tailWord_6766817 prefixEnd_6766817 3474629622015356531067481 := by
  unfold tailWord_6766817
  simp only [CollatzResearch.WordTrace]
  refine ⟨246806091925985164180298705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164537394617323442786865803 246806091925985164180298705)
  ·
    refine ⟨185104568944488873135224029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246806091925985164180298705 185104568944488873135224029)
    ·
      refine ⟨69414213354183327425709011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185104568944488873135224029 69414213354183327425709011)
      ·
        refine ⟨104121320031274991138563517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69414213354183327425709011 104121320031274991138563517)
        ·
          refine ⟨39045495011728121676961319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104121320031274991138563517 39045495011728121676961319)
          ·
            refine ⟨58568242517592182515441979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39045495011728121676961319 58568242517592182515441979)
            ·
              refine ⟨87852363776388273773162969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58568242517592182515441979 87852363776388273773162969)
              ·
                refine ⟨65889272832291205329872227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87852363776388273773162969 65889272832291205329872227)
                ·
                  refine ⟨98833909248436807994808341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65889272832291205329872227 98833909248436807994808341)
                  ·
                    refine ⟨4632839496020475374756641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98833909248436807994808341 4632839496020475374756641)
                    ·
                      refine ⟨3474629622015356531067481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632839496020475374756641 3474629622015356531067481)
                      ·
                        rfl

theorem cell23_6766817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_6766817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766817 prefixEnd_6766817 := by exact prefixLift 6766817
  have htrace : WordTrace (prefixWord ++ tailWord_6766817) baseStart_6766817 baseEnd_6766817 := by
    simpa [prefixWord, tailWord_6766817, baseEnd_6766817] using wordTrace_append hprefix tailTrace_6766817
  have hstable : (prefixWord ++ tailWord_6766817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766817).length < 2 ^ (prefixWord ++ tailWord_6766817).sum := by decide
  have hdescent : baseEnd_6766817 < baseStart_6766817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766834 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_6766834 : Nat := 118140960795 + 6766834 * 2 ^ 59
def prefixEnd_6766834 : Nat := 4983230072969 + 3 ^ 40 * 6766834 * 2
def baseEnd_6766834 : Nat := 3474638351186482964554903

theorem tailTrace_6766834 : CollatzResearch.WordTrace tailWord_6766834 prefixEnd_6766834 3474638351186482964554903 := by
  unfold tailWord_6766834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61701677991730894020916889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164537807977949050722445037 61701677991730894020916889)
  ·
    refine ⟨46276258493798170515687667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61701677991730894020916889 46276258493798170515687667)
    ·
      refine ⟨69414387740697255773531501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46276258493798170515687667 69414387740697255773531501)
      ·
        refine ⟨26030395402761470915074313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69414387740697255773531501 26030395402761470915074313)
        ·
          refine ⟨19522796552071103186305735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26030395402761470915074313 19522796552071103186305735)
          ·
            refine ⟨29284194828106654779458603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19522796552071103186305735 29284194828106654779458603)
            ·
              refine ⟨43926292242159982169187905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29284194828106654779458603 43926292242159982169187905)
              ·
                refine ⟨32944719181619986626890929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43926292242159982169187905 32944719181619986626890929)
                ·
                  refine ⟨24708539386214989970168197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32944719181619986626890929 24708539386214989970168197)
                  ·
                    refine ⟨4632851134915310619406537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24708539386214989970168197 4632851134915310619406537)
                    ·
                      refine ⟨3474638351186482964554903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632851134915310619406537 3474638351186482964554903)
                      ·
                        rfl

theorem cell23_6766834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_6766834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766834 prefixEnd_6766834 := by exact prefixLift 6766834
  have htrace : WordTrace (prefixWord ++ tailWord_6766834) baseStart_6766834 baseEnd_6766834 := by
    simpa [prefixWord, tailWord_6766834, baseEnd_6766834] using wordTrace_append hprefix tailTrace_6766834
  have hstable : (prefixWord ++ tailWord_6766834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766834).length < 2 ^ (prefixWord ++ tailWord_6766834).sum := by decide
  have hdescent : baseEnd_6766834 < baseStart_6766834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766844 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_6766844 : Nat := 118140960795 + 6766844 * 2 ^ 59
def prefixEnd_6766844 : Nat := 4983230072969 + 3 ^ 40 * 6766844 * 2
def baseEnd_6766844 : Nat := 1158214495331009308476619

theorem tailTrace_6766844 : CollatzResearch.WordTrace tailWord_6766844 prefixEnd_6766844 1158214495331009308476619 := by
  unfold tailWord_6766844
  simp only [CollatzResearch.WordTrace]
  refine ⟨123403538348443673895765793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164538051131258231861021057 123403538348443673895765793)
  ·
    refine ⟨92552653761332755421824345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123403538348443673895765793 92552653761332755421824345)
    ·
      refine ⟨69414490320999566566368259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92552653761332755421824345 69414490320999566566368259)
      ·
        refine ⟨104121735481499349849552389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69414490320999566566368259 104121735481499349849552389)
        ·
          refine ⟨19522825402781128096791073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104121735481499349849552389 19522825402781128096791073)
          ·
            refine ⟨14642119052085846072593305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19522825402781128096791073 14642119052085846072593305)
            ·
              refine ⟨10981589289064384554444979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14642119052085846072593305 10981589289064384554444979)
              ·
                refine ⟨16472383933596576831667469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10981589289064384554444979 16472383933596576831667469)
                ·
                  refine ⟨6177143975098716311875301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16472383933596576831667469 6177143975098716311875301)
                  ·
                    refine ⟨1158214495331009308476619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177143975098716311875301 1158214495331009308476619)
                    ·
                      rfl

theorem cell23_6766844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_6766844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766844 prefixEnd_6766844 := by exact prefixLift 6766844
  have htrace : WordTrace (prefixWord ++ tailWord_6766844) baseStart_6766844 baseEnd_6766844 := by
    simpa [prefixWord, tailWord_6766844, baseEnd_6766844] using wordTrace_append hprefix tailTrace_6766844
  have hstable : (prefixWord ++ tailWord_6766844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766844).length < 2 ^ (prefixWord ++ tailWord_6766844).sum := by decide
  have hdescent : baseEnd_6766844 < baseStart_6766844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766860 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6766860 : Nat := 118140960795 + 6766860 * 2 ^ 59
def prefixEnd_6766860 : Nat := 4983230072969 + 3 ^ 40 * 6766860 * 2
def baseEnd_6766860 : Nat := 3474651701683499862829783

theorem tailTrace_6766860 : CollatzResearch.WordTrace tailWord_6766860 prefixEnd_6766860 3474651701683499862829783 := by
  unfold tailWord_6766860
  simp only [CollatzResearch.WordTrace]
  refine ⟨123403830132414691262057017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164538440176552921682742689 123403830132414691262057017)
  ·
    refine ⟨92552872599311018446542763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123403830132414691262057017 92552872599311018446542763)
    ·
      refine ⟨138829308898966527669814145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92552872599311018446542763 138829308898966527669814145)
      ·
        refine ⟨104121981674224895752360609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138829308898966527669814145 104121981674224895752360609)
        ·
          refine ⟨78091486255668671814270457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104121981674224895752360609 78091486255668671814270457)
          ·
            refine ⟨58568614691751503860702843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78091486255668671814270457 58568614691751503860702843)
            ·
              refine ⟨87852922037627255791054265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58568614691751503860702843 87852922037627255791054265)
              ·
                refine ⟨65889691528220441843290699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87852922037627255791054265 65889691528220441843290699)
                ·
                  refine ⟨98834537292330662764936049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65889691528220441843290699 98834537292330662764936049)
                  ·
                    refine ⟨74125902969247997073702037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98834537292330662764936049 74125902969247997073702037)
                    ·
                      refine ⟨3474651701683499862829783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74125902969247997073702037 3474651701683499862829783)
                      ·
                        rfl

theorem cell23_6766860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6766860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766860 prefixEnd_6766860 := by exact prefixLift 6766860
  have htrace : WordTrace (prefixWord ++ tailWord_6766860) baseStart_6766860 baseEnd_6766860 := by
    simpa [prefixWord, tailWord_6766860, baseEnd_6766860] using wordTrace_append hprefix tailTrace_6766860
  have hstable : (prefixWord ++ tailWord_6766860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766860).length < 2 ^ (prefixWord ++ tailWord_6766860).sum := by decide
  have hdescent : baseEnd_6766860 < baseStart_6766860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766951 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 2, 4]
def baseStart_6766951 : Nat := 118140960795 + 6766951 * 2 ^ 59
def prefixEnd_6766951 : Nat := 4983230072969 + 3 ^ 40 * 6766951 * 2
def baseEnd_6766951 : Nat := 1158232809474353002263955

theorem tailTrace_6766951 : CollatzResearch.WordTrace tailWord_6766951 prefixEnd_6766951 1158232809474353002263955 := by
  unfold tailWord_6766951
  simp only [CollatzResearch.WordTrace]
  refine ⟨246810979307499705065676707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164540652871666470043784471 246810979307499705065676707)
  ·
    refine ⟨370216468961249557598515061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246810979307499705065676707 370216468961249557598515061)
    ·
      refine ⟨34707793965117146024860787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 370216468961249557598515061 34707793965117146024860787)
      ·
        refine ⟨52061690947675719037291181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34707793965117146024860787 52061690947675719037291181)
        ·
          refine ⟨19523134105378394638984193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52061690947675719037291181 19523134105378394638984193)
          ·
            refine ⟨14642350579033795979238145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19523134105378394638984193 14642350579033795979238145)
            ·
              refine ⟨10981762934275346984428609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14642350579033795979238145 10981762934275346984428609)
              ·
                refine ⟨8236322200706510238321457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10981762934275346984428609 8236322200706510238321457)
                ·
                  refine ⟨6177241650529882678741093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236322200706510238321457 6177241650529882678741093)
                  ·
                    refine ⟨1158232809474353002263955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177241650529882678741093 1158232809474353002263955)
                    ·
                      rfl

theorem cell23_6766951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_6766951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766951 prefixEnd_6766951 := by exact prefixLift 6766951
  have htrace : WordTrace (prefixWord ++ tailWord_6766951) baseStart_6766951 baseEnd_6766951 := by
    simpa [prefixWord, tailWord_6766951, baseEnd_6766951] using wordTrace_append hprefix tailTrace_6766951
  have hstable : (prefixWord ++ tailWord_6766951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766951).length < 2 ^ (prefixWord ++ tailWord_6766951).sum := by decide
  have hdescent : baseEnd_6766951 < baseStart_6766951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6766998 : List Nat := [5, 3, 1, 2, 1, 1, 10]
def baseStart_6766998 : Nat := 118140960795 + 6766998 * 2 ^ 59
def prefixEnd_6766998 : Nat := 4983230072969 + 3 ^ 40 * 6766998 * 2
def baseEnd_6766998 : Nat := 42897809407578028677829

theorem tailTrace_6766998 : CollatzResearch.WordTrace tailWord_6766998 prefixEnd_6766998 42897809407578028677829 := by
  unfold tailWord_6766998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15425793346145589505789853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164541795692219621395091765 15425793346145589505789853)
  ·
    refine ⟨5784672504804596064671195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15425793346145589505789853 5784672504804596064671195)
    ·
      refine ⟨8677008757206894097006793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5784672504804596064671195 8677008757206894097006793)
      ·
        refine ⟨6507756567905170572755095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8677008757206894097006793 6507756567905170572755095)
        ·
          refine ⟨9761634851857755859132643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507756567905170572755095 9761634851857755859132643)
          ·
            refine ⟨14642452277786633788698965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9761634851857755859132643 14642452277786633788698965)
            ·
              refine ⟨42897809407578028677829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14642452277786633788698965 42897809407578028677829)
              ·
                rfl

theorem cell23_6766998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 10].length) (baseStart_6766998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6766998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6766998 prefixEnd_6766998 := by exact prefixLift 6766998
  have htrace : WordTrace (prefixWord ++ tailWord_6766998) baseStart_6766998 baseEnd_6766998 := by
    simpa [prefixWord, tailWord_6766998, baseEnd_6766998] using wordTrace_append hprefix tailTrace_6766998
  have hstable : (prefixWord ++ tailWord_6766998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6766998).length < 2 ^ (prefixWord ++ tailWord_6766998).sum := by decide
  have hdescent : baseEnd_6766998 < baseStart_6766998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6766998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767001 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 1, 3, 2]
def baseStart_6767001 : Nat := 118140960795 + 6767001 * 2 ^ 59
def prefixEnd_6767001 : Nat := 4983230072969 + 3 ^ 40 * 6767001 * 2
def baseEnd_6767001 : Nat := 3474724102455783811166635

theorem tailTrace_6767001 : CollatzResearch.WordTrace tailWord_6767001 prefixEnd_6767001 3474724102455783811166635 := by
  unfold tailWord_6767001
  simp only [CollatzResearch.WordTrace]
  refine ⟨246812802957318563604996857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164541868638212375736664571 246812802957318563604996857)
  ·
    refine ⟨185109602217988922703747643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246812802957318563604996857 185109602217988922703747643)
    ·
      refine ⟨277664403326983384055621465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185109602217988922703747643 277664403326983384055621465)
      ·
        refine ⟨208248302495237538041716099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277664403326983384055621465 208248302495237538041716099)
        ·
          refine ⟨312372453742856307062574149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208248302495237538041716099 312372453742856307062574149)
          ·
            refine ⟨58569835076785557574232653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312372453742856307062574149 58569835076785557574232653)
            ·
              refine ⟨21963688153794584090337245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58569835076785557574232653 21963688153794584090337245)
              ·
                refine ⟨8236383057672969033876467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21963688153794584090337245 8236383057672969033876467)
                ·
                  refine ⟨12354574586509453550814701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8236383057672969033876467 12354574586509453550814701)
                  ·
                    refine ⟨4632965469941045081555513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12354574586509453550814701 4632965469941045081555513)
                    ·
                      refine ⟨3474724102455783811166635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632965469941045081555513 3474724102455783811166635)
                      ·
                        rfl

theorem cell23_6767001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_6767001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767001 prefixEnd_6767001 := by exact prefixLift 6767001
  have htrace : WordTrace (prefixWord ++ tailWord_6767001) baseStart_6767001 baseEnd_6767001 := by
    simpa [prefixWord, tailWord_6767001, baseEnd_6767001] using wordTrace_append hprefix tailTrace_6767001
  have hstable : (prefixWord ++ tailWord_6767001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767001).length < 2 ^ (prefixWord ++ tailWord_6767001).sum := by decide
  have hdescent : baseEnd_6767001 < baseStart_6767001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767007 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 4, 6]
def baseStart_6767007 : Nat := 118140960795 + 6767007 * 2 ^ 59
def prefixEnd_6767007 : Nat := 4983230072969 + 3 ^ 40 * 6767007 * 2
def baseEnd_6767007 : Nat := 1158242394446570262563869

theorem tailTrace_6767007 : CollatzResearch.WordTrace tailWord_6767007 prefixEnd_6767007 1158242394446570262563869 := by
  unfold tailWord_6767007
  simp only [CollatzResearch.WordTrace]
  refine ⟨246813021795296826629715275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164542014530197884419810183 246813021795296826629715275)
  ·
    refine ⟨370219532692945239944572913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246813021795296826629715275 370219532692945239944572913)
    ·
      refine ⟨277664649519708929958429685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370219532692945239944572913 277664649519708929958429685)
      ·
        refine ⟨26031060892472712183602783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277664649519708929958429685 26031060892472712183602783)
        ·
          refine ⟨39046591338709068275404175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26031060892472712183602783 39046591338709068275404175)
          ·
            refine ⟨58569887008063602413106263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39046591338709068275404175 58569887008063602413106263)
            ·
              refine ⟨87854830512095403619659395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58569887008063602413106263 87854830512095403619659395)
              ·
                refine ⟨131782245768143105429489093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87854830512095403619659395 131782245768143105429489093)
                ·
                  refine ⟨24709171081526832268029205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131782245768143105429489093 24709171081526832268029205)
                  ·
                    refine ⟨1158242394446570262563869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24709171081526832268029205 1158242394446570262563869)
                    ·
                      rfl

theorem cell23_6767007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_6767007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767007 prefixEnd_6767007 := by exact prefixLift 6767007
  have htrace : WordTrace (prefixWord ++ tailWord_6767007) baseStart_6767007 baseEnd_6767007 := by
    simpa [prefixWord, tailWord_6767007, baseEnd_6767007] using wordTrace_append hprefix tailTrace_6767007
  have hstable : (prefixWord ++ tailWord_6767007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767007).length < 2 ^ (prefixWord ++ tailWord_6767007).sum := by decide
  have hdescent : baseEnd_6767007 < baseStart_6767007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767008 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3]
def baseStart_6767008 : Nat := 118140960795 + 6767008 * 2 ^ 59
def prefixEnd_6767008 : Nat := 4983230072969 + 3 ^ 40 * 6767008 * 2
def baseEnd_6767008 : Nat := 3474727696820365283779103

theorem tailTrace_6767008 : CollatzResearch.WordTrace tailWord_6767008 prefixEnd_6767008 3474727696820365283779103 := by
  unfold tailWord_6767008
  simp only [CollatzResearch.WordTrace]
  refine ⟨123406529134146601900250839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164542038845528802533667785 123406529134146601900250839)
  ·
    refine ⟨185109793701219902850376259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123406529134146601900250839 185109793701219902850376259)
    ·
      refine ⟨277664690551829854275564389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185109793701219902850376259 277664690551829854275564389)
      ·
        refine ⟨52062129478468097676668323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277664690551829854275564389 52062129478468097676668323)
        ·
          refine ⟨78093194217702146515002485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52062129478468097676668323 78093194217702146515002485)
          ·
            refine ⟨7321236957909576235781483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78093194217702146515002485 7321236957909576235781483)
            ·
              refine ⟨10981855436864364353672225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321236957909576235781483 10981855436864364353672225)
              ·
                refine ⟨8236391577648273265254169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10981855436864364353672225 8236391577648273265254169)
                ·
                  refine ⟨6177293683236204948940627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236391577648273265254169 6177293683236204948940627)
                  ·
                    refine ⟨9265940524854307423410941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177293683236204948940627 9265940524854307423410941)
                    ·
                      refine ⟨3474727696820365283779103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9265940524854307423410941 3474727696820365283779103)
                      ·
                        rfl

theorem cell23_6767008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_6767008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767008 prefixEnd_6767008 := by exact prefixLift 6767008
  have htrace : WordTrace (prefixWord ++ tailWord_6767008) baseStart_6767008 baseEnd_6767008 := by
    simpa [prefixWord, tailWord_6767008, baseEnd_6767008] using wordTrace_append hprefix tailTrace_6767008
  have hstable : (prefixWord ++ tailWord_6767008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767008).length < 2 ^ (prefixWord ++ tailWord_6767008).sum := by decide
  have hdescent : baseEnd_6767008 < baseStart_6767008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767017 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_6767017 : Nat := 118140960795 + 6767017 * 2 ^ 59
def prefixEnd_6767017 : Nat := 4983230072969 + 3 ^ 40 * 6767017 * 2
def baseEnd_6767017 : Nat := 3474732318146255748566561

theorem tailTrace_6767017 : CollatzResearch.WordTrace tailWord_6767017 prefixEnd_6767017 3474732318146255748566561 := by
  unfold tailWord_6767017
  simp only [CollatzResearch.WordTrace]
  refine ⟨246813386525260598337579305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164542257683507065558386203 246813386525260598337579305)
  ·
    refine ⟨185110039893945448753184479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246813386525260598337579305 185110039893945448753184479)
    ·
      refine ⟨277665059840918173129776719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185110039893945448753184479 277665059840918173129776719)
      ·
        refine ⟨416497589761377259694665079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277665059840918173129776719 416497589761377259694665079)
        ·
          refine ⟨624746384642065889541997619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416497589761377259694665079 624746384642065889541997619)
          ·
            refine ⟨937119576963098834312996429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624746384642065889541997619 937119576963098834312996429)
            ·
              refine ⟨351419841361162062867373661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937119576963098834312996429 351419841361162062867373661)
              ·
                refine ⟨131782440510435773575265123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351419841361162062867373661 131782440510435773575265123)
                ·
                  refine ⟨197673660765653660362897685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131782440510435773575265123 197673660765653660362897685)
                  ·
                    refine ⟨9265952848390015329510829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197673660765653660362897685 9265952848390015329510829)
                    ·
                      refine ⟨3474732318146255748566561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9265952848390015329510829 3474732318146255748566561)
                      ·
                        rfl

theorem cell23_6767017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_6767017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767017 prefixEnd_6767017 := by exact prefixLift 6767017
  have htrace : WordTrace (prefixWord ++ tailWord_6767017) baseStart_6767017 baseEnd_6767017 := by
    simpa [prefixWord, tailWord_6767017, baseEnd_6767017] using wordTrace_append hprefix tailTrace_6767017
  have hstable : (prefixWord ++ tailWord_6767017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767017).length < 2 ^ (prefixWord ++ tailWord_6767017).sum := by decide
  have hdescent : baseEnd_6767017 < baseStart_6767017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767031 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_6767031 : Nat := 118140960795 + 6767031 * 2 ^ 59
def prefixEnd_6767031 : Nat := 4983230072969 + 3 ^ 40 * 6767031 * 2
def baseEnd_6767031 : Nat := 3474739506875418693791497

theorem tailTrace_6767031 : CollatzResearch.WordTrace tailWord_6767031 prefixEnd_6767031 3474739506875418693791497 := by
  unfold tailWord_6767031
  simp only [CollatzResearch.WordTrace]
  refine ⟨246813897147209878728588947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164542598098139919152392631 246813897147209878728588947)
  ·
    refine ⟨370220845720814818092883421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246813897147209878728588947 370220845720814818092883421)
    ·
      refine ⟨138832817145305556784831283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370220845720814818092883421 138832817145305556784831283)
      ·
        refine ⟨208249225717958335177246925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138832817145305556784831283 208249225717958335177246925)
        ·
          refine ⟨78093459644234375691467597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208249225717958335177246925 78093459644234375691467597)
          ·
            refine ⟨29285047366587890884300349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78093459644234375691467597 29285047366587890884300349)
            ·
              refine ⟨10981892762470459081612631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29285047366587890884300349 10981892762470459081612631)
              ·
                refine ⟨16472839143705688622418947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10981892762470459081612631 16472839143705688622418947)
                ·
                  refine ⟨24709258715558532933628421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16472839143705688622418947 24709258715558532933628421)
                  ·
                    refine ⟨4632986009167224925055329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24709258715558532933628421 4632986009167224925055329)
                    ·
                      refine ⟨3474739506875418693791497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4632986009167224925055329 3474739506875418693791497)
                      ·
                        rfl

theorem cell23_6767031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_6767031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767031 prefixEnd_6767031 := by exact prefixLift 6767031
  have htrace : WordTrace (prefixWord ++ tailWord_6767031) baseStart_6767031 baseEnd_6767031 := by
    simpa [prefixWord, tailWord_6767031, baseEnd_6767031] using wordTrace_append hprefix tailTrace_6767031
  have hstable : (prefixWord ++ tailWord_6767031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767031).length < 2 ^ (prefixWord ++ tailWord_6767031).sum := by decide
  have hdescent : baseEnd_6767031 < baseStart_6767031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767082 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_6767082 : Nat := 118140960795 + 6767082 * 2 ^ 59
def prefixEnd_6767082 : Nat := 4983230072969 + 3 ^ 40 * 6767082 * 2
def baseEnd_6767082 : Nat := 3474765694388797994253763

theorem tailTrace_6767082 : CollatzResearch.WordTrace tailWord_6767082 prefixEnd_6767082 3474765694388797994253763 := by
  unfold tailWord_6767082
  simp only [CollatzResearch.WordTrace]
  refine ⟨61703939317506278609673875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164543838180016742959130333 61703939317506278609673875)
  ·
    refine ⟨92555908976259417914510813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61703939317506278609673875 92555908976259417914510813)
    ·
      refine ⟨34708465866097281717941555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92555908976259417914510813 34708465866097281717941555)
      ·
        refine ⟨52062698799145922576912333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34708465866097281717941555 52062698799145922576912333)
        ·
          refine ⟨19523512049679720966342125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52062698799145922576912333 19523512049679720966342125)
          ·
            refine ⟨7321317018629895362378297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19523512049679720966342125 7321317018629895362378297)
            ·
              refine ⟨5490987763972421521783723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7321317018629895362378297 5490987763972421521783723)
              ·
                refine ⟨8236481645958632282675585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490987763972421521783723 8236481645958632282675585)
                ·
                  refine ⟨6177361234468974212006689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236481645958632282675585 6177361234468974212006689)
                  ·
                    refine ⟨4633020925851730659005017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177361234468974212006689 4633020925851730659005017)
                    ·
                      refine ⟨3474765694388797994253763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633020925851730659005017 3474765694388797994253763)
                      ·
                        rfl

theorem cell23_6767082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_6767082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767082 prefixEnd_6767082 := by exact prefixLift 6767082
  have htrace : WordTrace (prefixWord ++ tailWord_6767082) baseStart_6767082 baseEnd_6767082 := by
    simpa [prefixWord, tailWord_6767082, baseEnd_6767082] using wordTrace_append hprefix tailTrace_6767082
  have hstable : (prefixWord ++ tailWord_6767082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767082).length < 2 ^ (prefixWord ++ tailWord_6767082).sum := by decide
  have hdescent : baseEnd_6767082 < baseStart_6767082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767094 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6767094 : Nat := 118140960795 + 6767094 * 2 ^ 59
def prefixEnd_6767094 : Nat := 4983230072969 + 3 ^ 40 * 6767094 * 2
def baseEnd_6767094 : Nat := 3474771856156651947303707

theorem tailTrace_6767094 : CollatzResearch.WordTrace tailWord_6767094 prefixEnd_6767094 3474771856156651947303707 := by
  unfold tailWord_6767094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426012184123852530508271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164544129963987760325421557 15426012184123852530508271)
  ·
    refine ⟨23139018276185778795762407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15426012184123852530508271 23139018276185778795762407)
    ·
      refine ⟨34708527414278668193643611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139018276185778795762407 34708527414278668193643611)
      ·
        refine ⟨52062791121418002290465417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34708527414278668193643611 52062791121418002290465417)
        ·
          refine ⟨39047093341063501717849063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52062791121418002290465417 39047093341063501717849063)
          ·
            refine ⟨58570640011595252576773595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39047093341063501717849063 58570640011595252576773595)
            ·
              refine ⟨87855960017392878865160393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58570640011595252576773595 87855960017392878865160393)
              ·
                refine ⟨65891970013044659148870295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87855960017392878865160393 65891970013044659148870295)
                ·
                  refine ⟨98837955019566988723305443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65891970013044659148870295 98837955019566988723305443)
                  ·
                    refine ⟨148256932529350483084958165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98837955019566988723305443 148256932529350483084958165)
                    ·
                      refine ⟨3474771856156651947303707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148256932529350483084958165 3474771856156651947303707)
                      ·
                        rfl

theorem cell23_6767094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6767094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767094 prefixEnd_6767094 := by exact prefixLift 6767094
  have htrace : WordTrace (prefixWord ++ tailWord_6767094) baseStart_6767094 baseEnd_6767094 := by
    simpa [prefixWord, tailWord_6767094, baseEnd_6767094] using wordTrace_append hprefix tailTrace_6767094
  have hstable : (prefixWord ++ tailWord_6767094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767094).length < 2 ^ (prefixWord ++ tailWord_6767094).sum := by decide
  have hdescent : baseEnd_6767094 < baseStart_6767094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767097 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_6767097 : Nat := 118140960795 + 6767097 * 2 ^ 59
def prefixEnd_6767097 : Nat := 4983230072969 + 3 ^ 40 * 6767097 * 2
def baseEnd_6767097 : Nat := 1158257798866205145188731

theorem tailTrace_6767097 : CollatzResearch.WordTrace tailWord_6767097 prefixEnd_6767097 1158257798866205145188731 := by
  unfold tailWord_6767097
  simp only [CollatzResearch.WordTrace]
  refine ⟨246816304364970772000491545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164544202909980514666994363 246816304364970772000491545)
  ·
    refine ⟨185112228273728079000368659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246816304364970772000491545 185112228273728079000368659)
    ·
      refine ⟨277668342410592118500552989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185112228273728079000368659 277668342410592118500552989)
      ·
        refine ⟨104125628403972044437707371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277668342410592118500552989 104125628403972044437707371)
        ·
          refine ⟨156188442605958066656561057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104125628403972044437707371 156188442605958066656561057)
          ·
            refine ⟨117141331954468549992420793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156188442605958066656561057 117141331954468549992420793)
            ·
              refine ⟨87855998965851412494315595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117141331954468549992420793 87855998965851412494315595)
              ·
                refine ⟨131783998448777118741473393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87855998965851412494315595 131783998448777118741473393)
                ·
                  refine ⟨98837998836582839056105045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131783998448777118741473393 98837998836582839056105045)
                  ·
                    refine ⟨1158257798866205145188731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98837998836582839056105045 1158257798866205145188731)
                    ·
                      rfl

theorem cell23_6767097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_6767097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767097 prefixEnd_6767097 := by exact prefixLift 6767097
  have htrace : WordTrace (prefixWord ++ tailWord_6767097) baseStart_6767097 baseEnd_6767097 := by
    simpa [prefixWord, tailWord_6767097, baseEnd_6767097] using wordTrace_append hprefix tailTrace_6767097
  have hstable : (prefixWord ++ tailWord_6767097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767097).length < 2 ^ (prefixWord ++ tailWord_6767097).sum := by decide
  have hdescent : baseEnd_6767097 < baseStart_6767097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767158 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_6767158 : Nat := 118140960795 + 6767158 * 2 ^ 59
def prefixEnd_6767158 : Nat := 4983230072969 + 3 ^ 40 * 6767158 * 2
def baseEnd_6767158 : Nat := 3474804718918539696903413

theorem tailTrace_6767158 : CollatzResearch.WordTrace tailWord_6767158 prefixEnd_6767158 3474804718918539696903413 := by
  unfold tailWord_6767158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426158076109361213653883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164545686145166519612308085 15426158076109361213653883)
  ·
    refine ⟨23139237114164041820480825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15426158076109361213653883 23139237114164041820480825)
    ·
      refine ⟨17354427835623031365360619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23139237114164041820480825 17354427835623031365360619)
      ·
        refine ⟨26031641753434547048040929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17354427835623031365360619 26031641753434547048040929)
        ·
          refine ⟨19523731315075910286030697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26031641753434547048040929 19523731315075910286030697)
          ·
            refine ⟨14642798486306932714523023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19523731315075910286030697 14642798486306932714523023)
            ·
              refine ⟨21964197729460399071784535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14642798486306932714523023 21964197729460399071784535)
              ·
                refine ⟨32946296594190598607676803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21964197729460399071784535 32946296594190598607676803)
                ·
                  refine ⟨49419444891285897911515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32946296594190598607676803 49419444891285897911515205)
                  ·
                    refine ⟨9266145917116105858409101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49419444891285897911515205 9266145917116105858409101)
                    ·
                      refine ⟨3474804718918539696903413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266145917116105858409101 3474804718918539696903413)
                      ·
                        rfl

theorem cell23_6767158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_6767158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767158 prefixEnd_6767158 := by exact prefixLift 6767158
  have htrace : WordTrace (prefixWord ++ tailWord_6767158) baseStart_6767158 baseEnd_6767158 := by
    simpa [prefixWord, tailWord_6767158, baseEnd_6767158] using wordTrace_append hprefix tailTrace_6767158
  have hstable : (prefixWord ++ tailWord_6767158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767158).length < 2 ^ (prefixWord ++ tailWord_6767158).sum := by decide
  have hdescent : baseEnd_6767158 < baseStart_6767158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767165 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_6767165 : Nat := 118140960795 + 6767165 * 2 ^ 59
def prefixEnd_6767165 : Nat := 4983230072969 + 3 ^ 40 * 6767165 * 2
def baseEnd_6767165 : Nat := 1158269437761040389838627

theorem tailTrace_6767165 : CollatzResearch.WordTrace tailWord_6767165 prefixEnd_6767165 1158269437761040389838627 := by
  unfold tailWord_6767165
  simp only [CollatzResearch.WordTrace]
  refine ⟨246818784528724419613966949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164545856352482946409311299 246818784528724419613966949)
  ·
    refine ⟨46278522099135828677618803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246818784528724419613966949 46278522099135828677618803)
    ·
      refine ⟨69417783148703743016428205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46278522099135828677618803 69417783148703743016428205)
      ·
        refine ⟨26031668680763903631160577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69417783148703743016428205 26031668680763903631160577)
        ·
          refine ⟨19523751510572927723370433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26031668680763903631160577 19523751510572927723370433)
          ·
            refine ⟨14642813632929695792527825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19523751510572927723370433 14642813632929695792527825)
            ·
              refine ⟨10982110224697271844395869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14642813632929695792527825 10982110224697271844395869)
              ·
                refine ⟨4118291334261476941648451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10982110224697271844395869 4118291334261476941648451)
                ·
                  refine ⟨6177437001392215412472677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118291334261476941648451 6177437001392215412472677)
                  ·
                    refine ⟨1158269437761040389838627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177437001392215412472677 1158269437761040389838627)
                    ·
                      rfl

theorem cell23_6767165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_6767165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767165 prefixEnd_6767165 := by exact prefixLift 6767165
  have htrace : WordTrace (prefixWord ++ tailWord_6767165) baseStart_6767165 baseEnd_6767165 := by
    simpa [prefixWord, tailWord_6767165, baseEnd_6767165] using wordTrace_append hprefix tailTrace_6767165
  have hstable : (prefixWord ++ tailWord_6767165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767165).length < 2 ^ (prefixWord ++ tailWord_6767165).sum := by decide
  have hdescent : baseEnd_6767165 < baseStart_6767165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767181 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6767181 : Nat := 118140960795 + 6767181 * 2 ^ 59
def prefixEnd_6767181 : Nat := 4983230072969 + 3 ^ 40 * 6767181 * 2
def baseEnd_6767181 : Nat := 3474816528973593106915807

theorem tailTrace_6767181 : CollatzResearch.WordTrace tailWord_6767181 prefixEnd_6767181 3474816528973593106915807 := by
  unfold tailWord_6767181
  simp only [CollatzResearch.WordTrace]
  refine ⟨246819368096666454346549397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164546245397777636231032931 246819368096666454346549397)
  ·
    refine ⟨11569657879531240047494503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246819368096666454346549397 11569657879531240047494503)
    ·
      refine ⟨17354486819296860071241755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11569657879531240047494503 17354486819296860071241755)
      ·
        refine ⟨26031730228945290106862633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17354486819296860071241755 26031730228945290106862633)
        ·
          refine ⟨19523797671708967580146975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26031730228945290106862633 19523797671708967580146975)
          ·
            refine ⟨29285696507563451370220463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19523797671708967580146975 29285696507563451370220463)
            ·
              refine ⟨43928544761345177055330695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29285696507563451370220463 43928544761345177055330695)
              ·
                refine ⟨65892817142017765582996043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43928544761345177055330695 65892817142017765582996043)
                ·
                  refine ⟨98839225713026648374494065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65892817142017765582996043 98839225713026648374494065)
                  ·
                    refine ⟨74129419284769986280870549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98839225713026648374494065 74129419284769986280870549)
                    ·
                      refine ⟨3474816528973593106915807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74129419284769986280870549 3474816528973593106915807)
                      ·
                        rfl

theorem cell23_6767181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6767181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767181 prefixEnd_6767181 := by exact prefixLift 6767181
  have htrace : WordTrace (prefixWord ++ tailWord_6767181) baseStart_6767181 baseEnd_6767181 := by
    simpa [prefixWord, tailWord_6767181, baseEnd_6767181] using wordTrace_append hprefix tailTrace_6767181
  have hstable : (prefixWord ++ tailWord_6767181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767181).length < 2 ^ (prefixWord ++ tailWord_6767181).sum := by decide
  have hdescent : baseEnd_6767181 < baseStart_6767181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767188 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_6767188 : Nat := 118140960795 + 6767188 * 2 ^ 59
def prefixEnd_6767188 : Nat := 4983230072969 + 3 ^ 40 * 6767188 * 2
def baseEnd_6767188 : Nat := 3474820123338174579528275

theorem tailTrace_6767188 : CollatzResearch.WordTrace tailWord_6767188 prefixEnd_6767188 3474820123338174579528275 := by
  unfold tailWord_6767188
  simp only [CollatzResearch.WordTrace]
  refine ⟨123409811703820547271027109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164546415605094063028036145 123409811703820547271027109)
  ·
    refine ⟨23139339694466352613317583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123409811703820547271027109 23139339694466352613317583)
    ·
      refine ⟨34709009541699528919976375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139339694466352613317583 34709009541699528919976375)
      ·
        refine ⟨52063514312549293379964563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34709009541699528919976375 52063514312549293379964563)
        ·
          refine ⟨78095271468823940069946845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52063514312549293379964563 78095271468823940069946845)
          ·
            refine ⟨29285726800808977526230067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78095271468823940069946845 29285726800808977526230067)
            ·
              refine ⟨43928590201213466289345101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29285726800808977526230067 43928590201213466289345101)
              ·
                refine ⟨16473221325455049858504413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43928590201213466289345101 16473221325455049858504413)
                ·
                  refine ⟨6177457997045643696939155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16473221325455049858504413 6177457997045643696939155)
                  ·
                    refine ⟨9266186995568465545408733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177457997045643696939155 9266186995568465545408733)
                    ·
                      refine ⟨3474820123338174579528275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266186995568465545408733 3474820123338174579528275)
                      ·
                        rfl

theorem cell23_6767188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_6767188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767188 prefixEnd_6767188 := by exact prefixLift 6767188
  have htrace : WordTrace (prefixWord ++ tailWord_6767188) baseStart_6767188 baseEnd_6767188 := by
    simpa [prefixWord, tailWord_6767188, baseEnd_6767188] using wordTrace_append hprefix tailTrace_6767188
  have hstable : (prefixWord ++ tailWord_6767188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767188).length < 2 ^ (prefixWord ++ tailWord_6767188).sum := by decide
  have hdescent : baseEnd_6767188 < baseStart_6767188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767228 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_6767228 : Nat := 118140960795 + 6767228 * 2 ^ 59
def prefixEnd_6767228 : Nat := 4983230072969 + 3 ^ 40 * 6767228 * 2
def baseEnd_6767228 : Nat := 3474840662564354423028091

theorem tailTrace_6767228 : CollatzResearch.WordTrace tailWord_6767228 prefixEnd_6767228 3474840662564354423028091 := by
  unfold tailWord_6767228
  simp only [CollatzResearch.WordTrace]
  refine ⟨123410541163748090686755169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164547388218330787582340225 123410541163748090686755169)
  ·
    refine ⟨92557905872811068015066377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123410541163748090686755169 92557905872811068015066377)
    ·
      refine ⟨69418429404608301011299783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92557905872811068015066377 69418429404608301011299783)
      ·
        refine ⟨104127644106912451516949675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69418429404608301011299783 104127644106912451516949675)
        ·
          refine ⟨156191466160368677275424513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104127644106912451516949675 156191466160368677275424513)
          ·
            refine ⟨117143599620276507956568385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156191466160368677275424513 117143599620276507956568385)
            ·
              refine ⟨87857699715207380967426289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117143599620276507956568385 87857699715207380967426289)
              ·
                refine ⟨65893274786405535725569717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87857699715207380967426289 65893274786405535725569717)
                ·
                  refine ⟨6177494511225518974272161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65893274786405535725569717 6177494511225518974272161)
                  ·
                    refine ⟨4633120883419139230704121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177494511225518974272161 4633120883419139230704121)
                    ·
                      refine ⟨3474840662564354423028091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633120883419139230704121 3474840662564354423028091)
                      ·
                        rfl

theorem cell23_6767228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_6767228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767228 prefixEnd_6767228 := by exact prefixLift 6767228
  have htrace : WordTrace (prefixWord ++ tailWord_6767228) baseStart_6767228 baseEnd_6767228 := by
    simpa [prefixWord, tailWord_6767228, baseEnd_6767228] using wordTrace_append hprefix tailTrace_6767228
  have hstable : (prefixWord ++ tailWord_6767228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767228).length < 2 ^ (prefixWord ++ tailWord_6767228).sum := by decide
  have hdescent : baseEnd_6767228 < baseStart_6767228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767295 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 3]
def baseStart_6767295 : Nat := 118140960795 + 6767295 * 2 ^ 59
def prefixEnd_6767295 : Nat := 4983230072969 + 3 ^ 40 * 6767295 * 2
def baseEnd_6767295 : Nat := 3474875065768205660890283

theorem tailTrace_6767295 : CollatzResearch.WordTrace tailWord_6767295 prefixEnd_6767295 3474875065768205660890283 := by
  unfold tailWord_6767295
  simp only [CollatzResearch.WordTrace]
  refine ⟨246823526018253451816199339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164549017345502301210799559 246823526018253451816199339)
  ·
    refine ⟨370235289027380177724299009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246823526018253451816199339 370235289027380177724299009)
    ·
      refine ⟨277676466770535133293224257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370235289027380177724299009 277676466770535133293224257)
      ·
        refine ⟨208257350077901349969918193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277676466770535133293224257 208257350077901349969918193)
        ·
          refine ⟨156193012558426012477438645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208257350077901349969918193 156193012558426012477438645)
          ·
            refine ⟨14643094927352438669759873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156193012558426012477438645 14643094927352438669759873)
            ·
              refine ⟨10982321195514329002319905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643094927352438669759873 10982321195514329002319905)
              ·
                refine ⟨8236740896635746751739929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10982321195514329002319905 8236740896635746751739929)
                ·
                  refine ⟨6177555672476810063804947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236740896635746751739929 6177555672476810063804947)
                  ·
                    refine ⟨9266333508715215095707421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177555672476810063804947 9266333508715215095707421)
                    ·
                      refine ⟨3474875065768205660890283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266333508715215095707421 3474875065768205660890283)
                      ·
                        rfl

theorem cell23_6767295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_6767295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767295 prefixEnd_6767295 := by exact prefixLift 6767295
  have htrace : WordTrace (prefixWord ++ tailWord_6767295) baseStart_6767295 baseEnd_6767295 := by
    simpa [prefixWord, tailWord_6767295, baseEnd_6767295] using wordTrace_append hprefix tailTrace_6767295
  have hstable : (prefixWord ++ tailWord_6767295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767295).length < 2 ^ (prefixWord ++ tailWord_6767295).sum := by decide
  have hdescent : baseEnd_6767295 < baseStart_6767295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767302 : List Nat := [6, 1, 2, 1, 2, 2, 1, 8]
def baseStart_6767302 : Nat := 118140960795 + 6767302 * 2 ^ 59
def prefixEnd_6767302 : Nat := 4983230072969 + 3 ^ 40 * 6767302 * 2
def baseEnd_6767302 : Nat := 128699209634547671611213

theorem tailTrace_6767302 : CollatzResearch.WordTrace tailWord_6767302 prefixEnd_6767302 128699209634547671611213 := by
  unfold tailWord_6767302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713243166538377875365755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 164549187552818728007802773 7713243166538377875365755)
  ·
    refine ⟨11569864749807566813048633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7713243166538377875365755 11569864749807566813048633)
    ·
      refine ⟨8677398562355675109786475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11569864749807566813048633 8677398562355675109786475)
      ·
        refine ⟨13016097843533512664679713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677398562355675109786475 13016097843533512664679713)
        ·
          refine ⟨9762073382650134498509785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13016097843533512664679713 9762073382650134498509785)
          ·
            refine ⟨7321555036987600873882339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9762073382650134498509785 7321555036987600873882339)
            ·
              refine ⟨10982332555481401310823509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321555036987600873882339 10982332555481401310823509)
              ·
                refine ⟨128699209634547671611213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10982332555481401310823509 128699209634547671611213)
                ·
                  rfl

theorem cell23_6767302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_6767302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767302 prefixEnd_6767302 := by exact prefixLift 6767302
  have htrace : WordTrace (prefixWord ++ tailWord_6767302) baseStart_6767302 baseEnd_6767302 := by
    simpa [prefixWord, tailWord_6767302, baseEnd_6767302] using wordTrace_append hprefix tailTrace_6767302
  have hstable : (prefixWord ++ tailWord_6767302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767302).length < 2 ^ (prefixWord ++ tailWord_6767302).sum := by decide
  have hdescent : baseEnd_6767302 < baseStart_6767302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767321 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_6767321 : Nat := 118140960795 + 6767321 * 2 ^ 59
def prefixEnd_6767321 : Nat := 4983230072969 + 3 ^ 40 * 6767321 * 2
def baseEnd_6767321 : Nat := 3474888416265222559165163

theorem tailTrace_6767321 : CollatzResearch.WordTrace tailWord_6767321 prefixEnd_6767321 3474888416265222559165163 := by
  unfold tailWord_6767321
  simp only [CollatzResearch.WordTrace]
  refine ⟨246824474316159258256645817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164549649544106172171097211 246824474316159258256645817)
  ·
    refine ⟨185118355737119443692484363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246824474316159258256645817 185118355737119443692484363)
    ·
      refine ⟨277677533605679165538726545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185118355737119443692484363 277677533605679165538726545)
      ·
        refine ⟨208258150204259374154044909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277677533605679165538726545 208258150204259374154044909)
        ·
          refine ⟨78096806326597265307766841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208258150204259374154044909 78096806326597265307766841)
          ·
            refine ⟨58572604744947948980825131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78096806326597265307766841 58572604744947948980825131)
            ·
              refine ⟨87858907117421923471237697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58572604744947948980825131 87858907117421923471237697)
              ·
                refine ⟨65894180338066442603428273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87858907117421923471237697 65894180338066442603428273)
                ·
                  refine ⟨49420635253549831952571205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65894180338066442603428273 49420635253549831952571205)
                  ·
                    refine ⟨9266369110040593491107101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49420635253549831952571205 9266369110040593491107101)
                    ·
                      refine ⟨3474888416265222559165163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266369110040593491107101 3474888416265222559165163)
                      ·
                        rfl

theorem cell23_6767321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_6767321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767321 prefixEnd_6767321 := by exact prefixLift 6767321
  have htrace : WordTrace (prefixWord ++ tailWord_6767321) baseStart_6767321 baseEnd_6767321 := by
    simpa [prefixWord, tailWord_6767321, baseEnd_6767321] using wordTrace_append hprefix tailTrace_6767321
  have hstable : (prefixWord ++ tailWord_6767321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767321).length < 2 ^ (prefixWord ++ tailWord_6767321).sum := by decide
  have hdescent : baseEnd_6767321 < baseStart_6767321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767341 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 9]
def baseStart_6767341 : Nat := 118140960795 + 6767341 * 2 ^ 59
def prefixEnd_6767341 : Nat := 4983230072969 + 3 ^ 40 * 6767341 * 2
def baseEnd_6767341 : Nat := 386099853986479164546119

theorem tailTrace_6767341 : CollatzResearch.WordTrace tailWord_6767341 prefixEnd_6767341 386099853986479164546119 := by
  unfold tailWord_6767341
  simp only [CollatzResearch.WordTrace]
  refine ⟨246825203776086801672373877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164550135850724534448249251 246825203776086801672373877)
  ·
    refine ⟨23139862854008137656785051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246825203776086801672373877 23139862854008137656785051)
    ·
      refine ⟨34709794281012206485177577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139862854008137656785051 34709794281012206485177577)
      ·
        refine ⟨26032345710759154863883183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34709794281012206485177577 26032345710759154863883183)
        ·
          refine ⟨39048518566138732295824775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26032345710759154863883183 39048518566138732295824775)
          ·
            refine ⟨58572777849208098443737163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39048518566138732295824775 58572777849208098443737163)
            ·
              refine ⟨87859166773812147665605745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58572777849208098443737163 87859166773812147665605745)
              ·
                refine ⟨65894375080359110749204309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87859166773812147665605745 65894375080359110749204309)
                ·
                  refine ⟨386099853986479164546119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65894375080359110749204309 386099853986479164546119)
                  ·
                    rfl

theorem cell23_6767341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_6767341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767341 prefixEnd_6767341 := by exact prefixLift 6767341
  have htrace : WordTrace (prefixWord ++ tailWord_6767341) baseStart_6767341 baseEnd_6767341 := by
    simpa [prefixWord, tailWord_6767341, baseEnd_6767341] using wordTrace_append hprefix tailTrace_6767341
  have hstable : (prefixWord ++ tailWord_6767341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767341).length < 2 ^ (prefixWord ++ tailWord_6767341).sum := by decide
  have hdescent : baseEnd_6767341 < baseStart_6767341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767358 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_6767358 : Nat := 118140960795 + 6767358 * 2 ^ 59
def prefixEnd_6767358 : Nat := 4983230072969 + 3 ^ 40 * 6767358 * 2
def baseEnd_6767358 : Nat := 386100823894382101600277

theorem tailTrace_6767358 : CollatzResearch.WordTrace tailWord_6767358 prefixEnd_6767358 386100823894382101600277 := by
  unfold tailWord_6767358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30853227977128151696967841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164550549211350142383828485 30853227977128151696967841)
  ·
    refine ⟨23139920982846113772725881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30853227977128151696967841 23139920982846113772725881)
    ·
      refine ⟨17354940737134585329544411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23139920982846113772725881 17354940737134585329544411)
      ·
        refine ⟨26032411105701877994316617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17354940737134585329544411 26032411105701877994316617)
        ·
          refine ⟨19524308329276408495737463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26032411105701877994316617 19524308329276408495737463)
          ·
            refine ⟨29286462493914612743606195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19524308329276408495737463 29286462493914612743606195)
            ·
              refine ⟨43929693740871919115409293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29286462493914612743606195 43929693740871919115409293)
              ·
                refine ⟨16473635152826969668278485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43929693740871919115409293 16473635152826969668278485)
                ·
                  refine ⟨386100823894382101600277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16473635152826969668278485 386100823894382101600277)
                  ·
                    rfl

theorem cell23_6767358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_6767358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767358 prefixEnd_6767358 := by exact prefixLift 6767358
  have htrace : WordTrace (prefixWord ++ tailWord_6767358) baseStart_6767358 baseEnd_6767358 := by
    simpa [prefixWord, tailWord_6767358, baseEnd_6767358] using wordTrace_append hprefix tailTrace_6767358
  have hstable : (prefixWord ++ tailWord_6767358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767358).length < 2 ^ (prefixWord ++ tailWord_6767358).sum := by decide
  have hdescent : baseEnd_6767358 < baseStart_6767358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767368 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_6767368 : Nat := 118140960795 + 6767368 * 2 ^ 59
def prefixEnd_6767368 : Nat := 4983230072969 + 3 ^ 40 * 6767368 * 2
def baseEnd_6767368 : Nat := 3474912549855983875277447

theorem tailTrace_6767368 : CollatzResearch.WordTrace tailWord_6767368 prefixEnd_6767368 3474912549855983875277447 := by
  unfold tailWord_6767368
  simp only [CollatzResearch.WordTrace]
  refine ⟨123413094273494492641803379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164550792364659323522404505 123413094273494492641803379)
  ·
    refine ⟨185119641410241738962705069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123413094273494492641803379 185119641410241738962705069)
    ·
      refine ⟨69419865528840652111014401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185119641410241738962705069 69419865528840652111014401)
      ·
        refine ⟨52064899146630489083260801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69419865528840652111014401 52064899146630489083260801)
        ·
          refine ⟨39048674359972866812445601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52064899146630489083260801 39048674359972866812445601)
          ·
            refine ⟨29286505769979650109334201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39048674359972866812445601 29286505769979650109334201)
            ·
              refine ⟨21964879327484737582000651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29286505769979650109334201 21964879327484737582000651)
              ·
                refine ⟨32947318991227106373000977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21964879327484737582000651 32947318991227106373000977)
                ·
                  refine ⟨24710489243420329779750733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32947318991227106373000977 24710489243420329779750733)
                  ·
                    refine ⟨9266433466282623667406525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24710489243420329779750733 9266433466282623667406525)
                    ·
                      refine ⟨3474912549855983875277447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266433466282623667406525 3474912549855983875277447)
                      ·
                        rfl

theorem cell23_6767368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_6767368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767368 prefixEnd_6767368 := by exact prefixLift 6767368
  have htrace : WordTrace (prefixWord ++ tailWord_6767368) baseStart_6767368 baseEnd_6767368 := by
    simpa [prefixWord, tailWord_6767368, baseEnd_6767368] using wordTrace_append hprefix tailTrace_6767368
  have hstable : (prefixWord ++ tailWord_6767368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767368).length < 2 ^ (prefixWord ++ tailWord_6767368).sum := by decide
  have hdescent : baseEnd_6767368 < baseStart_6767368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767408 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2]
def baseStart_6767408 : Nat := 118140960795 + 6767408 * 2 ^ 59
def prefixEnd_6767408 : Nat := 4983230072969 + 3 ^ 40 * 6767408 * 2
def baseEnd_6767408 : Nat := 3474933089082163718777263

theorem tailTrace_6767408 : CollatzResearch.WordTrace tailWord_6767408 prefixEnd_6767408 3474933089082163718777263 := by
  unfold tailWord_6767408
  simp only [CollatzResearch.WordTrace]
  refine ⟨123413823733422036057531439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164551764977896048076708585 123413823733422036057531439)
  ·
    refine ⟨185120735600133054086297159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123413823733422036057531439 185120735600133054086297159)
    ·
      refine ⟨277681103400199581129445739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185120735600133054086297159 277681103400199581129445739)
      ·
        refine ⟨416521655100299371694168609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277681103400199581129445739 416521655100299371694168609)
        ·
          refine ⟨312391241325224528770626457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416521655100299371694168609 312391241325224528770626457)
          ·
            refine ⟨234293430993918396577969843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312391241325224528770626457 234293430993918396577969843)
            ·
              refine ⟨351440146490877594866954765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234293430993918396577969843 351440146490877594866954765)
              ·
                refine ⟨131790054934079098075108037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351440146490877594866954765 131790054934079098075108037)
                ·
                  refine ⟨24710635300139830889082757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131790054934079098075108037 24710635300139830889082757)
                  ·
                    refine ⟨4633244118776218291703017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24710635300139830889082757 4633244118776218291703017)
                    ·
                      refine ⟨3474933089082163718777263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633244118776218291703017 3474933089082163718777263)
                      ·
                        rfl

theorem cell23_6767408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2].length) (baseStart_6767408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767408 prefixEnd_6767408 := by exact prefixLift 6767408
  have htrace : WordTrace (prefixWord ++ tailWord_6767408) baseStart_6767408 baseEnd_6767408 := by
    simpa [prefixWord, tailWord_6767408, baseEnd_6767408] using wordTrace_append hprefix tailTrace_6767408
  have hstable : (prefixWord ++ tailWord_6767408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767408).length < 2 ^ (prefixWord ++ tailWord_6767408).sum := by decide
  have hdescent : baseEnd_6767408 < baseStart_6767408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767445 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6767445 : Nat := 118140960795 + 6767445 * 2 ^ 59
def prefixEnd_6767445 : Nat := 4983230072969 + 3 ^ 40 * 6767445 * 2
def baseEnd_6767445 : Nat := 3474952087866380074014593

theorem tailTrace_6767445 : CollatzResearch.WordTrace tailWord_6767445 prefixEnd_6767445 3474952087866380074014593 := by
  unfold tailWord_6767445
  simp only [CollatzResearch.WordTrace]
  refine ⟨246828996967710027434159789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164552664645140018289439859 246828996967710027434159789)
  ·
    refine ⟨92560873862891260287809921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246828996967710027434159789 92560873862891260287809921)
    ·
      refine ⟨69420655397168445215857441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92560873862891260287809921 69420655397168445215857441)
      ·
        refine ⟨52065491547876333911893081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69420655397168445215857441 52065491547876333911893081)
        ·
          refine ⟨39049118660907250433919811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52065491547876333911893081 39049118660907250433919811)
          ·
            refine ⟨58573677991360875650879717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39049118660907250433919811 58573677991360875650879717)
            ·
              refine ⟨10982564623380164184539947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58573677991360875650879717 10982564623380164184539947)
              ·
                refine ⟨16473846935070246276809921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982564623380164184539947 16473846935070246276809921)
                ·
                  refine ⟨12355385201302684707607441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16473846935070246276809921 12355385201302684707607441)
                  ·
                    refine ⟨9266538900977013530705581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12355385201302684707607441 9266538900977013530705581)
                    ·
                      refine ⟨3474952087866380074014593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266538900977013530705581 3474952087866380074014593)
                      ·
                        rfl

theorem cell23_6767445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6767445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767445 prefixEnd_6767445 := by exact prefixLift 6767445
  have htrace : WordTrace (prefixWord ++ tailWord_6767445) baseStart_6767445 baseEnd_6767445 := by
    simpa [prefixWord, tailWord_6767445, baseEnd_6767445] using wordTrace_append hprefix tailTrace_6767445
  have hstable : (prefixWord ++ tailWord_6767445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767445).length < 2 ^ (prefixWord ++ tailWord_6767445).sum := by decide
  have hdescent : baseEnd_6767445 < baseStart_6767445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767471 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_6767471 : Nat := 118140960795 + 6767471 * 2 ^ 59
def prefixEnd_6767471 : Nat := 4983230072969 + 3 ^ 40 * 6767471 * 2
def baseEnd_6767471 : Nat := 3474965438363396972289473

theorem tailTrace_6767471 : CollatzResearch.WordTrace tailWord_6767471 prefixEnd_6767471 3474965438363396972289473 := by
  unfold tailWord_6767471
  simp only [CollatzResearch.WordTrace]
  refine ⟨246829945265615833874606267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164553296843743889249737511 246829945265615833874606267)
  ·
    refine ⟨370244917898423750811909401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246829945265615833874606267 370244917898423750811909401)
    ·
      refine ⟨277683688423817813108932051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370244917898423750811909401 277683688423817813108932051)
      ·
        refine ⟨416525532635726719663398077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277683688423817813108932051 416525532635726719663398077)
        ·
          refine ⟨156197074738397519873774279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416525532635726719663398077 156197074738397519873774279)
          ·
            refine ⟨234295612107596279810661419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156197074738397519873774279 234295612107596279810661419)
            ·
              refine ⟨351443418161394419715992129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234295612107596279810661419 351443418161394419715992129)
              ·
                refine ⟨263582563621045814786994097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351443418161394419715992129 263582563621045814786994097)
                ·
                  refine ⟨197686922715784361090245573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263582563621045814786994097 197686922715784361090245573)
                  ·
                    refine ⟨37066298009209567704421045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197686922715784361090245573 37066298009209567704421045)
                    ·
                      refine ⟨3474965438363396972289473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37066298009209567704421045 3474965438363396972289473)
                      ·
                        rfl

theorem cell23_6767471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_6767471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767471 prefixEnd_6767471 := by exact prefixLift 6767471
  have htrace : WordTrace (prefixWord ++ tailWord_6767471) baseStart_6767471 baseEnd_6767471 := by
    simpa [prefixWord, tailWord_6767471, baseEnd_6767471] using wordTrace_append hprefix tailTrace_6767471
  have hstable : (prefixWord ++ tailWord_6767471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767471).length < 2 ^ (prefixWord ++ tailWord_6767471).sum := by decide
  have hdescent : baseEnd_6767471 < baseStart_6767471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767485 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_6767485 : Nat := 118140960795 + 6767485 * 2 ^ 59
def prefixEnd_6767485 : Nat := 4983230072969 + 3 ^ 40 * 6767485 * 2
def baseEnd_6767485 : Nat := 3474972627092559917514409

theorem tailTrace_6767485 : CollatzResearch.WordTrace tailWord_6767485 prefixEnd_6767485 3474972627092559917514409 := by
  unfold tailWord_6767485
  simp only [CollatzResearch.WordTrace]
  refine ⟨246830455887565114265615909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164553637258376742843743939 246830455887565114265615909)
  ·
    refine ⟨46280710478918458924802983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246830455887565114265615909 46280710478918458924802983)
    ·
      refine ⟨69421065718377688387204475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46280710478918458924802983 69421065718377688387204475)
      ·
        refine ⟨104131598577566532580806713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69421065718377688387204475 104131598577566532580806713)
        ·
          refine ⟨78098698933174899435605035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104131598577566532580806713 78098698933174899435605035)
          ·
            refine ⟨117148048399762349153407553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78098698933174899435605035 117148048399762349153407553)
            ·
              refine ⟨87861036299821761865055665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117148048399762349153407553 87861036299821761865055665)
              ·
                refine ⟨65895777224866321398791749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87861036299821761865055665 65895777224866321398791749)
                ·
                  refine ⟨12355458229662435262273453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65895777224866321398791749 12355458229662435262273453)
                  ·
                    refine ⟨4633296836123413223352545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12355458229662435262273453 4633296836123413223352545)
                    ·
                      refine ⟨3474972627092559917514409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633296836123413223352545 3474972627092559917514409)
                      ·
                        rfl

theorem cell23_6767485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_6767485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767485 prefixEnd_6767485 := by exact prefixLift 6767485
  have htrace : WordTrace (prefixWord ++ tailWord_6767485) baseStart_6767485 baseEnd_6767485 := by
    simpa [prefixWord, tailWord_6767485, baseEnd_6767485] using wordTrace_append hprefix tailTrace_6767485
  have hstable : (prefixWord ++ tailWord_6767485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767485).length < 2 ^ (prefixWord ++ tailWord_6767485).sum := by decide
  have hdescent : baseEnd_6767485 < baseStart_6767485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767509 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_6767509 : Nat := 118140960795 + 6767509 * 2 ^ 59
def prefixEnd_6767509 : Nat := 4983230072969 + 3 ^ 40 * 6767509 * 2
def baseEnd_6767509 : Nat := 3474984950628267823614299

theorem tailTrace_6767509 : CollatzResearch.WordTrace tailWord_6767509 prefixEnd_6767509 3474984950628267823614299 := by
  unfold tailWord_6767509
  simp only [CollatzResearch.WordTrace]
  refine ⟨246831331239478166364489581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164554220826318777576326387 246831331239478166364489581)
  ·
    refine ⟨92561749214804312386683593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246831331239478166364489581 92561749214804312386683593)
    ·
      refine ⟨69421311911103234290012695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92561749214804312386683593 69421311911103234290012695)
      ·
        refine ⟨104131967866654851435019043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69421311911103234290012695 104131967866654851435019043)
        ·
          refine ⟨156197951799982277152528565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104131967866654851435019043 156197951799982277152528565)
          ·
            refine ⟨14643557981248338483049553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156197951799982277152528565 14643557981248338483049553)
            ·
              refine ⟨10982668485936253862287165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643557981248338483049553 10982668485936253862287165)
              ·
                refine ⟨4118500682226095198357687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10982668485936253862287165 4118500682226095198357687)
                ·
                  refine ⟨6177751023339142797536531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118500682226095198357687 6177751023339142797536531)
                  ·
                    refine ⟨9266626535008714196304797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177751023339142797536531 9266626535008714196304797)
                    ·
                      refine ⟨3474984950628267823614299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266626535008714196304797 3474984950628267823614299)
                      ·
                        rfl

theorem cell23_6767509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_6767509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767509 prefixEnd_6767509 := by exact prefixLift 6767509
  have htrace : WordTrace (prefixWord ++ tailWord_6767509) baseStart_6767509 baseEnd_6767509 := by
    simpa [prefixWord, tailWord_6767509, baseEnd_6767509] using wordTrace_append hprefix tailTrace_6767509
  have hstable : (prefixWord ++ tailWord_6767509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767509).length < 2 ^ (prefixWord ++ tailWord_6767509).sum := by decide
  have hdescent : baseEnd_6767509 < baseStart_6767509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767545 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6767545 : Nat := 118140960795 + 6767545 * 2 ^ 59
def prefixEnd_6767545 : Nat := 4983230072969 + 3 ^ 40 * 6767545 * 2
def baseEnd_6767545 : Nat := 3475003435931829682764133

theorem tailTrace_6767545 : CollatzResearch.WordTrace tailWord_6767545 prefixEnd_6767545 3475003435931829682764133 := by
  unfold tailWord_6767545
  simp only [CollatzResearch.WordTrace]
  refine ⟨246832644267347744512800089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164555096178231829675200059 246832644267347744512800089)
  ·
    refine ⟨185124483200510808384600067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246832644267347744512800089 185124483200510808384600067)
    ·
      refine ⟨277686724800766212576900101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185124483200510808384600067 277686724800766212576900101)
      ·
        refine ⟨52066260900143664858168769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277686724800766212576900101 52066260900143664858168769)
        ·
          refine ⟨39049695675107748643626577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52066260900143664858168769 39049695675107748643626577)
          ·
            refine ⟨29287271756330811482719933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39049695675107748643626577 29287271756330811482719933)
            ·
              refine ⟨10982726908624054306019975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29287271756330811482719933 10982726908624054306019975)
              ·
                refine ⟨16474090362936081459029963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982726908624054306019975 16474090362936081459029963)
                ·
                  refine ⟨24711135544404122188544945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16474090362936081459029963 24711135544404122188544945)
                  ·
                    refine ⟨18533351658303091641408709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24711135544404122188544945 18533351658303091641408709)
                    ·
                      refine ⟨3475003435931829682764133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18533351658303091641408709 3475003435931829682764133)
                      ·
                        rfl

theorem cell23_6767545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6767545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767545 prefixEnd_6767545 := by exact prefixLift 6767545
  have htrace : WordTrace (prefixWord ++ tailWord_6767545) baseStart_6767545 baseEnd_6767545 := by
    simpa [prefixWord, tailWord_6767545, baseEnd_6767545] using wordTrace_append hprefix tailTrace_6767545
  have hstable : (prefixWord ++ tailWord_6767545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767545).length < 2 ^ (prefixWord ++ tailWord_6767545).sum := by decide
  have hdescent : baseEnd_6767545 < baseStart_6767545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767552 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_6767552 : Nat := 118140960795 + 6767552 * 2 ^ 59
def prefixEnd_6767552 : Nat := 4983230072969 + 3 ^ 40 * 6767552 * 2
def baseEnd_6767552 : Nat := 3475007030296411155376601

theorem tailTrace_6767552 : CollatzResearch.WordTrace tailWord_6767552 prefixEnd_6767552 3475007030296411155376601 := by
  unfold tailWord_6767552
  simp only [CollatzResearch.WordTrace]
  refine ⟨123416449789161192354152455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164555266385548256472203273 123416449789161192354152455)
  ·
    refine ⟨185124674683741788531228683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123416449789161192354152455 185124674683741788531228683)
    ·
      refine ⟨277687012025612682796843025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185124674683741788531228683 277687012025612682796843025)
      ·
        refine ⟨208265259019209512097632269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277687012025612682796843025 208265259019209512097632269)
        ·
          refine ⟨78099472132203567036612101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208265259019209512097632269 78099472132203567036612101)
          ·
            refine ⟨14643651024788168819364769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78099472132203567036612101 14643651024788168819364769)
            ·
              refine ⟨10982738268591126614523577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643651024788168819364769 10982738268591126614523577)
              ·
                refine ⟨8237053701443344960892683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10982738268591126614523577 8237053701443344960892683)
                ·
                  refine ⟨12355580552165017441339025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237053701443344960892683 12355580552165017441339025)
                  ·
                    refine ⟨9266685414123763081004269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12355580552165017441339025 9266685414123763081004269)
                    ·
                      refine ⟨3475007030296411155376601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266685414123763081004269 3475007030296411155376601)
                      ·
                        rfl

theorem cell23_6767552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_6767552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767552 prefixEnd_6767552 := by exact prefixLift 6767552
  have htrace : WordTrace (prefixWord ++ tailWord_6767552) baseStart_6767552 baseEnd_6767552 := by
    simpa [prefixWord, tailWord_6767552, baseEnd_6767552] using wordTrace_append hprefix tailTrace_6767552
  have hstable : (prefixWord ++ tailWord_6767552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767552).length < 2 ^ (prefixWord ++ tailWord_6767552).sum := by decide
  have hdescent : baseEnd_6767552 < baseStart_6767552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767566 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_6767566 : Nat := 118140960795 + 6767566 * 2 ^ 59
def prefixEnd_6767566 : Nat := 4983230072969 + 3 ^ 40 * 6767566 * 2
def baseEnd_6767566 : Nat := 3475014219025574100601537

theorem tailTrace_6767566 : CollatzResearch.WordTrace tailWord_6767566 prefixEnd_6767566 3475014219025574100601537 := by
  unfold tailWord_6767566
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854176275033958137414319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164555606800181110066209701 30854176275033958137414319)
  ·
    refine ⟨46281264412550937206121479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30854176275033958137414319 46281264412550937206121479)
    ·
      refine ⟨69421896618826405809182219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46281264412550937206121479 69421896618826405809182219)
      ·
        refine ⟨104132844928239608713773329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69421896618826405809182219 104132844928239608713773329)
        ·
          refine ⟨78099633696179706535329997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104132844928239608713773329 78099633696179706535329997)
          ·
            refine ⟨29287362636067389950748749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78099633696179706535329997 29287362636067389950748749)
            ·
              refine ⟨10982760988525271231530781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29287362636067389950748749 10982760988525271231530781)
              ·
                refine ⟨4118535370696976711824043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10982760988525271231530781 4118535370696976711824043)
                ·
                  refine ⟨6177803056045465067736065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118535370696976711824043 6177803056045465067736065)
                  ·
                    refine ⟨4633352292034098800802049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177803056045465067736065 4633352292034098800802049)
                    ·
                      refine ⟨3475014219025574100601537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633352292034098800802049 3475014219025574100601537)
                      ·
                        rfl

theorem cell23_6767566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_6767566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767566 prefixEnd_6767566 := by exact prefixLift 6767566
  have htrace : WordTrace (prefixWord ++ tailWord_6767566) baseStart_6767566 baseEnd_6767566 := by
    simpa [prefixWord, tailWord_6767566, baseEnd_6767566] using wordTrace_append hprefix tailTrace_6767566
  have hstable : (prefixWord ++ tailWord_6767566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767566).length < 2 ^ (prefixWord ++ tailWord_6767566).sum := by decide
  have hdescent : baseEnd_6767566 < baseStart_6767566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767583 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 1, 2, 2]
def baseStart_6767583 : Nat := 118140960795 + 6767583 * 2 ^ 59
def prefixEnd_6767583 : Nat := 4983230072969 + 3 ^ 40 * 6767583 * 2
def baseEnd_6767583 : Nat := 3475022948196700534088959

theorem tailTrace_6767583 : CollatzResearch.WordTrace tailWord_6767583 prefixEnd_6767583 3475022948196700534088959 := by
  unfold tailWord_6767583
  simp only [CollatzResearch.WordTrace]
  refine ⟨246834030241210077002683403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164556020160806718001788935 246834030241210077002683403)
  ·
    refine ⟨370251045361815115504025105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246834030241210077002683403 370251045361815115504025105)
    ·
      refine ⟨277688284021361336628018829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370251045361815115504025105 277688284021361336628018829)
      ·
        refine ⟨104133106508010501235507061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277688284021361336628018829 104133106508010501235507061)
        ·
          refine ⟨9762478735125984490828787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104133106508010501235507061 9762478735125984490828787)
          ·
            refine ⟨14643718102688976736243181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762478735125984490828787 14643718102688976736243181)
            ·
              refine ⟨5491394288508366276091193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14643718102688976736243181 5491394288508366276091193)
              ·
                refine ⟨4118545716381274707068395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491394288508366276091193 4118545716381274707068395)
                ·
                  refine ⟨6177818574571912060602593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118545716381274707068395 6177818574571912060602593)
                  ·
                    refine ⟨4633363930928934045451945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177818574571912060602593 4633363930928934045451945)
                    ·
                      refine ⟨3475022948196700534088959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633363930928934045451945 3475022948196700534088959)
                      ·
                        rfl

theorem cell23_6767583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_6767583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767583 prefixEnd_6767583 := by exact prefixLift 6767583
  have htrace : WordTrace (prefixWord ++ tailWord_6767583) baseStart_6767583 baseEnd_6767583 := by
    simpa [prefixWord, tailWord_6767583, baseEnd_6767583] using wordTrace_append hprefix tailTrace_6767583
  have hstable : (prefixWord ++ tailWord_6767583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767583).length < 2 ^ (prefixWord ++ tailWord_6767583).sum := by decide
  have hdescent : baseEnd_6767583 < baseStart_6767583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767599 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 2, 1, 3]
def baseStart_6767599 : Nat := 118140960795 + 6767599 * 2 ^ 59
def prefixEnd_6767599 : Nat := 4983230072969 + 3 ^ 40 * 6767599 * 2
def baseEnd_6767599 : Nat := 3475031163887172471488885

theorem tailTrace_6767599 : CollatzResearch.WordTrace tailWord_6767599 prefixEnd_6767599 3475031163887172471488885 := by
  unfold tailWord_6767599
  simp only [CollatzResearch.WordTrace]
  refine ⟨246834613809152111735265851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164556409206101407823510567 246834613809152111735265851)
  ·
    refine ⟨370251920713728167602898777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246834613809152111735265851 370251920713728167602898777)
    ·
      refine ⟨277688940535296125702174083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370251920713728167602898777 277688940535296125702174083)
      ·
        refine ⟨416533410802944188553261125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277688940535296125702174083 416533410802944188553261125)
        ·
          refine ⟨78100014525552035353736461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 416533410802944188553261125 78100014525552035353736461)
          ·
            refine ⟨29287505447082013257651173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78100014525552035353736461 29287505447082013257651173)
            ·
              refine ⟨5491407271327877485809595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29287505447082013257651173 5491407271327877485809595)
              ·
                refine ⟨8237110906991816228714393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491407271327877485809595 8237110906991816228714393)
                ·
                  refine ⟨6177833180243862171535795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8237110906991816228714393 6177833180243862171535795)
                  ·
                    refine ⟨9266749770365793257303693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6177833180243862171535795 9266749770365793257303693)
                    ·
                      refine ⟨3475031163887172471488885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266749770365793257303693 3475031163887172471488885)
                      ·
                        rfl

theorem cell23_6767599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 1, 3].length) (baseStart_6767599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767599 prefixEnd_6767599 := by exact prefixLift 6767599
  have htrace : WordTrace (prefixWord ++ tailWord_6767599) baseStart_6767599 baseEnd_6767599 := by
    simpa [prefixWord, tailWord_6767599, baseEnd_6767599] using wordTrace_append hprefix tailTrace_6767599
  have hstable : (prefixWord ++ tailWord_6767599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767599).length < 2 ^ (prefixWord ++ tailWord_6767599).sum := by decide
  have hdescent : baseEnd_6767599 < baseStart_6767599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767626 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_6767626 : Nat := 118140960795 + 6767626 * 2 ^ 59
def prefixEnd_6767626 : Nat := 4983230072969 + 3 ^ 40 * 6767626 * 2
def baseEnd_6767626 : Nat := 3475045027864843865851261

theorem tailTrace_6767626 : CollatzResearch.WordTrace tailWord_6767626 prefixEnd_6767626 3475045027864843865851261 := by
  unfold tailWord_6767626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61708899645013573836624683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164557065720036196897665821 61708899645013573836624683)
  ·
    refine ⟨92563349467520360754937025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61708899645013573836624683 92563349467520360754937025)
    ·
      refine ⟨69422512100640270566202769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92563349467520360754937025 69422512100640270566202769)
      ·
        refine ⟨52066884075480202924652077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69422512100640270566202769 52066884075480202924652077)
        ·
          refine ⟨19525081528305076096744529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52066884075480202924652077 19525081528305076096744529)
          ·
            refine ⟨14643811146228807072558397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19525081528305076096744529 14643811146228807072558397)
            ·
              refine ⟨5491429179835802652209399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14643811146228807072558397 5491429179835802652209399)
              ·
                refine ⟨8237143769753703978314099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491429179835802652209399 8237143769753703978314099)
                ·
                  refine ⟨12355715654630555967471149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237143769753703978314099 12355715654630555967471149)
                  ·
                    refine ⟨4633393370486458487801681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12355715654630555967471149 4633393370486458487801681)
                    ·
                      refine ⟨3475045027864843865851261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633393370486458487801681 3475045027864843865851261)
                      ·
                        rfl

theorem cell23_6767626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_6767626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767626 prefixEnd_6767626 := by exact prefixLift 6767626
  have htrace : WordTrace (prefixWord ++ tailWord_6767626) baseStart_6767626 baseEnd_6767626 := by
    simpa [prefixWord, tailWord_6767626, baseEnd_6767626] using wordTrace_append hprefix tailTrace_6767626
  have hstable : (prefixWord ++ tailWord_6767626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767626).length < 2 ^ (prefixWord ++ tailWord_6767626).sum := by decide
  have hdescent : baseEnd_6767626 < baseStart_6767626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767634 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6767634 : Nat := 118140960795 + 6767634 * 2 ^ 59
def prefixEnd_6767634 : Nat := 4983230072969 + 3 ^ 40 * 6767634 * 2
def baseEnd_6767634 : Nat := 3475049135710079834551225

theorem tailTrace_6767634 : CollatzResearch.WordTrace tailWord_6767634 prefixEnd_6767634 3475049135710079834551225 := by
  unfold tailWord_6767634
  simp only [CollatzResearch.WordTrace]
  refine ⟨61708972591006328178197489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164557260242683541808526637 61708972591006328178197489)
  ·
    refine ⟨46281729443254746133648117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61708972591006328178197489 46281729443254746133648117)
    ·
      refine ⟨4338912135305132450029511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46281729443254746133648117 4338912135305132450029511)
      ·
        refine ⟨6508368202957698675044267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338912135305132450029511 6508368202957698675044267)
        ·
          refine ⟨9762552304436548012566401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508368202957698675044267 9762552304436548012566401)
          ·
            refine ⟨7321914228327411009424801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9762552304436548012566401 7321914228327411009424801)
            ·
              refine ⟨5491435671245558257068601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7321914228327411009424801 5491435671245558257068601)
              ·
                refine ⟨4118576753434168692801451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491435671245558257068601 4118576753434168692801451)
                ·
                  refine ⟨6177865130151253039202177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118576753434168692801451 6177865130151253039202177)
                  ·
                    refine ⟨4633398847613439779401633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177865130151253039202177 4633398847613439779401633)
                    ·
                      refine ⟨3475049135710079834551225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633398847613439779401633 3475049135710079834551225)
                      ·
                        rfl

theorem cell23_6767634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6767634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767634 prefixEnd_6767634 := by exact prefixLift 6767634
  have htrace : WordTrace (prefixWord ++ tailWord_6767634) baseStart_6767634 baseEnd_6767634 := by
    simpa [prefixWord, tailWord_6767634, baseEnd_6767634] using wordTrace_append hprefix tailTrace_6767634
  have hstable : (prefixWord ++ tailWord_6767634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767634).length < 2 ^ (prefixWord ++ tailWord_6767634).sum := by decide
  have hdescent : baseEnd_6767634 < baseStart_6767634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767652 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6767652 : Nat := 118140960795 + 6767652 * 2 ^ 59
def prefixEnd_6767652 : Nat := 4983230072969 + 3 ^ 40 * 6767652 * 2
def baseEnd_6767652 : Nat := 3475058378361860764126141

theorem tailTrace_6767652 : CollatzResearch.WordTrace tailWord_6767652 prefixEnd_6767652 3475058378361860764126141 := by
  unfold tailWord_6767652
  simp only [CollatzResearch.WordTrace]
  refine ⟨123418273438980050893472605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164557697918640067857963473 123418273438980050893472605)
  ·
    refine ⟨46281852539617519085052227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123418273438980050893472605 46281852539617519085052227)
    ·
      refine ⟨69422778809426278627578341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46281852539617519085052227 69422778809426278627578341)
      ·
        refine ⟨13016771026767427242670939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69422778809426278627578341 13016771026767427242670939)
        ·
          refine ⟨19525156540151140864006409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016771026767427242670939 19525156540151140864006409)
          ·
            refine ⟨14643867405113355648004807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19525156540151140864006409 14643867405113355648004807)
            ·
              refine ⟨21965801107670033472007211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14643867405113355648004807 21965801107670033472007211)
              ·
                refine ⟨32948701661505050208010817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21965801107670033472007211 32948701661505050208010817)
                ·
                  refine ⟨24711526246128787656008113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32948701661505050208010817 24711526246128787656008113)
                  ·
                    refine ⟨18533644684596590742006085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24711526246128787656008113 18533644684596590742006085)
                    ·
                      refine ⟨3475058378361860764126141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18533644684596590742006085 3475058378361860764126141)
                      ·
                        rfl

theorem cell23_6767652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6767652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767652 prefixEnd_6767652 := by exact prefixLift 6767652
  have htrace : WordTrace (prefixWord ++ tailWord_6767652) baseStart_6767652 baseEnd_6767652 := by
    simpa [prefixWord, tailWord_6767652, baseEnd_6767652] using wordTrace_append hprefix tailTrace_6767652
  have hstable : (prefixWord ++ tailWord_6767652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767652).length < 2 ^ (prefixWord ++ tailWord_6767652).sum := by decide
  have hdescent : baseEnd_6767652 < baseStart_6767652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767712 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2]
def baseStart_6767712 : Nat := 118140960795 + 6767712 * 2 ^ 59
def prefixEnd_6767712 : Nat := 4983230072969 + 3 ^ 40 * 6767712 * 2
def baseEnd_6767712 : Nat := 3475089187201130529375865

theorem tailTrace_6767712 : CollatzResearch.WordTrace tailWord_6767712 prefixEnd_6767712 3475089187201130529375865 := by
  unfold tailWord_6767712
  simp only [CollatzResearch.WordTrace]
  refine ⟨123419367628871366017064695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164559156838495154689419593 123419367628871366017064695)
  ·
    refine ⟨185129051443307049025597043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123419367628871366017064695 185129051443307049025597043)
    ·
      refine ⟨277693577164960573538395565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185129051443307049025597043 277693577164960573538395565)
      ·
        refine ⟨104135091436860215076898337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277693577164960573538395565 104135091436860215076898337)
        ·
          refine ⟨78101318577645161307673753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104135091436860215076898337 78101318577645161307673753)
          ·
            refine ⟨58575988933233870980755315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78101318577645161307673753 58575988933233870980755315)
            ·
              refine ⟨87863983399850806471132973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58575988933233870980755315 87863983399850806471132973)
              ·
                refine ⟨32948993774944052426674865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87863983399850806471132973 32948993774944052426674865)
                ·
                  refine ⟨24711745331208039320006149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32948993774944052426674865 24711745331208039320006149)
                  ·
                    refine ⟨4633452249601507372501153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24711745331208039320006149 4633452249601507372501153)
                    ·
                      refine ⟨3475089187201130529375865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633452249601507372501153 3475089187201130529375865)
                      ·
                        rfl

theorem cell23_6767712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_6767712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767712 prefixEnd_6767712 := by exact prefixLift 6767712
  have htrace : WordTrace (prefixWord ++ tailWord_6767712) baseStart_6767712 baseEnd_6767712 := by
    simpa [prefixWord, tailWord_6767712, baseEnd_6767712] using wordTrace_append hprefix tailTrace_6767712
  have hstable : (prefixWord ++ tailWord_6767712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767712).length < 2 ^ (prefixWord ++ tailWord_6767712).sum := by decide
  have hdescent : baseEnd_6767712 < baseStart_6767712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767749 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_6767749 : Nat := 118140960795 + 6767749 * 2 ^ 59
def prefixEnd_6767749 : Nat := 4983230072969 + 3 ^ 40 * 6767749 * 2
def baseEnd_6767749 : Nat := 3475108185985346884613195

theorem tailTrace_6767749 : CollatzResearch.WordTrace tailWord_6767749 prefixEnd_6767749 3475108185985346884613195 := by
  unfold tailWord_6767749
  simp only [CollatzResearch.WordTrace]
  refine ⟨246840084758608687353226301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164560056505739124902150867 246840084758608687353226301)
  ·
    refine ⟨92565031784478257757459863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246840084758608687353226301 92565031784478257757459863)
    ·
      refine ⟨138847547676717386636189795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92565031784478257757459863 138847547676717386636189795)
      ·
        refine ⟨208271321515076079954284693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138847547676717386636189795 208271321515076079954284693)
        ·
          refine ⟨9762718196019191247857095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208271321515076079954284693 9762718196019191247857095)
          ·
            refine ⟨14644077294028786871785643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762718196019191247857095 14644077294028786871785643)
            ·
              refine ⟨21966115941043180307678465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14644077294028786871785643 21966115941043180307678465)
              ·
                refine ⟨16474586955782385230758849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21966115941043180307678465 16474586955782385230758849)
                ·
                  refine ⟨12355940216836788923069137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16474586955782385230758849 12355940216836788923069137)
                  ·
                    refine ⟨9266955162627591692301853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12355940216836788923069137 9266955162627591692301853)
                    ·
                      refine ⟨3475108185985346884613195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9266955162627591692301853 3475108185985346884613195)
                      ·
                        rfl

theorem cell23_6767749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_6767749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767749 prefixEnd_6767749 := by exact prefixLift 6767749
  have htrace : WordTrace (prefixWord ++ tailWord_6767749) baseStart_6767749 baseEnd_6767749 := by
    simpa [prefixWord, tailWord_6767749, baseEnd_6767749] using wordTrace_append hprefix tailTrace_6767749
  have hstable : (prefixWord ++ tailWord_6767749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767749).length < 2 ^ (prefixWord ++ tailWord_6767749).sum := by decide
  have hdescent : baseEnd_6767749 < baseStart_6767749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767795 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 3, 6]
def baseStart_6767795 : Nat := 118140960795 + 6767795 * 2 ^ 59
def prefixEnd_6767795 : Nat := 4983230072969 + 3 ^ 40 * 6767795 * 2
def baseEnd_6767795 : Nat := 1158377268698484568212661

theorem tailTrace_6767795 : CollatzResearch.WordTrace tailWord_6767795 prefixEnd_6767795 1158377268698484568212661 := by
  unfold tailWord_6767795
  simp only [CollatzResearch.WordTrace]
  refine ⟨246841762516442037209400839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164561175010961358139600559 246841762516442037209400839)
  ·
    refine ⟨370262643774663055814101259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246841762516442037209400839 370262643774663055814101259)
    ·
      refine ⟨555393965661994583721151889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370262643774663055814101259 555393965661994583721151889)
      ·
        refine ⟨416545474246495937790863917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555393965661994583721151889 416545474246495937790863917)
        ·
          refine ⟨156204552842435976671573969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416545474246495937790863917 156204552842435976671573969)
          ·
            refine ⟨117153414631826982503680477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156204552842435976671573969 117153414631826982503680477)
            ·
              refine ⟨43932530486935118438880179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117153414631826982503680477 43932530486935118438880179)
              ·
                refine ⟨65898795730402677658320269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43932530486935118438880179 65898795730402677658320269)
                ·
                  refine ⟨24712048398901004121870101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65898795730402677658320269 24712048398901004121870101)
                  ·
                    refine ⟨1158377268698484568212661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24712048398901004121870101 1158377268698484568212661)
                    ·
                      rfl

theorem cell23_6767795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_6767795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767795 prefixEnd_6767795 := by exact prefixLift 6767795
  have htrace : WordTrace (prefixWord ++ tailWord_6767795) baseStart_6767795 baseEnd_6767795 := by
    simpa [prefixWord, tailWord_6767795, baseEnd_6767795] using wordTrace_append hprefix tailTrace_6767795
  have hstable : (prefixWord ++ tailWord_6767795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767795).length < 2 ^ (prefixWord ++ tailWord_6767795).sum := by decide
  have hdescent : baseEnd_6767795 < baseStart_6767795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767799 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 1, 5]
def baseStart_6767799 : Nat := 118140960795 + 6767799 * 2 ^ 59
def prefixEnd_6767799 : Nat := 4983230072969 + 3 ^ 40 * 6767799 * 2
def baseEnd_6767799 : Nat := 1158377953339357229662655

theorem tailTrace_6767799 : CollatzResearch.WordTrace tailWord_6767799 prefixEnd_6767799 1158377953339357229662655 := by
  unfold tailWord_6767799
  simp only [CollatzResearch.WordTrace]
  refine ⟨246841908408427545892546451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164561272272285030595030967 246841908408427545892546451)
  ·
    refine ⟨370262862612641318838819677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246841908408427545892546451 370262862612641318838819677)
    ·
      refine ⟨138848573479740494564557379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370262862612641318838819677 138848573479740494564557379)
      ·
        refine ⟨208272860219610741846836069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138848573479740494564557379 208272860219610741846836069)
        ·
          refine ⟨39051161291177014096281763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208272860219610741846836069 39051161291177014096281763)
          ·
            refine ⟨58576741936765521144422645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39051161291177014096281763 58576741936765521144422645)
            ·
              refine ⟨5491569556571767607289623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58576741936765521144422645 5491569556571767607289623)
              ·
                refine ⟨8237354334857651410934435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491569556571767607289623 8237354334857651410934435)
                ·
                  refine ⟨12356031502286477116401653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237354334857651410934435 12356031502286477116401653)
                  ·
                    refine ⟨1158377953339357229662655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12356031502286477116401653 1158377953339357229662655)
                    ·
                      rfl

theorem cell23_6767799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_6767799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767799 prefixEnd_6767799 := by exact prefixLift 6767799
  have htrace : WordTrace (prefixWord ++ tailWord_6767799) baseStart_6767799 baseEnd_6767799 := by
    simpa [prefixWord, tailWord_6767799, baseEnd_6767799] using wordTrace_append hprefix tailTrace_6767799
  have hstable : (prefixWord ++ tailWord_6767799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767799).length < 2 ^ (prefixWord ++ tailWord_6767799).sum := by decide
  have hdescent : baseEnd_6767799 < baseStart_6767799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767806 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_6767806 : Nat := 118140960795 + 6767806 * 2 ^ 59
def prefixEnd_6767806 : Nat := 4983230072969 + 3 ^ 40 * 6767806 * 2
def baseEnd_6767806 : Nat := 3475137454382653161600433

theorem tailTrace_6767806 : CollatzResearch.WordTrace tailWord_6767806 prefixEnd_6767806 3475137454382653161600433 := by
  unfold tailWord_6767806
  simp only [CollatzResearch.WordTrace]
  refine ⟨30855270464925273261006409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164561442479601457392034181 30855270464925273261006409)
  ·
    refine ⟨23141452848693954945754807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30855270464925273261006409 23141452848693954945754807)
    ·
      refine ⟨34712179273040932418632211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23141452848693954945754807 34712179273040932418632211)
      ·
        refine ⟨52068268909561398627948317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34712179273040932418632211 52068268909561398627948317)
        ·
          refine ⟨19525600841085524485480619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52068268909561398627948317 19525600841085524485480619)
          ·
            refine ⟨29288401261628286728220929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19525600841085524485480619 29288401261628286728220929)
            ·
              refine ⟨21966300946221215046165697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29288401261628286728220929 21966300946221215046165697)
              ·
                refine ⟨16474725709665911284624273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21966300946221215046165697 16474725709665911284624273)
                ·
                  refine ⟨12356044282249433463468205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16474725709665911284624273 12356044282249433463468205)
                  ·
                    refine ⟨4633516605843537548800577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12356044282249433463468205 4633516605843537548800577)
                    ·
                      refine ⟨3475137454382653161600433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633516605843537548800577 3475137454382653161600433)
                      ·
                        rfl

theorem cell23_6767806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_6767806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767806 prefixEnd_6767806 := by exact prefixLift 6767806
  have htrace : WordTrace (prefixWord ++ tailWord_6767806) baseStart_6767806 baseEnd_6767806 := by
    simpa [prefixWord, tailWord_6767806, baseEnd_6767806] using wordTrace_append hprefix tailTrace_6767806
  have hstable : (prefixWord ++ tailWord_6767806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767806).length < 2 ^ (prefixWord ++ tailWord_6767806).sum := by decide
  have hdescent : baseEnd_6767806 < baseStart_6767806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767815 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_6767815 : Nat := 118140960795 + 6767815 * 2 ^ 59
def prefixEnd_6767815 : Nat := 4983230072969 + 3 ^ 40 * 6767815 * 2
def baseEnd_6767815 : Nat := 3475142075708543626387891

theorem tailTrace_6767815 : CollatzResearch.WordTrace tailWord_6767815 prefixEnd_6767815 3475142075708543626387891 := by
  unfold tailWord_6767815
  simp only [CollatzResearch.WordTrace]
  refine ⟨246842491976369580625128899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164561661317579720416752599 246842491976369580625128899)
  ·
    refine ⟨370263737964554370937693349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246842491976369580625128899 370263737964554370937693349)
    ·
      refine ⟨69424450868353944550817503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370263737964554370937693349 69424450868353944550817503)
      ·
        refine ⟨104136676302530916826226255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69424450868353944550817503 104136676302530916826226255)
        ·
          refine ⟨156205014453796375239339383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104136676302530916826226255 156205014453796375239339383)
          ·
            refine ⟨234307521680694562859009075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156205014453796375239339383 234307521680694562859009075)
            ·
              refine ⟨351461282521041844288513613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234307521680694562859009075 351461282521041844288513613)
              ·
                refine ⟨131797980945390691608192605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351461282521041844288513613 131797980945390691608192605)
                ·
                  refine ⟨49424242854521509353072227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131797980945390691608192605 49424242854521509353072227)
                  ·
                    refine ⟨74136364281782264029608341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49424242854521509353072227 74136364281782264029608341)
                    ·
                      refine ⟨3475142075708543626387891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74136364281782264029608341 3475142075708543626387891)
                      ·
                        rfl

theorem cell23_6767815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_6767815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767815 prefixEnd_6767815 := by exact prefixLift 6767815
  have htrace : WordTrace (prefixWord ++ tailWord_6767815) baseStart_6767815 baseEnd_6767815 := by
    simpa [prefixWord, tailWord_6767815, baseEnd_6767815] using wordTrace_append hprefix tailTrace_6767815
  have hstable : (prefixWord ++ tailWord_6767815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767815).length < 2 ^ (prefixWord ++ tailWord_6767815).sum := by decide
  have hdescent : baseEnd_6767815 < baseStart_6767815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767829 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_6767829 : Nat := 118140960795 + 6767829 * 2 ^ 59
def prefixEnd_6767829 : Nat := 4983230072969 + 3 ^ 40 * 6767829 * 2
def baseEnd_6767829 : Nat := 1158383088145902190537609

theorem tailTrace_6767829 : CollatzResearch.WordTrace tailWord_6767829 prefixEnd_6767829 1158383088145902190537609 := by
  unfold tailWord_6767829
  simp only [CollatzResearch.WordTrace]
  refine ⟨246843002598318861016138541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164562001732212574010759027 246843002598318861016138541)
  ·
    refine ⟨92566125974369572881051953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246843002598318861016138541 92566125974369572881051953)
    ·
      refine ⟨69424594480777179660788965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92566125974369572881051953 69424594480777179660788965)
      ·
        refine ⟨13017111465145721186397931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69424594480777179660788965 13017111465145721186397931)
        ·
          refine ⟨19525667197718581779596897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13017111465145721186397931 19525667197718581779596897)
          ·
            refine ⟨14644250398288936334697673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19525667197718581779596897 14644250398288936334697673)
            ·
              refine ⟨10983187798716702251023255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14644250398288936334697673 10983187798716702251023255)
              ·
                refine ⟨16474781698075053376534883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10983187798716702251023255 16474781698075053376534883)
                ·
                  refine ⟨24712172547112580064802325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16474781698075053376534883 24712172547112580064802325)
                  ·
                    refine ⟨1158383088145902190537609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24712172547112580064802325 1158383088145902190537609)
                    ·
                      rfl

theorem cell23_6767829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_6767829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767829 prefixEnd_6767829 := by exact prefixLift 6767829
  have htrace : WordTrace (prefixWord ++ tailWord_6767829) baseStart_6767829 baseEnd_6767829 := by
    simpa [prefixWord, tailWord_6767829, baseEnd_6767829] using wordTrace_append hprefix tailTrace_6767829
  have hstable : (prefixWord ++ tailWord_6767829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767829).length < 2 ^ (prefixWord ++ tailWord_6767829).sum := by decide
  have hdescent : baseEnd_6767829 < baseStart_6767829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767853 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_6767853 : Nat := 118140960795 + 6767853 * 2 ^ 59
def prefixEnd_6767853 : Nat := 4983230072969 + 3 ^ 40 * 6767853 * 2
def baseEnd_6767853 : Nat := 3475161587973414477712717

theorem tailTrace_6767853 : CollatzResearch.WordTrace tailWord_6767853 prefixEnd_6767853 3475161587973414477712717 := by
  unfold tailWord_6767853
  simp only [CollatzResearch.WordTrace]
  refine ⟨246843877950231913115012213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164562585300154608743341475 246843877950231913115012213)
  ·
    refine ⟨23141613557834241854532395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246843877950231913115012213 23141613557834241854532395)
    ·
      refine ⟨34712420336751362781798593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23141613557834241854532395 34712420336751362781798593)
      ·
        refine ⟨26034315252563522086348945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34712420336751362781798593 26034315252563522086348945)
        ·
          refine ⟨19525736439422641564761709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26034315252563522086348945 19525736439422641564761709)
          ·
            refine ⟨7322151164783490586785641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19525736439422641564761709 7322151164783490586785641)
            ·
              refine ⟨5491613373587617940089231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7322151164783490586785641 5491613373587617940089231)
              ·
                refine ⟨8237420060381426910133847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491613373587617940089231 8237420060381426910133847)
                ·
                  refine ⟨12356130090572140365200771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237420060381426910133847 12356130090572140365200771)
                  ·
                    refine ⟨18534195135858210547801157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12356130090572140365200771 18534195135858210547801157)
                    ·
                      refine ⟨3475161587973414477712717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18534195135858210547801157 3475161587973414477712717)
                      ·
                        rfl

theorem cell23_6767853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_6767853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767853 prefixEnd_6767853 := by exact prefixLift 6767853
  have htrace : WordTrace (prefixWord ++ tailWord_6767853) baseStart_6767853 baseEnd_6767853 := by
    simpa [prefixWord, tailWord_6767853, baseEnd_6767853] using wordTrace_append hprefix tailTrace_6767853
  have hstable : (prefixWord ++ tailWord_6767853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767853).length < 2 ^ (prefixWord ++ tailWord_6767853).sum := by decide
  have hdescent : baseEnd_6767853 < baseStart_6767853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767862 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6767862 : Nat := 118140960795 + 6767862 * 2 ^ 59
def prefixEnd_6767862 : Nat := 4983230072969 + 3 ^ 40 * 6767862 * 2
def baseEnd_6767862 : Nat := 3475166209299304942500175

theorem tailTrace_6767862 : CollatzResearch.WordTrace tailWord_6767862 prefixEnd_6767862 3475166209299304942500175 := by
  unfold tailWord_6767862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15427762887949956728255615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164562804138132871768059893 15427762887949956728255615)
  ·
    refine ⟨23141644331924935092383423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15427762887949956728255615 23141644331924935092383423)
    ·
      refine ⟨34712466497887402638575135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23141644331924935092383423 34712466497887402638575135)
      ·
        refine ⟨52068699746831103957862703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34712466497887402638575135 52068699746831103957862703)
        ·
          refine ⟨78103049620246655936794055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52068699746831103957862703 78103049620246655936794055)
          ·
            refine ⟨117154574430369983905191083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78103049620246655936794055 117154574430369983905191083)
            ·
              refine ⟨175731861645554975857786625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117154574430369983905191083 175731861645554975857786625)
              ·
                refine ⟨131798896234166231893339969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175731861645554975857786625 131798896234166231893339969)
                ·
                  refine ⟨98849172175624673920004977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131798896234166231893339969 98849172175624673920004977)
                  ·
                    refine ⟨74136879131718505440003733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98849172175624673920004977 74136879131718505440003733)
                    ·
                      refine ⟨3475166209299304942500175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74136879131718505440003733 3475166209299304942500175)
                      ·
                        rfl

theorem cell23_6767862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6767862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767862 prefixEnd_6767862 := by exact prefixLift 6767862
  have htrace : WordTrace (prefixWord ++ tailWord_6767862) baseStart_6767862 baseEnd_6767862 := by
    simpa [prefixWord, tailWord_6767862, baseEnd_6767862] using wordTrace_append hprefix tailTrace_6767862
  have hstable : (prefixWord ++ tailWord_6767862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767862).length < 2 ^ (prefixWord ++ tailWord_6767862).sum := by decide
  have hdescent : baseEnd_6767862 < baseStart_6767862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767870 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6767870 : Nat := 118140960795 + 6767870 * 2 ^ 59
def prefixEnd_6767870 : Nat := 4983230072969 + 3 ^ 40 * 6767870 * 2
def baseEnd_6767870 : Nat := 3475170317144540911200139

theorem tailTrace_6767870 : CollatzResearch.WordTrace tailWord_6767870 prefixEnd_6767870 3475170317144540911200139 := by
  unfold tailWord_6767870
  simp only [CollatzResearch.WordTrace]
  refine ⟨30855562248896290627297633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164562998660780216678920709 30855562248896290627297633)
  ·
    refine ⟨23141671686672217970473225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30855562248896290627297633 23141671686672217970473225)
    ·
      refine ⟨17356253765004163477854919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23141671686672217970473225 17356253765004163477854919)
      ·
        refine ⟨26034380647506245216782379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17356253765004163477854919 26034380647506245216782379)
        ·
          refine ⟨39051570971259367825173569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26034380647506245216782379 39051570971259367825173569)
          ·
            refine ⟨29288678228444525868880177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39051570971259367825173569 29288678228444525868880177)
            ·
              refine ⟨21966508671333394401660133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29288678228444525868880177 21966508671333394401660133)
              ·
                refine ⟨4118720375875011450311275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21966508671333394401660133 4118720375875011450311275)
                ·
                  refine ⟨6178080563812517175466913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118720375875011450311275 6178080563812517175466913)
                  ·
                    refine ⟨4633560422859387881600185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178080563812517175466913 4633560422859387881600185)
                    ·
                      refine ⟨3475170317144540911200139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633560422859387881600185 3475170317144540911200139)
                      ·
                        rfl

theorem cell23_6767870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6767870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767870 prefixEnd_6767870 := by exact prefixLift 6767870
  have htrace : WordTrace (prefixWord ++ tailWord_6767870) baseStart_6767870 baseEnd_6767870 := by
    simpa [prefixWord, tailWord_6767870, baseEnd_6767870] using wordTrace_append hprefix tailTrace_6767870
  have hstable : (prefixWord ++ tailWord_6767870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767870).length < 2 ^ (prefixWord ++ tailWord_6767870).sum := by decide
  have hdescent : baseEnd_6767870 < baseStart_6767870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767886 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_6767886 : Nat := 118140960795 + 6767886 * 2 ^ 59
def prefixEnd_6767886 : Nat := 4983230072969 + 3 ^ 40 * 6767886 * 2
def baseEnd_6767886 : Nat := 3475178532835012848600065

theorem tailTrace_6767886 : CollatzResearch.WordTrace tailWord_6767886 prefixEnd_6767886 3475178532835012848600065 := by
  unfold tailWord_6767886
  simp only [CollatzResearch.WordTrace]
  refine ⟨30855635194889044968870439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164563387706074906500642341 30855635194889044968870439)
  ·
    refine ⟨46283452792333567453305659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30855635194889044968870439 46283452792333567453305659)
    ·
      refine ⟨69425179188500351179958489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46283452792333567453305659 69425179188500351179958489)
      ·
        refine ⟨52068884391375263384968867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69425179188500351179958489 52068884391375263384968867)
        ·
          refine ⟨78103326587062895077453301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52068884391375263384968867 78103326587062895077453301)
          ·
            refine ⟨7322186867537146413511247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78103326587062895077453301 7322186867537146413511247)
            ·
              refine ⟨10983280301305719620266871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322186867537146413511247 10983280301305719620266871)
              ·
                refine ⟨16474920451958579430400307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10983280301305719620266871 16474920451958579430400307)
                ·
                  refine ⟨24712380677937869145600461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16474920451958579430400307 24712380677937869145600461)
                  ·
                    refine ⟨9267142754226700929600173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24712380677937869145600461 9267142754226700929600173)
                    ·
                      refine ⟨3475178532835012848600065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267142754226700929600173 3475178532835012848600065)
                      ·
                        rfl

theorem cell23_6767886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_6767886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767886 prefixEnd_6767886 := by exact prefixLift 6767886
  have htrace : WordTrace (prefixWord ++ tailWord_6767886) baseStart_6767886 baseEnd_6767886 := by
    simpa [prefixWord, tailWord_6767886, baseEnd_6767886] using wordTrace_append hprefix tailTrace_6767886
  have hstable : (prefixWord ++ tailWord_6767886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767886).length < 2 ^ (prefixWord ++ tailWord_6767886).sum := by decide
  have hdescent : baseEnd_6767886 < baseStart_6767886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767890 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6767890 : Nat := 118140960795 + 6767890 * 2 ^ 59
def prefixEnd_6767890 : Nat := 4983230072969 + 3 ^ 40 * 6767890 * 2
def baseEnd_6767890 : Nat := 3475180586757630832950047

theorem tailTrace_6767890 : CollatzResearch.WordTrace tailWord_6767890 prefixEnd_6767890 3475180586757630832950047 := by
  unfold tailWord_6767890
  simp only [CollatzResearch.WordTrace]
  refine ⟨61711306862774467108527281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164563484967398578956072749 61711306862774467108527281)
  ·
    refine ⟨46283480147080850331395461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61711306862774467108527281 46283480147080850331395461)
    ·
      refine ⟨8678152527577659437136649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46283480147080850331395461 8678152527577659437136649)
      ·
        refine ⟨6508614395683244577852487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8678152527577659437136649 6508614395683244577852487)
        ·
          refine ⟨9762921593524866866778731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508614395683244577852487 9762921593524866866778731)
          ·
            refine ⟨14644382390287300300168097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762921593524866866778731 14644382390287300300168097)
            ·
              refine ⟨10983286792715475225126073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14644382390287300300168097 10983286792715475225126073)
              ·
                refine ⟨8237465094536606418844555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10983286792715475225126073 8237465094536606418844555)
                ·
                  refine ⟨12356197641804909628266833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237465094536606418844555 12356197641804909628266833)
                  ·
                    refine ⟨9267148231353682221200125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12356197641804909628266833 9267148231353682221200125)
                    ·
                      refine ⟨3475180586757630832950047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267148231353682221200125 3475180586757630832950047)
                      ·
                        rfl

theorem cell23_6767890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6767890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767890 prefixEnd_6767890 := by exact prefixLift 6767890
  have htrace : WordTrace (prefixWord ++ tailWord_6767890) baseStart_6767890 baseEnd_6767890 := by
    simpa [prefixWord, tailWord_6767890, baseEnd_6767890] using wordTrace_append hprefix tailTrace_6767890
  have hstable : (prefixWord ++ tailWord_6767890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767890).length < 2 ^ (prefixWord ++ tailWord_6767890).sum := by decide
  have hdescent : baseEnd_6767890 < baseStart_6767890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767896 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_6767896 : Nat := 118140960795 + 6767896 * 2 ^ 59
def prefixEnd_6767896 : Nat := 4983230072969 + 3 ^ 40 * 6767896 * 2
def baseEnd_6767896 : Nat := 3475183667641557809475019

theorem tailTrace_6767896 : CollatzResearch.WordTrace tailWord_6767896 prefixEnd_6767896 3475183667641557809475019 := by
  unfold tailWord_6767896
  simp only [CollatzResearch.WordTrace]
  refine ⟨123422723144538065729413771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164563630859384087639218361 123422723144538065729413771)
  ·
    refine ⟨185134084716807098594120657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123422723144538065729413771 185134084716807098594120657)
    ·
      refine ⟨138850563537605323945590493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185134084716807098594120657 138850563537605323945590493)
      ·
        refine ⟨52068961326601996479596435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138850563537605323945590493 52068961326601996479596435)
        ·
          refine ⟨78103441989902994719394653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52068961326601996479596435 78103441989902994719394653)
          ·
            refine ⟨29288790746213623019772995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78103441989902994719394653 29288790746213623019772995)
            ·
              refine ⟨43933186119320434529659493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29288790746213623019772995 43933186119320434529659493)
              ·
                refine ⟨8237472397372581474311155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43933186119320434529659493 8237472397372581474311155)
                ·
                  refine ⟨12356208596058872211466733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237472397372581474311155 12356208596058872211466733)
                  ·
                    refine ⟨4633578223522077079300025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12356208596058872211466733 4633578223522077079300025)
                    ·
                      refine ⟨3475183667641557809475019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633578223522077079300025 3475183667641557809475019)
                      ·
                        rfl

theorem cell23_6767896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_6767896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767896 prefixEnd_6767896 := by exact prefixLift 6767896
  have htrace : WordTrace (prefixWord ++ tailWord_6767896) baseStart_6767896 baseEnd_6767896 := by
    simpa [prefixWord, tailWord_6767896, baseEnd_6767896] using wordTrace_append hprefix tailTrace_6767896
  have hstable : (prefixWord ++ tailWord_6767896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767896).length < 2 ^ (prefixWord ++ tailWord_6767896).sum := by decide
  have hdescent : baseEnd_6767896 < baseStart_6767896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767943 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_6767943 : Nat := 118140960795 + 6767943 * 2 ^ 59
def prefixEnd_6767943 : Nat := 4983230072969 + 3 ^ 40 * 6767943 * 2
def baseEnd_6767943 : Nat := 3475207801232319125587303

theorem tailTrace_6767943 : CollatzResearch.WordTrace tailWord_6767943 prefixEnd_6767943 3475207801232319125587303 := by
  unfold tailWord_6767943
  simp only [CollatzResearch.WordTrace]
  refine ⟨246847160519905858485788483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164564773679937238990525655 246847160519905858485788483)
  ·
    refine ⟨370270740779858787728682725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246847160519905858485788483 370270740779858787728682725)
    ·
      refine ⟨69425763896223522699128011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370270740779858787728682725 69425763896223522699128011)
      ·
        refine ⟨104138645844335284048692017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69425763896223522699128011 104138645844335284048692017)
        ·
          refine ⟨78103984383251463036519013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104138645844335284048692017 78103984383251463036519013)
          ·
            refine ⟨14644497071859649319347315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78103984383251463036519013 14644497071859649319347315)
            ·
              refine ⟨21966745607789473979020973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14644497071859649319347315 21966745607789473979020973)
              ·
                refine ⟨8237529602921052742132865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21966745607789473979020973 8237529602921052742132865)
                ·
                  refine ⟨6178147202190789556599649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8237529602921052742132865 6178147202190789556599649)
                  ·
                    refine ⟨4633610401643092167449737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178147202190789556599649 4633610401643092167449737)
                    ·
                      refine ⟨3475207801232319125587303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633610401643092167449737 3475207801232319125587303)
                      ·
                        rfl

theorem cell23_6767943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_6767943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767943 prefixEnd_6767943 := by exact prefixLift 6767943
  have htrace : WordTrace (prefixWord ++ tailWord_6767943) baseStart_6767943 baseEnd_6767943 := by
    simpa [prefixWord, tailWord_6767943, baseEnd_6767943] using wordTrace_append hprefix tailTrace_6767943
  have hstable : (prefixWord ++ tailWord_6767943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767943).length < 2 ^ (prefixWord ++ tailWord_6767943).sum := by decide
  have hdescent : baseEnd_6767943 < baseStart_6767943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767962 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_6767962 : Nat := 118140960795 + 6767962 * 2 ^ 59
def prefixEnd_6767962 : Nat := 4983230072969 + 3 ^ 40 * 6767962 * 2
def baseEnd_6767962 : Nat := 1158405852454918183749905

theorem tailTrace_6767962 : CollatzResearch.WordTrace tailWord_6767962 prefixEnd_6767962 1158405852454918183749905 := by
  unfold tailWord_6767962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61711963376709256182682535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164565235671224683153820093 61711963376709256182682535)
  ·
    refine ⟨92567945065063884274023803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61711963376709256182682535 92567945065063884274023803)
    ·
      refine ⟨138851917597595826411035705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92567945065063884274023803 138851917597595826411035705)
      ·
        refine ⟨104138938198196869808276779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138851917597595826411035705 104138938198196869808276779)
        ·
          refine ⟨156208407297295304712415169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104138938198196869808276779 156208407297295304712415169)
          ·
            refine ⟨117156305472971478534311377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156208407297295304712415169 117156305472971478534311377)
            ·
              refine ⟨87867229104728608900733533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117156305472971478534311377 87867229104728608900733533)
              ·
                refine ⟨32950210914273228337775075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87867229104728608900733533 32950210914273228337775075)
                ·
                  refine ⟨49425316371409842506662613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32950210914273228337775075 49425316371409842506662613)
                  ·
                    refine ⟨1158405852454918183749905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49425316371409842506662613 1158405852454918183749905)
                    ·
                      rfl

theorem cell23_6767962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_6767962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767962 prefixEnd_6767962 := by exact prefixLift 6767962
  have htrace : WordTrace (prefixWord ++ tailWord_6767962) baseStart_6767962 baseEnd_6767962 := by
    simpa [prefixWord, tailWord_6767962, baseEnd_6767962] using wordTrace_append hprefix tailTrace_6767962
  have hstable : (prefixWord ++ tailWord_6767962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767962).length < 2 ^ (prefixWord ++ tailWord_6767962).sum := by decide
  have hdescent : baseEnd_6767962 < baseStart_6767962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6767969 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_6767969 : Nat := 118140960795 + 6767969 * 2 ^ 59
def prefixEnd_6767969 : Nat := 4983230072969 + 3 ^ 40 * 6767969 * 2
def baseEnd_6767969 : Nat := 3475221151729336023862183

theorem tailTrace_6767969 : CollatzResearch.WordTrace tailWord_6767969 prefixEnd_6767969 3475221151729336023862183 := by
  unfold tailWord_6767969
  simp only [CollatzResearch.WordTrace]
  refine ⟨246848108817811664926234961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164565405878541109950823307 246848108817811664926234961)
  ·
    refine ⟨185136081613358748694676221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246848108817811664926234961 185136081613358748694676221)
    ·
      refine ⟨69426030605009530760503583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185136081613358748694676221 69426030605009530760503583)
      ·
        refine ⟨104139045907514296140755375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69426030605009530760503583 104139045907514296140755375)
        ·
          refine ⟨156208568861271444211133063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104139045907514296140755375 156208568861271444211133063)
          ·
            refine ⟨234312853291907166316699595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156208568861271444211133063 234312853291907166316699595)
            ·
              refine ⟨351469279937860749475049393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234312853291907166316699595 351469279937860749475049393)
              ·
                refine ⟨263601959953395562106287045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351469279937860749475049393 263601959953395562106287045)
                ·
                  refine ⟨49425367491261667894928821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263601959953395562106287045 49425367491261667894928821)
                  ·
                    refine ⟨4633628202305781365149577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49425367491261667894928821 4633628202305781365149577)
                    ·
                      refine ⟨3475221151729336023862183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633628202305781365149577 3475221151729336023862183)
                      ·
                        rfl

theorem cell23_6767969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_6767969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6767969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6767969 prefixEnd_6767969 := by exact prefixLift 6767969
  have htrace : WordTrace (prefixWord ++ tailWord_6767969) baseStart_6767969 baseEnd_6767969 := by
    simpa [prefixWord, tailWord_6767969, baseEnd_6767969] using wordTrace_append hprefix tailTrace_6767969
  have hstable : (prefixWord ++ tailWord_6767969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6767969).length < 2 ^ (prefixWord ++ tailWord_6767969).sum := by decide
  have hdescent : baseEnd_6767969 < baseStart_6767969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6767969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768029 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6768029 : Nat := 118140960795 + 6768029 * 2 ^ 59
def prefixEnd_6768029 : Nat := 4983230072969 + 3 ^ 40 * 6768029 * 2
def baseEnd_6768029 : Nat := 3475251960568605789111907

theorem tailTrace_6768029 : CollatzResearch.WordTrace tailWord_6768029 prefixEnd_6768029 3475251960568605789111907 := by
  unfold tailWord_6768029
  simp only [CollatzResearch.WordTrace]
  refine ⟨246850297197594295173419141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164566864798396196782279427 246850297197594295173419141)
  ·
    refine ⟨46284430724548930345016089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246850297197594295173419141 46284430724548930345016089)
    ·
      refine ⟨34713323043411697758762067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46284430724548930345016089 34713323043411697758762067)
      ·
        refine ⟨52069984565117546638143101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34713323043411697758762067 52069984565117546638143101)
        ·
          refine ⟨19526244211919079989303663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52069984565117546638143101 19526244211919079989303663)
          ·
            refine ⟨29289366317878619983955495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19526244211919079989303663 29289366317878619983955495)
            ·
              refine ⟨43934049476817929975933243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29289366317878619983955495 43934049476817929975933243)
              ·
                refine ⟨65901074215226894963899865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43934049476817929975933243 65901074215226894963899865)
                ·
                  refine ⟨49425805661420171222924899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65901074215226894963899865 49425805661420171222924899)
                  ·
                    refine ⟨74138708492130256834387349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49425805661420171222924899 74138708492130256834387349)
                    ·
                      refine ⟨3475251960568605789111907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74138708492130256834387349 3475251960568605789111907)
                      ·
                        rfl

theorem cell23_6768029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6768029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768029 prefixEnd_6768029 := by exact prefixLift 6768029
  have htrace : WordTrace (prefixWord ++ tailWord_6768029) baseStart_6768029 baseEnd_6768029 := by
    simpa [prefixWord, tailWord_6768029, baseEnd_6768029] using wordTrace_append hprefix tailTrace_6768029
  have hstable : (prefixWord ++ tailWord_6768029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768029).length < 2 ^ (prefixWord ++ tailWord_6768029).sum := by decide
  have hdescent : baseEnd_6768029 < baseStart_6768029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768039 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 8]
def baseStart_6768039 : Nat := 118140960795 + 6768039 * 2 ^ 59
def prefixEnd_6768039 : Nat := 4983230072969 + 3 ^ 40 * 6768039 * 2
def baseEnd_6768039 : Nat := 386139677263905638887429

theorem tailTrace_6768039 : CollatzResearch.WordTrace tailWord_6768039 prefixEnd_6768039 386139677263905638887429 := by
  unfold tailWord_6768039
  simp only [CollatzResearch.WordTrace]
  refine ⟨246850661927558066881283171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164567107951705377920855447 246850661927558066881283171)
  ·
    refine ⟨370275992891337100321924757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246850661927558066881283171 370275992891337100321924757)
    ·
      refine ⟨17356687166781426577590223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370275992891337100321924757 17356687166781426577590223)
      ·
        refine ⟨26035030750172139866385335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17356687166781426577590223 26035030750172139866385335)
        ·
          refine ⟨39052546125258209799578003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26035030750172139866385335 39052546125258209799578003)
          ·
            refine ⟨58578819187887314699367005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39052546125258209799578003 58578819187887314699367005)
            ·
              refine ⟨21967057195457743012262627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58578819187887314699367005 21967057195457743012262627)
              ·
                refine ⟨32950585793186614518393941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21967057195457743012262627 32950585793186614518393941)
                ·
                  refine ⟨386139677263905638887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32950585793186614518393941 386139677263905638887429)
                  ·
                    rfl

theorem cell23_6768039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 8].length) (baseStart_6768039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768039 prefixEnd_6768039 := by exact prefixLift 6768039
  have htrace : WordTrace (prefixWord ++ tailWord_6768039) baseStart_6768039 baseEnd_6768039 := by
    simpa [prefixWord, tailWord_6768039, baseEnd_6768039] using wordTrace_append hprefix tailTrace_6768039
  have hstable : (prefixWord ++ tailWord_6768039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768039).length < 2 ^ (prefixWord ++ tailWord_6768039).sum := by decide
  have hdescent : baseEnd_6768039 < baseStart_6768039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768093 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_6768093 : Nat := 118140960795 + 6768093 * 2 ^ 59
def prefixEnd_6768093 : Nat := 4983230072969 + 3 ^ 40 * 6768093 * 2
def baseEnd_6768093 : Nat := 3475284823330493538711613

theorem tailTrace_6768093 : CollatzResearch.WordTrace tailWord_6768093 prefixEnd_6768093 3475284823330493538711613 := by
  unfold tailWord_6768093
  simp only [CollatzResearch.WordTrace]
  refine ⟨246852631469362434103748933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164568420979574956069165955 246852631469362434103748933)
  ·
    refine ⟨46284868400505456394452925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246852631469362434103748933 46284868400505456394452925)
    ·
      refine ⟨17356825650189546147919847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46284868400505456394452925 17356825650189546147919847)
      ·
        refine ⟨26035238475284319221879771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17356825650189546147919847 26035238475284319221879771)
        ·
          refine ⟨39052857712926478832819657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26035238475284319221879771 39052857712926478832819657)
          ·
            refine ⟨29289643284694859124614743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39052857712926478832819657 29289643284694859124614743)
            ·
              refine ⟨43934464927042288686922115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29289643284694859124614743 43934464927042288686922115)
              ·
                refine ⟨65901697390563433030383173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43934464927042288686922115 65901697390563433030383173)
                ·
                  refine ⟨12356568260730643693196845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65901697390563433030383173 12356568260730643693196845)
                  ·
                    refine ⟨4633713097773991384948817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12356568260730643693196845 4633713097773991384948817)
                    ·
                      refine ⟨3475284823330493538711613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633713097773991384948817 3475284823330493538711613)
                      ·
                        rfl

theorem cell23_6768093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_6768093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768093 prefixEnd_6768093 := by exact prefixLift 6768093
  have htrace : WordTrace (prefixWord ++ tailWord_6768093) baseStart_6768093 baseEnd_6768093 := by
    simpa [prefixWord, tailWord_6768093, baseEnd_6768093] using wordTrace_append hprefix tailTrace_6768093
  have hstable : (prefixWord ++ tailWord_6768093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768093).length < 2 ^ (prefixWord ++ tailWord_6768093).sum := by decide
  have hdescent : baseEnd_6768093 < baseStart_6768093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768140 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_6768140 : Nat := 118140960795 + 6768140 * 2 ^ 59
def prefixEnd_6768140 : Nat := 4983230072969 + 3 ^ 40 * 6768140 * 2
def baseEnd_6768140 : Nat := 3475308956921254854823897

theorem tailTrace_6768140 : CollatzResearch.WordTrace tailWord_6768140 prefixEnd_6768140 3475308956921254854823897 := by
  unfold tailWord_6768140
  simp only [CollatzResearch.WordTrace]
  refine ⟨123427172850096080565354937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164569563800128107420473249 123427172850096080565354937)
  ·
    refine ⟨92570379637572060424016203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123427172850096080565354937 92570379637572060424016203)
    ·
      refine ⟨138855569456358090636024305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92570379637572060424016203 138855569456358090636024305)
      ·
        refine ⟨104141677092268567977018229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138855569456358090636024305 104141677092268567977018229)
        ·
          refine ⟨9763282227400178247845459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104141677092268567977018229 9763282227400178247845459)
          ·
            refine ⟨14644923341100267371768189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9763282227400178247845459 14644923341100267371768189)
            ·
              refine ⟨5491846252912600264413071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14644923341100267371768189 5491846252912600264413071)
              ·
                refine ⟨8237769379368900396619607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491846252912600264413071 8237769379368900396619607)
                ·
                  refine ⟨12356654069053350594929411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8237769379368900396619607 12356654069053350594929411)
                  ·
                    refine ⟨18534981103580025892394117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12356654069053350594929411 18534981103580025892394117)
                    ·
                      refine ⟨3475308956921254854823897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18534981103580025892394117 3475308956921254854823897)
                      ·
                        rfl

theorem cell23_6768140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_6768140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768140 prefixEnd_6768140 := by exact prefixLift 6768140
  have htrace : WordTrace (prefixWord ++ tailWord_6768140) baseStart_6768140 baseEnd_6768140 := by
    simpa [prefixWord, tailWord_6768140, baseEnd_6768140] using wordTrace_append hprefix tailTrace_6768140
  have hstable : (prefixWord ++ tailWord_6768140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768140).length < 2 ^ (prefixWord ++ tailWord_6768140).sum := by decide
  have hdescent : baseEnd_6768140 < baseStart_6768140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768156 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6768156 : Nat := 118140960795 + 6768156 * 2 ^ 59
def prefixEnd_6768156 : Nat := 4983230072969 + 3 ^ 40 * 6768156 * 2
def baseEnd_6768156 : Nat := 3475317172611726792223823

theorem tailTrace_6768156 : CollatzResearch.WordTrace tailWord_6768156 prefixEnd_6768156 3475317172611726792223823 := by
  unfold tailWord_6768156
  simp only [CollatzResearch.WordTrace]
  refine ⟨123427464634067097931646161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164569952845422797242194881 123427464634067097931646161)
  ·
    refine ⟨92570598475550323448734621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123427464634067097931646161 92570598475550323448734621)
    ·
      refine ⟨34713974428331371293275483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92570598475550323448734621 34713974428331371293275483)
      ·
        refine ⟨52070961642497056939913225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34713974428331371293275483 52070961642497056939913225)
        ·
          refine ⟨39053221231872792704934919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52070961642497056939913225 39053221231872792704934919)
          ·
            refine ⟨58579831847809189057402379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39053221231872792704934919 58579831847809189057402379)
            ·
              refine ⟨87869747771713783586103569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58579831847809189057402379 87869747771713783586103569)
              ·
                refine ⟨65902310828785337689577677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87869747771713783586103569 65902310828785337689577677)
                ·
                  refine ⟨24713366560794501633591629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65902310828785337689577677 24713366560794501633591629)
                  ·
                    refine ⟨9267512460297938112596861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24713366560794501633591629 9267512460297938112596861)
                    ·
                      refine ⟨3475317172611726792223823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267512460297938112596861 3475317172611726792223823)
                      ·
                        rfl

theorem cell23_6768156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6768156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768156 prefixEnd_6768156 := by exact prefixLift 6768156
  have htrace : WordTrace (prefixWord ++ tailWord_6768156) baseStart_6768156 baseEnd_6768156 := by
    simpa [prefixWord, tailWord_6768156, baseEnd_6768156] using wordTrace_append hprefix tailTrace_6768156
  have hstable : (prefixWord ++ tailWord_6768156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768156).length < 2 ^ (prefixWord ++ tailWord_6768156).sum := by decide
  have hdescent : baseEnd_6768156 < baseStart_6768156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768157 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_6768157 : Nat := 118140960795 + 6768157 * 2 ^ 59
def prefixEnd_6768157 : Nat := 4983230072969 + 3 ^ 40 * 6768157 * 2
def baseEnd_6768157 : Nat := 3475317686092381288311319

theorem tailTrace_6768157 : CollatzResearch.WordTrace tailWord_6768157 prefixEnd_6768157 3475317686092381288311319 := by
  unfold tailWord_6768157
  simp only [CollatzResearch.WordTrace]
  refine ⟨246854965741130573034078725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164569977160753715356052483 246854965741130573034078725)
  ·
    refine ⟨46285306076461982443889761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246854965741130573034078725 46285306076461982443889761)
    ·
      refine ⟨34713979557346486832917321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46285306076461982443889761 34713979557346486832917321)
      ·
        refine ⟨26035484668009865124687991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34713979557346486832917321 26035484668009865124687991)
        ·
          refine ⟨39053227002014797687031987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26035484668009865124687991 39053227002014797687031987)
          ·
            refine ⟨58579840503022196530547981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39053227002014797687031987 58579840503022196530547981)
            ·
              refine ⟨21967440188633323698955493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58579840503022196530547981 21967440188633323698955493)
              ·
                refine ⟨4118895035368748193554155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21967440188633323698955493 4118895035368748193554155)
                ·
                  refine ⟨6178342553053122290331233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118895035368748193554155 6178342553053122290331233)
                  ·
                    refine ⟨4633756914789841717748425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178342553053122290331233 4633756914789841717748425)
                    ·
                      refine ⟨3475317686092381288311319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633756914789841717748425 3475317686092381288311319)
                      ·
                        rfl

theorem cell23_6768157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_6768157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768157 prefixEnd_6768157 := by exact prefixLift 6768157
  have htrace : WordTrace (prefixWord ++ tailWord_6768157) baseStart_6768157 baseEnd_6768157 := by
    simpa [prefixWord, tailWord_6768157, baseEnd_6768157] using wordTrace_append hprefix tailTrace_6768157
  have hstable : (prefixWord ++ tailWord_6768157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768157).length < 2 ^ (prefixWord ++ tailWord_6768157).sum := by decide
  have hdescent : baseEnd_6768157 < baseStart_6768157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768159 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 7]
def baseStart_6768159 : Nat := 118140960795 + 6768159 * 2 ^ 59
def prefixEnd_6768159 : Nat := 4983230072969 + 3 ^ 40 * 6768159 * 2
def baseEnd_6768159 : Nat := 1158439571017896760162103

theorem tailTrace_6768159 : CollatzResearch.WordTrace tailWord_6768159 prefixEnd_6768159 1158439571017896760162103 := by
  unfold tailWord_6768159
  simp only [CollatzResearch.WordTrace]
  refine ⟨246855038687123327375651531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164570025791415551583767687 246855038687123327375651531)
  ·
    refine ⟨370282558030684991063477297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246855038687123327375651531 370282558030684991063477297)
    ·
      refine ⟨277711918523013743297607973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370282558030684991063477297 277711918523013743297607973)
      ·
        refine ⟨52070984723065076868301495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277711918523013743297607973 52070984723065076868301495)
        ·
          refine ⟨78106477084597615302452243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52070984723065076868301495 78106477084597615302452243)
          ·
            refine ⟨117159715626896422953678365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78106477084597615302452243 117159715626896422953678365)
            ·
              refine ⟨43934893360086158607629387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117159715626896422953678365 43934893360086158607629387)
              ·
                refine ⟨65902340040129237911444081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43934893360086158607629387 65902340040129237911444081)
                ·
                  refine ⟨49426755030096928433583061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65902340040129237911444081 49426755030096928433583061)
                  ·
                    refine ⟨1158439571017896760162103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49426755030096928433583061 1158439571017896760162103)
                    ·
                      rfl

theorem cell23_6768159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_6768159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768159 prefixEnd_6768159 := by exact prefixLift 6768159
  have htrace : WordTrace (prefixWord ++ tailWord_6768159) baseStart_6768159 baseEnd_6768159 := by
    simpa [prefixWord, tailWord_6768159, baseEnd_6768159] using wordTrace_append hprefix tailTrace_6768159
  have hstable : (prefixWord ++ tailWord_6768159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768159).length < 2 ^ (prefixWord ++ tailWord_6768159).sum := by decide
  have hdescent : baseEnd_6768159 < baseStart_6768159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768163 : List Nat := [1, 1, 1, 4, 6, 1, 1, 8]
def baseStart_6768163 : Nat := 118140960795 + 6768163 * 2 ^ 59
def prefixEnd_6768163 : Nat := 4983230072969 + 3 ^ 40 * 6768163 * 2
def baseEnd_6768163 : Nat := 128715583962085491290233

theorem tailTrace_6768163 : CollatzResearch.WordTrace tailWord_6768163 prefixEnd_6768163 128715583962085491290233 := by
  unfold tailWord_6768163
  simp only [CollatzResearch.WordTrace]
  refine ⟨246855184579108836058797143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164570123052739224039198095 246855184579108836058797143)
  ·
    refine ⟨370282776868663254088195715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246855184579108836058797143 370282776868663254088195715)
    ·
      refine ⟨555424165302994881132293573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370282776868663254088195715 555424165302994881132293573)
      ·
        refine ⟨104142030994311540212305045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555424165302994881132293573 104142030994311540212305045)
        ·
          refine ⟨4881657702858353447451799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104142030994311540212305045 4881657702858353447451799)
          ·
            refine ⟨7322486554287530171177699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881657702858353447451799 7322486554287530171177699)
            ·
              refine ⟨10983729831431295256766549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322486554287530171177699 10983729831431295256766549)
              ·
                refine ⟨128715583962085491290233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10983729831431295256766549 128715583962085491290233)
                ·
                  rfl

theorem cell23_6768163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 8].length) (baseStart_6768163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768163 prefixEnd_6768163 := by exact prefixLift 6768163
  have htrace : WordTrace (prefixWord ++ tailWord_6768163) baseStart_6768163 baseEnd_6768163 := by
    simpa [prefixWord, tailWord_6768163, baseEnd_6768163] using wordTrace_append hprefix tailTrace_6768163
  have hstable : (prefixWord ++ tailWord_6768163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768163).length < 2 ^ (prefixWord ++ tailWord_6768163).sum := by decide
  have hdescent : baseEnd_6768163 < baseStart_6768163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768183 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_6768183 : Nat := 118140960795 + 6768183 * 2 ^ 59
def prefixEnd_6768183 : Nat := 4983230072969 + 3 ^ 40 * 6768183 * 2
def baseEnd_6768183 : Nat := 3475331036589398186586199

theorem tailTrace_6768183 : CollatzResearch.WordTrace tailWord_6768183 prefixEnd_6768183 3475331036589398186586199 := by
  unfold tailWord_6768183
  simp only [CollatzResearch.WordTrace]
  refine ⟨246855914039036379474525203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164570609359357586316350135 246855914039036379474525203)
  ·
    refine ⟨370283871058554569211787805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246855914039036379474525203 370283871058554569211787805)
    ·
      refine ⟨138856451646957963454420427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370283871058554569211787805 138856451646957963454420427)
      ·
        refine ⟨208284677470436945181630641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138856451646957963454420427 208284677470436945181630641)
        ·
          refine ⟨156213508102827708886222981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208284677470436945181630641 156213508102827708886222981)
          ·
            refine ⟨29290032769280195416166809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156213508102827708886222981 29290032769280195416166809)
            ·
              refine ⟨21967524576960146562125107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29290032769280195416166809 21967524576960146562125107)
              ·
                refine ⟨32951286865440219843187661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21967524576960146562125107 32951286865440219843187661)
                ·
                  refine ⟨12356732574540082441195373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32951286865440219843187661 12356732574540082441195373)
                  ·
                    refine ⟨4633774715452530915448265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12356732574540082441195373 4633774715452530915448265)
                    ·
                      refine ⟨3475331036589398186586199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633774715452530915448265 3475331036589398186586199)
                      ·
                        rfl

theorem cell23_6768183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_6768183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768183 prefixEnd_6768183 := by exact prefixLift 6768183
  have htrace : WordTrace (prefixWord ++ tailWord_6768183) baseStart_6768183 baseEnd_6768183 := by
    simpa [prefixWord, tailWord_6768183, baseEnd_6768183] using wordTrace_append hprefix tailTrace_6768183
  have hstable : (prefixWord ++ tailWord_6768183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768183).length < 2 ^ (prefixWord ++ tailWord_6768183).sum := by decide
  have hdescent : baseEnd_6768183 < baseStart_6768183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768303 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_6768303 : Nat := 118140960795 + 6768303 * 2 ^ 59
def prefixEnd_6768303 : Nat := 4983230072969 + 3 ^ 40 * 6768303 * 2
def baseEnd_6768303 : Nat := 3475392654267937717085647

theorem tailTrace_6768303 : CollatzResearch.WordTrace tailWord_6768303 prefixEnd_6768303 3475392654267937717085647 := by
  unfold tailWord_6768303
  simp only [CollatzResearch.WordTrace]
  refine ⟨246860290798601639968893563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164573527199067759979262375 246860290798601639968893563)
  ·
    refine ⟨370290436197902459953340345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246860290798601639968893563 370290436197902459953340345)
    ·
      refine ⟨277717827148426844965005259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370290436197902459953340345 277717827148426844965005259)
      ·
        refine ⟨416576740722640267447507889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277717827148426844965005259 416576740722640267447507889)
        ·
          refine ⟨312432555541980200585630917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416576740722640267447507889 312432555541980200585630917)
          ·
            refine ⟨58581104164121287609805797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312432555541980200585630917 58581104164121287609805797)
            ·
              refine ⟨10983957030772741426838587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58581104164121287609805797 10983957030772741426838587)
              ·
                refine ⟨16475935546159112140257881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10983957030772741426838587 16475935546159112140257881)
                ·
                  refine ⟨12356951659619334105193411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16475935546159112140257881 12356951659619334105193411)
                  ·
                    refine ⟨18535427489429001157790117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12356951659619334105193411 18535427489429001157790117)
                    ·
                      refine ⟨3475392654267937717085647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18535427489429001157790117 3475392654267937717085647)
                      ·
                        rfl

theorem cell23_6768303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_6768303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768303 prefixEnd_6768303 := by exact prefixLift 6768303
  have htrace : WordTrace (prefixWord ++ tailWord_6768303) baseStart_6768303 baseEnd_6768303 := by
    simpa [prefixWord, tailWord_6768303, baseEnd_6768303] using wordTrace_append hprefix tailTrace_6768303
  have hstable : (prefixWord ++ tailWord_6768303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768303).length < 2 ^ (prefixWord ++ tailWord_6768303).sum := by decide
  have hdescent : baseEnd_6768303 < baseStart_6768303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768310 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6768310 : Nat := 118140960795 + 6768310 * 2 ^ 59
def prefixEnd_6768310 : Nat := 4983230072969 + 3 ^ 40 * 6768310 * 2
def baseEnd_6768310 : Nat := 3475396248632519189698115

theorem tailTrace_6768310 : CollatzResearch.WordTrace tailWord_6768310 prefixEnd_6768310 3475396248632519189698115 := by
  unfold tailWord_6768310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428784131848517510274899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164573697406384186776265589 15428784131848517510274899)
  ·
    refine ⟨23143176197772776265412349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15428784131848517510274899 23143176197772776265412349)
    ·
      refine ⟨8678691074164791099529631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23143176197772776265412349 8678691074164791099529631)
      ·
        refine ⟨13018036611247186649294447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678691074164791099529631 13018036611247186649294447)
        ·
          refine ⟨19527054916870779973941671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13018036611247186649294447 19527054916870779973941671)
          ·
            refine ⟨29290582375306169960912507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19527054916870779973941671 29290582375306169960912507)
            ·
              refine ⟨43935873562959254941368761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29290582375306169960912507 43935873562959254941368761)
              ·
                refine ⟨32951905172219441206026571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43935873562959254941368761 32951905172219441206026571)
                ·
                  refine ⟨49427857758329161809039857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32951905172219441206026571 49427857758329161809039857)
                  ·
                    refine ⟨37070893318746871356779893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49427857758329161809039857 37070893318746871356779893)
                    ·
                      refine ⟨3475396248632519189698115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37070893318746871356779893 3475396248632519189698115)
                      ·
                        rfl

theorem cell23_6768310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6768310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768310 prefixEnd_6768310 := by exact prefixLift 6768310
  have htrace : WordTrace (prefixWord ++ tailWord_6768310) baseStart_6768310 baseEnd_6768310 := by
    simpa [prefixWord, tailWord_6768310, baseEnd_6768310] using wordTrace_append hprefix tailTrace_6768310
  have hstable : (prefixWord ++ tailWord_6768310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768310).length < 2 ^ (prefixWord ++ tailWord_6768310).sum := by decide
  have hdescent : baseEnd_6768310 < baseStart_6768310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768370 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_6768370 : Nat := 118140960795 + 6768370 * 2 ^ 59
def prefixEnd_6768370 : Nat := 4983230072969 + 3 ^ 40 * 6768370 * 2
def baseEnd_6768370 : Nat := 3475427057471788954947839

theorem tailTrace_6768370 : CollatzResearch.WordTrace tailWord_6768370 prefixEnd_6768370 3475427057471788954947839 := by
  unfold tailWord_6768370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61715683622339727602895641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164575156326239273607721709 61715683622339727602895641)
  ·
    refine ⟨46286762716754795702171731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61715683622339727602895641 46286762716754795702171731)
    ·
      refine ⟨69430144075132193553257597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46286762716754795702171731 69430144075132193553257597)
      ·
        refine ⟨26036304028174572582471599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69430144075132193553257597 26036304028174572582471599)
        ·
          refine ⟨39054456042261858873707399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26036304028174572582471599 39054456042261858873707399)
          ·
            refine ⟨58581684063392788310561099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39054456042261858873707399 58581684063392788310561099)
            ·
              refine ⟨87872526095089182465841649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58581684063392788310561099 87872526095089182465841649)
              ·
                refine ⟨65904394571316886849381237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87872526095089182465841649 65904394571316886849381237)
                ·
                  refine ⟨6178536991060958142129491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65904394571316886849381237 6178536991060958142129491)
                  ·
                    refine ⟨9267805486591437213194237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178536991060958142129491 9267805486591437213194237)
                    ·
                      refine ⟨3475427057471788954947839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267805486591437213194237 3475427057471788954947839)
                      ·
                        rfl

theorem cell23_6768370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_6768370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768370 prefixEnd_6768370 := by exact prefixLift 6768370
  have htrace : WordTrace (prefixWord ++ tailWord_6768370) baseStart_6768370 baseEnd_6768370 := by
    simpa [prefixWord, tailWord_6768370, baseEnd_6768370] using wordTrace_append hprefix tailTrace_6768370
  have hstable : (prefixWord ++ tailWord_6768370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768370).length < 2 ^ (prefixWord ++ tailWord_6768370).sum := by decide
  have hdescent : baseEnd_6768370 < baseStart_6768370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768380 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_6768380 : Nat := 118140960795 + 6768380 * 2 ^ 59
def prefixEnd_6768380 : Nat := 4983230072969 + 3 ^ 40 * 6768380 * 2
def baseEnd_6768380 : Nat := 3475432192278333915822793

theorem tailTrace_6768380 : CollatzResearch.WordTrace tailWord_6768380 prefixEnd_6768380 3475432192278333915822793 := by
  unfold tailWord_6768380
  simp only [CollatzResearch.WordTrace]
  refine ⟨123431549609661341059723297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164575399479548454746297729 123431549609661341059723297)
  ·
    refine ⟨92573662207246005794792473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123431549609661341059723297 92573662207246005794792473)
    ·
      refine ⟨69430246655434504346094355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92573662207246005794792473 69430246655434504346094355)
      ·
        refine ⟨104145369983151756519141533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69430246655434504346094355 104145369983151756519141533)
        ·
          refine ⟨39054513743681908694678075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104145369983151756519141533 39054513743681908694678075)
          ·
            refine ⟨58581770615522863042017113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39054513743681908694678075 58581770615522863042017113)
            ·
              refine ⟨43936327961642147281512835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58581770615522863042017113 43936327961642147281512835)
              ·
                refine ⟨65904491942463220922269253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43936327961642147281512835 65904491942463220922269253)
                ·
                  refine ⟨12357092239211853922925485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65904491942463220922269253 12357092239211853922925485)
                  ·
                    refine ⟨4633909589704445221097057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12357092239211853922925485 4633909589704445221097057)
                    ·
                      refine ⟨3475432192278333915822793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633909589704445221097057 3475432192278333915822793)
                      ·
                        rfl

theorem cell23_6768380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_6768380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768380 prefixEnd_6768380 := by exact prefixLift 6768380
  have htrace : WordTrace (prefixWord ++ tailWord_6768380) baseStart_6768380 baseEnd_6768380 := by
    simpa [prefixWord, tailWord_6768380, baseEnd_6768380] using wordTrace_append hprefix tailTrace_6768380
  have hstable : (prefixWord ++ tailWord_6768380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768380).length < 2 ^ (prefixWord ++ tailWord_6768380).sum := by decide
  have hdescent : baseEnd_6768380 < baseStart_6768380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768387 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 1, 1, 3]
def baseStart_6768387 : Nat := 118140960795 + 6768387 * 2 ^ 59
def prefixEnd_6768387 : Nat := 4983230072969 + 3 ^ 40 * 6768387 * 2
def baseEnd_6768387 : Nat := 3475435786642915388435261

theorem tailTrace_6768387 : CollatzResearch.WordTrace tailWord_6768387 prefixEnd_6768387 3475435786642915388435261 := by
  unfold tailWord_6768387
  simp only [CollatzResearch.WordTrace]
  refine ⟨246863354530297322314951415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164575569686864881543300943 246863354530297322314951415)
  ·
    refine ⟨370295031795445983472427123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246863354530297322314951415 370295031795445983472427123)
    ·
      refine ⟨555442547693168975208640685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370295031795445983472427123 555442547693168975208640685)
      ·
        refine ⟨208290955384938365703240257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555442547693168975208640685 208290955384938365703240257)
        ·
          refine ⟨156218216538703774277430193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208290955384938365703240257 156218216538703774277430193)
          ·
            refine ⟨117163662404027830708072645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156218216538703774277430193 117163662404027830708072645)
            ·
              refine ⟨21968186700755218257763621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117163662404027830708072645 21968186700755218257763621)
              ·
                refine ⟨4119035006391603423330679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21968186700755218257763621 4119035006391603423330679)
                ·
                  refine ⟨6178552509587405134996019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119035006391603423330679 6178552509587405134996019)
                  ·
                    refine ⟨9267828764381107702494029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178552509587405134996019 9267828764381107702494029)
                    ·
                      refine ⟨3475435786642915388435261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267828764381107702494029 3475435786642915388435261)
                      ·
                        rfl

theorem cell23_6768387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_6768387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768387 prefixEnd_6768387 := by exact prefixLift 6768387
  have htrace : WordTrace (prefixWord ++ tailWord_6768387) baseStart_6768387 baseEnd_6768387 := by
    simpa [prefixWord, tailWord_6768387, baseEnd_6768387] using wordTrace_append hprefix tailTrace_6768387
  have hstable : (prefixWord ++ tailWord_6768387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768387).length < 2 ^ (prefixWord ++ tailWord_6768387).sum := by decide
  have hdescent : baseEnd_6768387 < baseStart_6768387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768410 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_6768410 : Nat := 118140960795 + 6768410 * 2 ^ 59
def prefixEnd_6768410 : Nat := 4983230072969 + 3 ^ 40 * 6768410 * 2
def baseEnd_6768410 : Nat := 3475447596697968798447655

theorem tailTrace_6768410 : CollatzResearch.WordTrace tailWord_6768410 prefixEnd_6768410 3475447596697968798447655 := by
  unfold tailWord_6768410
  simp only [CollatzResearch.WordTrace]
  refine ⟨61716048352303499310759671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164576128939475998162025789 61716048352303499310759671)
  ·
    refine ⟨92574072528455248966139507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61716048352303499310759671 92574072528455248966139507)
    ·
      refine ⟨138861108792682873449209261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92574072528455248966139507 138861108792682873449209261)
      ·
        refine ⟨52072915797256077543453473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138861108792682873449209261 52072915797256077543453473)
        ·
          refine ⟨39054686847942058157590105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52072915797256077543453473 39054686847942058157590105)
          ·
            refine ⟨29291015135956543618192579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39054686847942058157590105 29291015135956543618192579)
            ·
              refine ⟨43936522703934815427288869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29291015135956543618192579 43936522703934815427288869)
              ·
                refine ⟨8238098006987777892616663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43936522703934815427288869 8238098006987777892616663)
                ·
                  refine ⟨12357147010481666838924995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238098006987777892616663 12357147010481666838924995)
                  ·
                    refine ⟨18535720515722500258387493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12357147010481666838924995 18535720515722500258387493)
                    ·
                      refine ⟨3475447596697968798447655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18535720515722500258387493 3475447596697968798447655)
                      ·
                        rfl

theorem cell23_6768410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_6768410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768410 prefixEnd_6768410 := by exact prefixLift 6768410
  have htrace : WordTrace (prefixWord ++ tailWord_6768410) baseStart_6768410 baseEnd_6768410 := by
    simpa [prefixWord, tailWord_6768410, baseEnd_6768410] using wordTrace_append hprefix tailTrace_6768410
  have hstable : (prefixWord ++ tailWord_6768410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768410).length < 2 ^ (prefixWord ++ tailWord_6768410).sum := by decide
  have hdescent : baseEnd_6768410 < baseStart_6768410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768420 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_6768420 : Nat := 118140960795 + 6768420 * 2 ^ 59
def prefixEnd_6768420 : Nat := 4983230072969 + 3 ^ 40 * 6768420 * 2
def baseEnd_6768420 : Nat := 1158484243834837919774203

theorem tailTrace_6768420 : CollatzResearch.WordTrace tailWord_6768420 prefixEnd_6768420 1158484243834837919774203 := by
  unfold tailWord_6768420
  simp only [CollatzResearch.WordTrace]
  refine ⟨123432279069588884475451357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164576372092785179300601809 123432279069588884475451357)
  ·
    refine ⟨46287104651095831678294259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123432279069588884475451357 46287104651095831678294259)
    ·
      refine ⟨69430656976643747517441389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46287104651095831678294259 69430656976643747517441389)
      ·
        refine ⟨26036496366241405319040521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69430656976643747517441389 26036496366241405319040521)
        ·
          refine ⟨19527372274681053989280391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26036496366241405319040521 19527372274681053989280391)
          ·
            refine ⟨29291058412021580983920587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19527372274681053989280391 29291058412021580983920587)
            ·
              refine ⟨43936587618032371475880881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29291058412021580983920587 43936587618032371475880881)
              ·
                refine ⟨32952440713524278606910661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43936587618032371475880881 32952440713524278606910661)
                ·
                  refine ⟨6178582633785802238795749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32952440713524278606910661 6178582633785802238795749)
                  ·
                    refine ⟨1158484243834837919774203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6178582633785802238795749 1158484243834837919774203)
                    ·
                      rfl

theorem cell23_6768420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_6768420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768420 prefixEnd_6768420 := by exact prefixLift 6768420
  have htrace : WordTrace (prefixWord ++ tailWord_6768420) baseStart_6768420 baseEnd_6768420 := by
    simpa [prefixWord, tailWord_6768420, baseEnd_6768420] using wordTrace_append hprefix tailTrace_6768420
  have hstable : (prefixWord ++ tailWord_6768420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768420).length < 2 ^ (prefixWord ++ tailWord_6768420).sum := by decide
  have hdescent : baseEnd_6768420 < baseStart_6768420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768433 : List Nat := [1, 2, 2, 3, 2, 4, 9]
def baseStart_6768433 : Nat := 118140960795 + 6768433 * 2 ^ 59
def prefixEnd_6768433 : Nat := 4983230072969 + 3 ^ 40 * 6768433 * 2
def baseEnd_6768433 : Nat := 42906906256210150721729

theorem tailTrace_6768433 : CollatzResearch.WordTrace tailWord_6768433 prefixEnd_6768433 42906906256210150721729 := by
  unfold tailWord_6768433
  simp only [CollatzResearch.WordTrace]
  refine ⟨246865032288130672171125953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164576688192087114780750635 246865032288130672171125953)
  ·
    refine ⟨185148774216098004128344465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246865032288130672171125953 185148774216098004128344465)
    ·
      refine ⟨138861580662073503096258349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185148774216098004128344465 138861580662073503096258349)
      ·
        refine ⟨52073092748277563661096881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138861580662073503096258349 52073092748277563661096881)
        ·
          refine ⟨39054819561208172745822661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52073092748277563661096881 39054819561208172745822661)
          ·
            refine ⟨7322778667726532389841749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39054819561208172745822661 7322778667726532389841749)
            ·
              refine ⟨42906906256210150721729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7322778667726532389841749 42906906256210150721729)
              ·
                rfl

theorem cell23_6768433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 9].length) (baseStart_6768433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768433 prefixEnd_6768433 := by exact prefixLift 6768433
  have htrace : WordTrace (prefixWord ++ tailWord_6768433) baseStart_6768433 baseEnd_6768433 := by
    simpa [prefixWord, tailWord_6768433, baseEnd_6768433] using wordTrace_append hprefix tailTrace_6768433
  have hstable : (prefixWord ++ tailWord_6768433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768433).length < 2 ^ (prefixWord ++ tailWord_6768433).sum := by decide
  have hdescent : baseEnd_6768433 < baseStart_6768433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768438 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6768438 : Nat := 118140960795 + 6768438 * 2 ^ 59
def prefixEnd_6768438 : Nat := 4983230072969 + 3 ^ 40 * 6768438 * 2
def baseEnd_6768438 : Nat := 3475461974156294688897527

theorem tailTrace_6768438 : CollatzResearch.WordTrace tailWord_6768438 prefixEnd_6768438 3475461974156294688897527 := by
  unfold tailWord_6768438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429075915819534876566123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164576809768741705350038645 15429075915819534876566123)
  ·
    refine ⟨23143613873729302314849185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15429075915819534876566123 23143613873729302314849185)
    ·
      refine ⟨17357710405296976736136889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23143613873729302314849185 17357710405296976736136889)
      ·
        refine ⟨13018282803972732552102667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17357710405296976736136889 13018282803972732552102667)
        ·
          refine ⟨19527424205959098828154001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13018282803972732552102667 19527424205959098828154001)
          ·
            refine ⟨14645568154469324121115501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19527424205959098828154001 14645568154469324121115501)
            ·
              refine ⟨5492088057925996545418313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14645568154469324121115501 5492088057925996545418313)
              ·
                refine ⟨4119066043444497409063735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492088057925996545418313 4119066043444497409063735)
                ·
                  refine ⟨6178599065166746113595603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119066043444497409063735 6178599065166746113595603)
                  ·
                    refine ⟨9267898597750119170393405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178599065166746113595603 9267898597750119170393405)
                    ·
                      refine ⟨3475461974156294688897527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267898597750119170393405 3475461974156294688897527)
                      ·
                        rfl

theorem cell23_6768438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6768438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768438 prefixEnd_6768438 := by exact prefixLift 6768438
  have htrace : WordTrace (prefixWord ++ tailWord_6768438) baseStart_6768438 baseEnd_6768438 := by
    simpa [prefixWord, tailWord_6768438, baseEnd_6768438] using wordTrace_append hprefix tailTrace_6768438
  have hstable : (prefixWord ++ tailWord_6768438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768438).length < 2 ^ (prefixWord ++ tailWord_6768438).sum := by decide
  have hdescent : baseEnd_6768438 < baseStart_6768438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768444 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_6768444 : Nat := 118140960795 + 6768444 * 2 ^ 59
def prefixEnd_6768444 : Nat := 4983230072969 + 3 ^ 40 * 6768444 * 2
def baseEnd_6768444 : Nat := 3475465055040221665422499

theorem tailTrace_6768444 : CollatzResearch.WordTrace tailWord_6768444 prefixEnd_6768444 3475465055040221665422499 := by
  unfold tailWord_6768444
  simp only [CollatzResearch.WordTrace]
  refine ⟨123432716745545410524888193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164576955660727214033184257 123432716745545410524888193)
  ·
    refine ⟨92574537559159057893666145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123432716745545410524888193 92574537559159057893666145)
    ·
      refine ⟨69430903169369293420249609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92574537559159057893666145 69430903169369293420249609)
      ·
        refine ⟨52073177377026970065187207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69430903169369293420249609 52073177377026970065187207)
        ·
          refine ⟨78109766065540455097780811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52073177377026970065187207 78109766065540455097780811)
          ·
            refine ⟨117164649098310682646671217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78109766065540455097780811 117164649098310682646671217)
            ·
              refine ⟨87873486823733011985003413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117164649098310682646671217 87873486823733011985003413)
              ·
                refine ⟨4119069694862484936797035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87873486823733011985003413 4119069694862484936797035)
                ·
                  refine ⟨6178604542293727405195553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119069694862484936797035 6178604542293727405195553)
                  ·
                    refine ⟨4633953406720295553896665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178604542293727405195553 4633953406720295553896665)
                    ·
                      refine ⟨3475465055040221665422499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4633953406720295553896665 3475465055040221665422499)
                      ·
                        rfl

theorem cell23_6768444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_6768444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768444 prefixEnd_6768444 := by exact prefixLift 6768444
  have htrace : WordTrace (prefixWord ++ tailWord_6768444) baseStart_6768444 baseEnd_6768444 := by
    simpa [prefixWord, tailWord_6768444, baseEnd_6768444] using wordTrace_append hprefix tailTrace_6768444
  have hstable : (prefixWord ++ tailWord_6768444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768444).length < 2 ^ (prefixWord ++ tailWord_6768444).sum := by decide
  have hdescent : baseEnd_6768444 < baseStart_6768444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768494 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6768494 : Nat := 118140960795 + 6768494 * 2 ^ 59
def prefixEnd_6768494 : Nat := 4983230072969 + 3 ^ 40 * 6768494 * 2
def baseEnd_6768494 : Nat := 3475490729072946469797269

theorem tailTrace_6768494 : CollatzResearch.WordTrace tailWord_6768494 prefixEnd_6768494 3475490729072946469797269 := by
  unfold tailWord_6768494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30858407142613709948637067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164578171427273119726064357 30858407142613709948637067)
  ·
    refine ⟨46287610713920564922955601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30858407142613709948637067 46287610713920564922955601)
    ·
      refine ⟨34715708035440423692216701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46287610713920564922955601 34715708035440423692216701)
      ·
        refine ⟨13018390513290158884581263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34715708035440423692216701 13018390513290158884581263)
        ·
          refine ⟨19527585769935238326871895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13018390513290158884581263 19527585769935238326871895)
          ·
            refine ⟨29291378654902857490307843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19527585769935238326871895 29291378654902857490307843)
            ·
              refine ⟨43937067982354286235461765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29291378654902857490307843 43937067982354286235461765)
              ·
                refine ⟨8238200246691428669149081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43937067982354286235461765 8238200246691428669149081)
                ·
                  refine ⟨6178650185018571501861811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238200246691428669149081 6178650185018571501861811)
                  ·
                    refine ⟨9267975277527857252792717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178650185018571501861811 9267975277527857252792717)
                    ·
                      refine ⟨3475490729072946469797269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9267975277527857252792717 3475490729072946469797269)
                      ·
                        rfl

theorem cell23_6768494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6768494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768494 prefixEnd_6768494 := by exact prefixLift 6768494
  have htrace : WordTrace (prefixWord ++ tailWord_6768494) baseStart_6768494 baseEnd_6768494 := by
    simpa [prefixWord, tailWord_6768494, baseEnd_6768494] using wordTrace_append hprefix tailTrace_6768494
  have hstable : (prefixWord ++ tailWord_6768494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768494).length < 2 ^ (prefixWord ++ tailWord_6768494).sum := by decide
  have hdescent : baseEnd_6768494 < baseStart_6768494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768517 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_6768517 : Nat := 118140960795 + 6768517 * 2 ^ 59
def prefixEnd_6768517 : Nat := 4983230072969 + 3 ^ 40 * 6768517 * 2
def baseEnd_6768517 : Nat := 3475502539127999879809663

theorem tailTrace_6768517 : CollatzResearch.WordTrace tailWord_6768517 prefixEnd_6768517 3475502539127999879809663 := by
  unfold tailWord_6768517
  simp only [CollatzResearch.WordTrace]
  refine ⟨246868096019826354517183805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164578730679884236344789203 246868096019826354517183805)
  ·
    refine ⟨92575536007434882943943927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246868096019826354517183805 92575536007434882943943927)
    ·
      refine ⟨138863304011152324415915891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92575536007434882943943927 138863304011152324415915891)
      ·
        refine ⟨208294956016728486623873837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138863304011152324415915891 208294956016728486623873837)
        ·
          refine ⟨78110608506273182483952689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208294956016728486623873837 78110608506273182483952689)
          ·
            refine ⟨58582956379704886862964517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78110608506273182483952689 58582956379704886862964517)
            ·
              refine ⟨10984304321194666286805847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58582956379704886862964517 10984304321194666286805847)
              ·
                refine ⟨16476456481791999430208771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10984304321194666286805847 16476456481791999430208771)
                ·
                  refine ⟨24714684722687999145313157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16476456481791999430208771 24714684722687999145313157)
                  ·
                    refine ⟨4634003385503999839746217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24714684722687999145313157 4634003385503999839746217)
                    ·
                      refine ⟨3475502539127999879809663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634003385503999839746217 3475502539127999879809663)
                      ·
                        rfl

theorem cell23_6768517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_6768517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768517 prefixEnd_6768517 := by exact prefixLift 6768517
  have htrace : WordTrace (prefixWord ++ tailWord_6768517) baseStart_6768517 baseEnd_6768517 := by
    simpa [prefixWord, tailWord_6768517, baseEnd_6768517] using wordTrace_append hprefix tailTrace_6768517
  have hstable : (prefixWord ++ tailWord_6768517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768517).length < 2 ^ (prefixWord ++ tailWord_6768517).sum := by decide
  have hdescent : baseEnd_6768517 < baseStart_6768517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768551 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6768551 : Nat := 118140960795 + 6768551 * 2 ^ 59
def prefixEnd_6768551 : Nat := 4983230072969 + 3 ^ 40 * 6768551 * 2
def baseEnd_6768551 : Nat := 3475519997470252746784507

theorem tailTrace_6768551 : CollatzResearch.WordTrace tailWord_6768551 prefixEnd_6768551 3475519997470252746784507 := by
  unfold tailWord_6768551
  simp only [CollatzResearch.WordTrace]
  refine ⟨246869336101703178323921507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164579557401135452215947671 246869336101703178323921507)
  ·
    refine ⟨370304004152554767485882261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246869336101703178323921507 370304004152554767485882261)
    ·
      refine ⟨17358000194651004725900731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370304004152554767485882261 17358000194651004725900731)
      ·
        refine ⟨26037000291976507088851097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358000194651004725900731 26037000291976507088851097)
        ·
          refine ⟨19527750218982380316638323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26037000291976507088851097 19527750218982380316638323)
          ·
            refine ⟨29291625328473570474957485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19527750218982380316638323 29291625328473570474957485)
            ·
              refine ⟨10984359498177588928109057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29291625328473570474957485 10984359498177588928109057)
              ·
                refine ⟨8238269623633191696081793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10984359498177588928109057 8238269623633191696081793)
                ·
                  refine ⟨6178702217724893772061345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238269623633191696081793 6178702217724893772061345)
                  ·
                    refine ⟨4634026663293670329046009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178702217724893772061345 4634026663293670329046009)
                    ·
                      refine ⟨3475519997470252746784507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634026663293670329046009 3475519997470252746784507)
                      ·
                        rfl

theorem cell23_6768551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6768551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768551 prefixEnd_6768551 := by exact prefixLift 6768551
  have htrace : WordTrace (prefixWord ++ tailWord_6768551) baseStart_6768551 baseEnd_6768551 := by
    simpa [prefixWord, tailWord_6768551, baseEnd_6768551] using wordTrace_append hprefix tailTrace_6768551
  have hstable : (prefixWord ++ tailWord_6768551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768551).length < 2 ^ (prefixWord ++ tailWord_6768551).sum := by decide
  have hdescent : baseEnd_6768551 < baseStart_6768551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768563 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_6768563 : Nat := 118140960795 + 6768563 * 2 ^ 59
def prefixEnd_6768563 : Nat := 4983230072969 + 3 ^ 40 * 6768563 * 2
def baseEnd_6768563 : Nat := 3475526159238106699834451

theorem tailTrace_6768563 : CollatzResearch.WordTrace tailWord_6768563 prefixEnd_6768563 3475526159238106699834451 := by
  unfold tailWord_6768563
  simp only [CollatzResearch.WordTrace]
  refine ⟨246869773777659704373358343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164579849185106469582238895 246869773777659704373358343)
  ·
    refine ⟨370304660666489556560037515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246869773777659704373358343 370304660666489556560037515)
    ·
      refine ⟨555456990999734334840056273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370304660666489556560037515 555456990999734334840056273)
      ·
        refine ⟨416592743249800751130042205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555456990999734334840056273 416592743249800751130042205)
        ·
          refine ⟨156222278718675281673765827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416592743249800751130042205 156222278718675281673765827)
          ·
            refine ⟨234333418078012922510648741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156222278718675281673765827 234333418078012922510648741)
            ·
              refine ⟨43937515889627422970746639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234333418078012922510648741 43937515889627422970746639)
              ·
                refine ⟨65906273834441134456119959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43937515889627422970746639 65906273834441134456119959)
                ·
                  refine ⟨98859410751661701684179939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65906273834441134456119959 98859410751661701684179939)
                  ·
                    refine ⟨148289116127492552526269909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98859410751661701684179939 148289116127492552526269909)
                    ·
                      refine ⟨3475526159238106699834451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148289116127492552526269909 3475526159238106699834451)
                      ·
                        rfl

theorem cell23_6768563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_6768563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768563 prefixEnd_6768563 := by exact prefixLift 6768563
  have htrace : WordTrace (prefixWord ++ tailWord_6768563) baseStart_6768563 baseEnd_6768563 := by
    simpa [prefixWord, tailWord_6768563, baseEnd_6768563] using wordTrace_append hprefix tailTrace_6768563
  have hstable : (prefixWord ++ tailWord_6768563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768563).length < 2 ^ (prefixWord ++ tailWord_6768563).sum := by decide
  have hdescent : baseEnd_6768563 < baseStart_6768563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768583 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 10]
def baseStart_6768583 : Nat := 118140960795 + 6768583 * 2 ^ 59
def prefixEnd_6768583 : Nat := 4983230072969 + 3 ^ 40 * 6768583 * 2
def baseEnd_6768583 : Nat := 1158512142950398873861453

theorem tailTrace_6768583 : CollatzResearch.WordTrace tailWord_6768583 prefixEnd_6768583 1158512142950398873861453 := by
  unfold tailWord_6768583
  simp only [CollatzResearch.WordTrace]
  refine ⟨246870503237587247789086403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164580335491724831859390935 246870503237587247789086403)
  ·
    refine ⟨370305754856380871683629605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246870503237587247789086403 370305754856380871683629605)
    ·
      refine ⟨69432329035571413440680551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370305754856380871683629605 69432329035571413440680551)
      ·
        refine ⟨104148493553357120161020827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69432329035571413440680551 104148493553357120161020827)
        ·
          refine ⟨156222740330035680241531241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104148493553357120161020827 156222740330035680241531241)
          ·
            refine ⟨117167055247526760181148431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156222740330035680241531241 117167055247526760181148431)
            ·
              refine ⟨175750582871290140271722647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117167055247526760181148431 175750582871290140271722647)
              ·
                refine ⟨263625874306935210407583971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175750582871290140271722647 263625874306935210407583971)
                ·
                  refine ⟨395438811460402815611375957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263625874306935210407583971 395438811460402815611375957)
                  ·
                    refine ⟨1158512142950398873861453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 395438811460402815611375957 1158512142950398873861453)
                    ·
                      rfl

theorem cell23_6768583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_6768583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768583 prefixEnd_6768583 := by exact prefixLift 6768583
  have htrace : WordTrace (prefixWord ++ tailWord_6768583) baseStart_6768583 baseEnd_6768583 := by
    simpa [prefixWord, tailWord_6768583, baseEnd_6768583] using wordTrace_append hprefix tailTrace_6768583
  have hstable : (prefixWord ++ tailWord_6768583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768583).length < 2 ^ (prefixWord ++ tailWord_6768583).sum := by decide
  have hdescent : baseEnd_6768583 < baseStart_6768583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768590 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_6768590 : Nat := 118140960795 + 6768590 * 2 ^ 59
def prefixEnd_6768590 : Nat := 4983230072969 + 3 ^ 40 * 6768590 * 2
def baseEnd_6768590 : Nat := 3475540023215778094196827

theorem tailTrace_6768590 : CollatzResearch.WordTrace tailWord_6768590 prefixEnd_6768590 3475540023215778094196827 := by
  unfold tailWord_6768590
  simp only [CollatzResearch.WordTrace]
  refine ⟨30858844818570235998073903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164580505699041258656394149 30858844818570235998073903)
  ·
    refine ⟨46288267227855353997110855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30858844818570235998073903 46288267227855353997110855)
    ·
      refine ⟨69432400841783030995666283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46288267227855353997110855 69432400841783030995666283)
      ·
        refine ⟨104148601262674546493499425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69432400841783030995666283 104148601262674546493499425)
        ·
          refine ⟨78111450947005909870124569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104148601262674546493499425 78111450947005909870124569)
          ·
            refine ⟨58583588210254432402593427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78111450947005909870124569 58583588210254432402593427)
            ·
              refine ⟨87875382315381648603890141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58583588210254432402593427 87875382315381648603890141)
              ·
                refine ⟨32953268368268118226458803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87875382315381648603890141 32953268368268118226458803)
                ·
                  refine ⟨49429902552402177339688205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32953268368268118226458803 49429902552402177339688205)
                  ·
                    refine ⟨18536213457150816502383077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49429902552402177339688205 18536213457150816502383077)
                    ·
                      refine ⟨3475540023215778094196827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18536213457150816502383077 3475540023215778094196827)
                      ·
                        rfl

theorem cell23_6768590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_6768590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768590 prefixEnd_6768590 := by exact prefixLift 6768590
  have htrace : WordTrace (prefixWord ++ tailWord_6768590) baseStart_6768590 baseEnd_6768590 := by
    simpa [prefixWord, tailWord_6768590, baseEnd_6768590] using wordTrace_append hprefix tailTrace_6768590
  have hstable : (prefixWord ++ tailWord_6768590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768590).length < 2 ^ (prefixWord ++ tailWord_6768590).sum := by decide
  have hdescent : baseEnd_6768590 < baseStart_6768590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768607 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_6768607 : Nat := 118140960795 + 6768607 * 2 ^ 59
def prefixEnd_6768607 : Nat := 4983230072969 + 3 ^ 40 * 6768607 * 2
def baseEnd_6768607 : Nat := 3475548752386904527684249

theorem tailTrace_6768607 : CollatzResearch.WordTrace tailWord_6768607 prefixEnd_6768607 3475548752386904527684249 := by
  unfold tailWord_6768607
  simp only [CollatzResearch.WordTrace]
  refine ⟨246871378589500299887960075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164580919059666866591973383 246871378589500299887960075)
  ·
    refine ⟨370307067884250449831940113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246871378589500299887960075 370307067884250449831940113)
    ·
      refine ⟨277730300913187837373955085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370307067884250449831940113 277730300913187837373955085)
      ·
        refine ⟨104148862842445439015233157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277730300913187837373955085 104148862842445439015233157)
        ·
          refine ⟨19527911782958519815356217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104148862842445439015233157 19527911782958519815356217)
          ·
            refine ⟨14645933837218889861517163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19527911782958519815356217 14645933837218889861517163)
            ·
              refine ⟨21968900755828334792275745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14645933837218889861517163 21968900755828334792275745)
              ·
                refine ⟨16476675566871251094206809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21968900755828334792275745 16476675566871251094206809)
                ·
                  refine ⟨12357506675153438320655107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16476675566871251094206809 12357506675153438320655107)
                  ·
                    refine ⟨18536260012730157480982661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12357506675153438320655107 18536260012730157480982661)
                    ·
                      refine ⟨3475548752386904527684249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18536260012730157480982661 3475548752386904527684249)
                      ·
                        rfl

theorem cell23_6768607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_6768607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768607 prefixEnd_6768607 := by exact prefixLift 6768607
  have htrace : WordTrace (prefixWord ++ tailWord_6768607) baseStart_6768607 baseEnd_6768607 := by
    simpa [prefixWord, tailWord_6768607, baseEnd_6768607] using wordTrace_append hprefix tailTrace_6768607
  have hstable : (prefixWord ++ tailWord_6768607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768607).length < 2 ^ (prefixWord ++ tailWord_6768607).sum := by decide
  have hdescent : baseEnd_6768607 < baseStart_6768607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 4, 3, 2]
def baseStart_6768667 : Nat := 118140960795 + 6768667 * 2 ^ 59
def prefixEnd_6768667 : Nat := 4983230072969 + 3 ^ 40 * 6768667 * 2
def baseEnd_6768667 : Nat := 3475579561226174292933973

theorem tailTrace_6768667 : CollatzResearch.WordTrace tailWord_6768667 prefixEnd_6768667 3475579561226174292933973 := by
  unfold tailWord_6768667
  simp only [CollatzResearch.WordTrace]
  refine ⟨246873566969282930135144255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164582377979521953423429503 246873566969282930135144255)
  ·
    refine ⟨370310350453924395202716383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246873566969282930135144255 370310350453924395202716383)
    ·
      refine ⟨555465525680886592804074575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370310350453924395202716383 555465525680886592804074575)
      ·
        refine ⟨833198288521329889206111863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555465525680886592804074575 833198288521329889206111863)
        ·
          refine ⟨1249797432781994833809167795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833198288521329889206111863 1249797432781994833809167795)
          ·
            refine ⟨1874696149172992250713751693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249797432781994833809167795 1874696149172992250713751693)
            ·
              refine ⟨703011055939872094017656885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874696149172992250713751693 703011055939872094017656885)
              ·
                refine ⟨65907286494363008814155333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703011055939872094017656885 65907286494363008814155333)
                ·
                  refine ⟨12357616217693064152654125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65907286494363008814155333 12357616217693064152654125)
                  ·
                    refine ⟨4634106081634899057245297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12357616217693064152654125 4634106081634899057245297)
                    ·
                      refine ⟨3475579561226174292933973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634106081634899057245297 3475579561226174292933973)
                      ·
                        rfl

theorem cell23_6768667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3, 2].length) (baseStart_6768667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768667 prefixEnd_6768667 := by exact prefixLift 6768667
  have htrace : WordTrace (prefixWord ++ tailWord_6768667) baseStart_6768667 baseEnd_6768667 := by
    simpa [prefixWord, tailWord_6768667, baseEnd_6768667] using wordTrace_append hprefix tailTrace_6768667
  have hstable : (prefixWord ++ tailWord_6768667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768667).length < 2 ^ (prefixWord ++ tailWord_6768667).sum := by decide
  have hdescent : baseEnd_6768667 < baseStart_6768667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768668 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_6768668 : Nat := 118140960795 + 6768668 * 2 ^ 59
def prefixEnd_6768668 : Nat := 4983230072969 + 3 ^ 40 * 6768668 * 2
def baseEnd_6768668 : Nat := 1158526691568942929673823

theorem tailTrace_6768668 : CollatzResearch.WordTrace tailWord_6768668 prefixEnd_6768668 1158526691568942929673823 := by
  unfold tailWord_6768668
  simp only [CollatzResearch.WordTrace]
  refine ⟨123436801721139653652965329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164582402294852871537287105 123436801721139653652965329)
  ·
    refine ⟨92577601290854740239723997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123436801721139653652965329 92577601290854740239723997)
    ·
      refine ⟨34716600484070527589896499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92577601290854740239723997 34716600484070527589896499)
      ·
        refine ⟨52074900726105791384844749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34716600484070527589896499 52074900726105791384844749)
        ·
          refine ⟨19528087772289671769316781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52074900726105791384844749 19528087772289671769316781)
          ·
            refine ⟨7323032914608626913493793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19528087772289671769316781 7323032914608626913493793)
            ·
              refine ⟨5492274685956470185120345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7323032914608626913493793 5492274685956470185120345)
              ·
                refine ⟨4119206014467352638840259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492274685956470185120345 4119206014467352638840259)
                ·
                  refine ⟨6178809021701028958260389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119206014467352638840259 6178809021701028958260389)
                  ·
                    refine ⟨1158526691568942929673823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6178809021701028958260389 1158526691568942929673823)
                    ·
                      rfl

theorem cell23_6768668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_6768668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768668 prefixEnd_6768668 := by exact prefixLift 6768668
  have htrace : WordTrace (prefixWord ++ tailWord_6768668) baseStart_6768668 baseEnd_6768668 := by
    simpa [prefixWord, tailWord_6768668, baseEnd_6768668] using wordTrace_append hprefix tailTrace_6768668
  have hstable : (prefixWord ++ tailWord_6768668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768668).length < 2 ^ (prefixWord ++ tailWord_6768668).sum := by decide
  have hdescent : baseEnd_6768668 < baseStart_6768668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768674 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_6768674 : Nat := 118140960795 + 6768674 * 2 ^ 59
def prefixEnd_6768674 : Nat := 4983230072969 + 3 ^ 40 * 6768674 * 2
def baseEnd_6768674 : Nat := 3475583155590755765546441

theorem tailTrace_6768674 : CollatzResearch.WordTrace tailWord_6768674 prefixEnd_6768674 3475583155590755765546441 := by
  unfold tailWord_6768674
  simp only [CollatzResearch.WordTrace]
  refine ⟨61718455570064392582662269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164582548186838380220432717 61718455570064392582662269)
  ·
    refine ⟨23144420838774147218498351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61718455570064392582662269 23144420838774147218498351)
    ·
      refine ⟨34716631258161220827747527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23144420838774147218498351 34716631258161220827747527)
      ·
        refine ⟨52074946887241831241621291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34716631258161220827747527 52074946887241831241621291)
        ·
          refine ⟨78112420330862746862431937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52074946887241831241621291 78112420330862746862431937)
          ·
            refine ⟨58584315248147060146823953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78112420330862746862431937 58584315248147060146823953)
            ·
              refine ⟨43938236436110295110117965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58584315248147060146823953 43938236436110295110117965)
              ·
                refine ⟨16476838663541360666294237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43938236436110295110117965 16476838663541360666294237)
                ·
                  refine ⟨6178814498828010249860339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16476838663541360666294237 6178814498828010249860339)
                  ·
                    refine ⟨9268221748242015374790509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178814498828010249860339 9268221748242015374790509)
                    ·
                      refine ⟨3475583155590755765546441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9268221748242015374790509 3475583155590755765546441)
                      ·
                        rfl

theorem cell23_6768674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_6768674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768674 prefixEnd_6768674 := by exact prefixLift 6768674
  have htrace : WordTrace (prefixWord ++ tailWord_6768674) baseStart_6768674 baseEnd_6768674 := by
    simpa [prefixWord, tailWord_6768674, baseEnd_6768674] using wordTrace_append hprefix tailTrace_6768674
  have hstable : (prefixWord ++ tailWord_6768674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768674).length < 2 ^ (prefixWord ++ tailWord_6768674).sum := by decide
  have hdescent : baseEnd_6768674 < baseStart_6768674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768694 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_6768694 : Nat := 118140960795 + 6768694 * 2 ^ 59
def prefixEnd_6768694 : Nat := 4983230072969 + 3 ^ 40 * 6768694 * 2
def baseEnd_6768694 : Nat := 1158531141734615229098783

theorem tailTrace_6768694 : CollatzResearch.WordTrace tailWord_6768694 prefixEnd_6768694 1158531141734615229098783 := by
  unfold tailWord_6768694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429659483761569609148571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164583034493456742497584757 15429659483761569609148571)
  ·
    refine ⟨23144489225642354413722857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15429659483761569609148571 23144489225642354413722857)
    ·
      refine ⟨17358366919231765810292143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23144489225642354413722857 17358366919231765810292143)
      ·
        refine ⟨26037550378847648715438215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358366919231765810292143 26037550378847648715438215)
        ·
          refine ⟨39056325568271473073157323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26037550378847648715438215 39056325568271473073157323)
          ·
            refine ⟨58584488352407209609735985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39056325568271473073157323 58584488352407209609735985)
            ·
              refine ⟨43938366264305407207301989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58584488352407209609735985 43938366264305407207301989)
              ·
                refine ⟨8238443674557263851369123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43938366264305407207301989 8238443674557263851369123)
                ·
                  refine ⟨12357665511835895777053685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238443674557263851369123 12357665511835895777053685)
                  ·
                    refine ⟨1158531141734615229098783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12357665511835895777053685 1158531141734615229098783)
                    ·
                      rfl

theorem cell23_6768694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_6768694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768694 prefixEnd_6768694 := by exact prefixLift 6768694
  have htrace : WordTrace (prefixWord ++ tailWord_6768694) baseStart_6768694 baseEnd_6768694 := by
    simpa [prefixWord, tailWord_6768694, baseEnd_6768694] using wordTrace_append hprefix tailTrace_6768694
  have hstable : (prefixWord ++ tailWord_6768694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768694).length < 2 ^ (prefixWord ++ tailWord_6768694).sum := by decide
  have hdescent : baseEnd_6768694 < baseStart_6768694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768714 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_6768714 : Nat := 118140960795 + 6768714 * 2 ^ 59
def prefixEnd_6768714 : Nat := 4983230072969 + 3 ^ 40 * 6768714 * 2
def baseEnd_6768714 : Nat := 3475603694816935609046257

theorem tailTrace_6768714 : CollatzResearch.WordTrace tailWord_6768714 prefixEnd_6768714 3475603694816935609046257 := by
  unfold tailWord_6768714
  simp only [CollatzResearch.WordTrace]
  refine ⟨61718820300028164290526299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164583520800075104774736797 61718820300028164290526299)
  ·
    refine ⟨92578230450042246435789449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61718820300028164290526299 92578230450042246435789449)
    ·
      refine ⟨69433672837531684826842087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92578230450042246435789449 69433672837531684826842087)
      ·
        refine ⟨104150509256297527240263131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69433672837531684826842087 104150509256297527240263131)
        ·
          refine ⟨156225763884446290860394697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104150509256297527240263131 156225763884446290860394697)
          ·
            refine ⟨117169322913334718145296023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156225763884446290860394697 117169322913334718145296023)
            ·
              refine ⟨175753984370002077217944035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117169322913334718145296023 175753984370002077217944035)
              ·
                refine ⟨263630976555003115826916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175753984370002077217944035 263630976555003115826916053)
                ·
                  refine ⟨6178851013007885527193345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 263630976555003115826916053 6178851013007885527193345)
                  ·
                    refine ⟨4634138259755914145395009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178851013007885527193345 4634138259755914145395009)
                    ·
                      refine ⟨3475603694816935609046257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634138259755914145395009 3475603694816935609046257)
                      ·
                        rfl

theorem cell23_6768714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_6768714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768714 prefixEnd_6768714 := by exact prefixLift 6768714
  have htrace : WordTrace (prefixWord ++ tailWord_6768714) baseStart_6768714 baseEnd_6768714 := by
    simpa [prefixWord, tailWord_6768714, baseEnd_6768714] using wordTrace_append hprefix tailTrace_6768714
  have hstable : (prefixWord ++ tailWord_6768714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768714).length < 2 ^ (prefixWord ++ tailWord_6768714).sum := by decide
  have hdescent : baseEnd_6768714 < baseStart_6768714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768741 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_6768741 : Nat := 118140960795 + 6768741 * 2 ^ 59
def prefixEnd_6768741 : Nat := 4983230072969 + 3 ^ 40 * 6768741 * 2
def baseEnd_6768741 : Nat := 1158539186264869001136211

theorem tailTrace_6768741 : CollatzResearch.WordTrace tailWord_6768741 prefixEnd_6768741 1158539186264869001136211 := by
  unfold tailWord_6768741
  simp only [CollatzResearch.WordTrace]
  refine ⟨246876265971014840773338077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164584177314009893848892051 246876265971014840773338077)
  ·
    refine ⟨92578599739130565290001779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246876265971014840773338077 92578599739130565290001779)
    ·
      refine ⟨138867899608695847935002669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92578599739130565290001779 138867899608695847935002669)
      ·
        refine ⟨52075462353260942975626001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138867899608695847935002669 52075462353260942975626001)
        ·
          refine ⟨39056596764945707231719501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52075462353260942975626001 39056596764945707231719501)
          ·
            refine ⟨14646223786854640211894813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39056596764945707231719501 14646223786854640211894813)
            ·
              refine ⟨5492333920070490079460555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14646223786854640211894813 5492333920070490079460555)
              ·
                refine ⟨8238500880105735119190833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492333920070490079460555 8238500880105735119190833)
                ·
                  refine ⟨6178875660079301339393125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238500880105735119190833 6178875660079301339393125)
                  ·
                    refine ⟨1158539186264869001136211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6178875660079301339393125 1158539186264869001136211)
                    ·
                      rfl

theorem cell23_6768741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_6768741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768741 prefixEnd_6768741 := by exact prefixLift 6768741
  have htrace : WordTrace (prefixWord ++ tailWord_6768741) baseStart_6768741 baseEnd_6768741 := by
    simpa [prefixWord, tailWord_6768741, baseEnd_6768741] using wordTrace_append hprefix tailTrace_6768741
  have hstable : (prefixWord ++ tailWord_6768741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768741).length < 2 ^ (prefixWord ++ tailWord_6768741).sum := by decide
  have hdescent : baseEnd_6768741 < baseStart_6768741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768754 : List Nat := [3, 2, 1, 2, 2, 4, 2, 7]
def baseStart_6768754 : Nat := 118140960795 + 6768754 * 2 ^ 59
def prefixEnd_6768754 : Nat := 4983230072969 + 3 ^ 40 * 6768754 * 2
def baseEnd_6768754 : Nat := 128726823483078350094299

theorem tailTrace_6768754 : CollatzResearch.WordTrace tailWord_6768754 prefixEnd_6768754 128726823483078350094299 := by
  unfold tailWord_6768754
  simp only [CollatzResearch.WordTrace]
  refine ⟨61719185029991935998390329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164584493413311829329040877 61719185029991935998390329)
  ·
    refine ⟨46289388772493951998792747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61719185029991935998390329 46289388772493951998792747)
    ·
      refine ⟨69434083158740927998189121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46289388772493951998792747 69434083158740927998189121)
      ·
        refine ⟨52075562369055695998641841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69434083158740927998189121 52075562369055695998641841)
        ·
          refine ⟨39056671776791771998981381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52075562369055695998641841 39056671776791771998981381)
          ·
            refine ⟨7323125958148457249809009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39056671776791771998981381 7323125958148457249809009)
            ·
              refine ⟨5492344468611342937356757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7323125958148457249809009 5492344468611342937356757)
              ·
                refine ⟨128726823483078350094299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5492344468611342937356757 128726823483078350094299)
                ·
                  rfl

theorem cell23_6768754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_6768754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768754 prefixEnd_6768754 := by exact prefixLift 6768754
  have htrace : WordTrace (prefixWord ++ tailWord_6768754) baseStart_6768754 baseEnd_6768754 := by
    simpa [prefixWord, tailWord_6768754, baseEnd_6768754] using wordTrace_append hprefix tailTrace_6768754
  have hstable : (prefixWord ++ tailWord_6768754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768754).length < 2 ^ (prefixWord ++ tailWord_6768754).sum := by decide
  have hdescent : baseEnd_6768754 < baseStart_6768754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768764 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_6768764 : Nat := 118140960795 + 6768764 * 2 ^ 59
def prefixEnd_6768764 : Nat := 4983230072969 + 3 ^ 40 * 6768764 * 2
def baseEnd_6768764 : Nat := 3475629368849660413421027

theorem tailTrace_6768764 : CollatzResearch.WordTrace tailWord_6768764 prefixEnd_6768764 3475629368849660413421027 := by
  unfold tailWord_6768764
  simp only [CollatzResearch.WordTrace]
  refine ⟨123438552424965757850712673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164584736566621010467616897 123438552424965757850712673)
  ·
    refine ⟨92578914318724318388034505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123438552424965757850712673 92578914318724318388034505)
    ·
      refine ⟨69434185739043238791025879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92578914318724318388034505 69434185739043238791025879)
      ·
        refine ⟨104151278608564858186538819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69434185739043238791025879 104151278608564858186538819)
        ·
          refine ⟨156226917912847287279808229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104151278608564858186538819 156226917912847287279808229)
          ·
            refine ⟨29292547108658866364964043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156226917912847287279808229 29292547108658866364964043)
            ·
              refine ⟨43938820662988299547446065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29292547108658866364964043 43938820662988299547446065)
              ·
                refine ⟨32954115497241224660584549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43938820662988299547446065 32954115497241224660584549)
                ·
                  refine ⟨6178896655732729623859603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32954115497241224660584549 6178896655732729623859603)
                  ·
                    refine ⟨9268344983599094435789405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6178896655732729623859603 9268344983599094435789405)
                    ·
                      refine ⟨3475629368849660413421027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9268344983599094435789405 3475629368849660413421027)
                      ·
                        rfl

theorem cell23_6768764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_6768764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768764 prefixEnd_6768764 := by exact prefixLift 6768764
  have htrace : WordTrace (prefixWord ++ tailWord_6768764) baseStart_6768764 baseEnd_6768764 := by
    simpa [prefixWord, tailWord_6768764, baseEnd_6768764] using wordTrace_append hprefix tailTrace_6768764
  have hstable : (prefixWord ++ tailWord_6768764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768764).length < 2 ^ (prefixWord ++ tailWord_6768764).sum := by decide
  have hdescent : baseEnd_6768764 < baseStart_6768764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768765 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_6768765 : Nat := 118140960795 + 6768765 * 2 ^ 59
def prefixEnd_6768765 : Nat := 4983230072969 + 3 ^ 40 * 6768765 * 2
def baseEnd_6768765 : Nat := 3475629882330314909508523

theorem tailTrace_6768765 : CollatzResearch.WordTrace tailWord_6768765 prefixEnd_6768765 3475629882330314909508523 := by
  unfold tailWord_6768765
  simp only [CollatzResearch.WordTrace]
  refine ⟨246877141322927892872211749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164584760881951928581474499 246877141322927892872211749)
  ·
    refine ⟨46289463998048979913539703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246877141322927892872211749 46289463998048979913539703)
    ·
      refine ⟨69434195997073469870309555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46289463998048979913539703 69434195997073469870309555)
      ·
        refine ⟨104151293995610204805464333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69434195997073469870309555 104151293995610204805464333)
        ·
          refine ⟨39056735248353826802049125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104151293995610204805464333 39056735248353826802049125)
          ·
            refine ⟨7323137859066342525384211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39056735248353826802049125 7323137859066342525384211)
            ·
              refine ⟨10984706788599513788076317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323137859066342525384211 10984706788599513788076317)
              ·
                refine ⟨4119265045724817670528619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10984706788599513788076317 4119265045724817670528619)
                ·
                  refine ⟨6178897568587226505792929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119265045724817670528619 6178897568587226505792929)
                  ·
                    refine ⟨4634173176440419879344697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178897568587226505792929 4634173176440419879344697)
                    ·
                      refine ⟨3475629882330314909508523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634173176440419879344697 3475629882330314909508523)
                      ·
                        rfl

theorem cell23_6768765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_6768765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768765 prefixEnd_6768765 := by exact prefixLift 6768765
  have htrace : WordTrace (prefixWord ++ tailWord_6768765) baseStart_6768765 baseEnd_6768765 := by
    simpa [prefixWord, tailWord_6768765, baseEnd_6768765] using wordTrace_append hprefix tailTrace_6768765
  have hstable : (prefixWord ++ tailWord_6768765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768765).length < 2 ^ (prefixWord ++ tailWord_6768765).sum := by decide
  have hdescent : baseEnd_6768765 < baseStart_6768765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768782 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_6768782 : Nat := 118140960795 + 6768782 * 2 ^ 59
def prefixEnd_6768782 : Nat := 4983230072969 + 3 ^ 40 * 6768782 * 2
def baseEnd_6768782 : Nat := 3475638611501441342995945

theorem tailTrace_6768782 : CollatzResearch.WordTrace tailWord_6768782 prefixEnd_6768782 3475638611501441342995945 := by
  unfold tailWord_6768782
  simp only [CollatzResearch.WordTrace]
  refine ⟨30859720170483288096947575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164585174242577536517053733 30859720170483288096947575)
  ·
    refine ⟨46289580255724932145421363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30859720170483288096947575 46289580255724932145421363)
    ·
      refine ⟨69434370383587398218132045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46289580255724932145421363 69434370383587398218132045)
      ·
        refine ⟨26037888893845274331799517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69434370383587398218132045 26037888893845274331799517)
        ·
          refine ⟨9764208335191977874424819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26037888893845274331799517 9764208335191977874424819)
          ·
            refine ⟨14646312502787966811637229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764208335191977874424819 14646312502787966811637229)
            ·
              refine ⟨5492367188545487554363961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14646312502787966811637229 5492367188545487554363961)
              ·
                refine ⟨4119275391409115665772971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492367188545487554363961 4119275391409115665772971)
                ·
                  refine ⟨6178913087113673498659457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119275391409115665772971 6178913087113673498659457)
                  ·
                    refine ⟨4634184815335255123994593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6178913087113673498659457 4634184815335255123994593)
                    ·
                      refine ⟨3475638611501441342995945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634184815335255123994593 3475638611501441342995945)
                      ·
                        rfl

theorem cell23_6768782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_6768782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768782 prefixEnd_6768782 := by exact prefixLift 6768782
  have htrace : WordTrace (prefixWord ++ tailWord_6768782) baseStart_6768782 baseEnd_6768782 := by
    simpa [prefixWord, tailWord_6768782, baseEnd_6768782] using wordTrace_append hprefix tailTrace_6768782
  have hstable : (prefixWord ++ tailWord_6768782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768782).length < 2 ^ (prefixWord ++ tailWord_6768782).sum := by decide
  have hdescent : baseEnd_6768782 < baseStart_6768782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768857 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_6768857 : Nat := 118140960795 + 6768857 * 2 ^ 59
def prefixEnd_6768857 : Nat := 4983230072969 + 3 ^ 40 * 6768857 * 2
def baseEnd_6768857 : Nat := 1158559040850176183186033

theorem tailTrace_6768857 : CollatzResearch.WordTrace tailWord_6768857 prefixEnd_6768857 1158559040850176183186033 := by
  unfold tailWord_6768857
  simp only [CollatzResearch.WordTrace]
  refine ⟨246880496838594592584560825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164586997892396395056373883 246880496838594592584560825)
  ·
    refine ⟨185160372628945944438420619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246880496838594592584560825 185160372628945944438420619)
    ·
      refine ⟨277740558943418916657630929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185160372628945944438420619 277740558943418916657630929)
      ·
        refine ⟨208305419207564187493223197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277740558943418916657630929 208305419207564187493223197)
        ·
          refine ⟨78114532202836570309958699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208305419207564187493223197 78114532202836570309958699)
          ·
            refine ⟨117171798304254855464938049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78114532202836570309958699 117171798304254855464938049)
            ·
              refine ⟨87878848728191141598703537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117171798304254855464938049 87878848728191141598703537)
              ·
                refine ⟨65909136546143356199027653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87878848728191141598703537 65909136546143356199027653)
                ·
                  refine ⟨12357963102401879287317685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65909136546143356199027653 12357963102401879287317685)
                  ·
                    refine ⟨1158559040850176183186033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12357963102401879287317685 1158559040850176183186033)
                    ·
                      rfl

theorem cell23_6768857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_6768857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768857 prefixEnd_6768857 := by exact prefixLift 6768857
  have htrace : WordTrace (prefixWord ++ tailWord_6768857) baseStart_6768857 baseEnd_6768857 := by
    simpa [prefixWord, tailWord_6768857, baseEnd_6768857] using wordTrace_append hprefix tailTrace_6768857
  have hstable : (prefixWord ++ tailWord_6768857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768857).length < 2 ^ (prefixWord ++ tailWord_6768857).sum := by decide
  have hdescent : baseEnd_6768857 < baseStart_6768857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768864 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2]
def baseStart_6768864 : Nat := 118140960795 + 6768864 * 2 ^ 59
def prefixEnd_6768864 : Nat := 4983230072969 + 3 ^ 40 * 6768864 * 2
def baseEnd_6768864 : Nat := 3475680716915110022170567

theorem tailTrace_6768864 : CollatzResearch.WordTrace tailWord_6768864 prefixEnd_6768864 3475680716915110022170567 := by
  unfold tailWord_6768864
  simp only [CollatzResearch.WordTrace]
  refine ⟨123440376074784616390032823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164587168099712821853377097 123440376074784616390032823)
  ·
    refine ⟨185160564112176924585049235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123440376074784616390032823 185160564112176924585049235)
    ·
      refine ⟨277740846168265386877573853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185160564112176924585049235 277740846168265386877573853)
      ·
        refine ⟨104152817313099520079090195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277740846168265386877573853 104152817313099520079090195)
        ·
          refine ⟨156229225969649280118635293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104152817313099520079090195 156229225969649280118635293)
          ·
            refine ⟨58585959738618480044488235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156229225969649280118635293 58585959738618480044488235)
            ·
              refine ⟨87878939607927720066732353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58585959738618480044488235 87878939607927720066732353)
              ·
                refine ⟨65909204705945790050049265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87878939607927720066732353 65909204705945790050049265)
                ·
                  refine ⟨49431903529459342537536949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65909204705945790050049265 49431903529459342537536949)
                  ·
                    refine ⟨4634240955886813362894089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49431903529459342537536949 4634240955886813362894089)
                    ·
                      refine ⟨3475680716915110022170567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634240955886813362894089 3475680716915110022170567)
                      ·
                        rfl

theorem cell23_6768864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_6768864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768864 prefixEnd_6768864 := by exact prefixLift 6768864
  have htrace : WordTrace (prefixWord ++ tailWord_6768864) baseStart_6768864 baseEnd_6768864 := by
    simpa [prefixWord, tailWord_6768864, baseEnd_6768864] using wordTrace_append hprefix tailTrace_6768864
  have hstable : (prefixWord ++ tailWord_6768864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768864).length < 2 ^ (prefixWord ++ tailWord_6768864).sum := by decide
  have hdescent : baseEnd_6768864 < baseStart_6768864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768907 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_6768907 : Nat := 118140960795 + 6768907 * 2 ^ 59
def prefixEnd_6768907 : Nat := 4983230072969 + 3 ^ 40 * 6768907 * 2
def baseEnd_6768907 : Nat := 3475702796583253353932869

theorem tailTrace_6768907 : CollatzResearch.WordTrace tailWord_6768907 prefixEnd_6768907 3475702796583253353932869 := by
  unfold tailWord_6768907
  simp only [CollatzResearch.WordTrace]
  refine ⟨246882320488413451123880975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164588213658942300749253983 246882320488413451123880975)
  ·
    refine ⟨370323480732620176685821463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246882320488413451123880975 370323480732620176685821463)
    ·
      refine ⟨555485221098930265028732195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370323480732620176685821463 555485221098930265028732195)
      ·
        refine ⟨833227831648395397543098293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555485221098930265028732195 833227831648395397543098293)
        ·
          refine ⟨78115109217037068519665465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 833227831648395397543098293 78115109217037068519665465)
          ·
            refine ⟨58586331912777801389749099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78115109217037068519665465 58586331912777801389749099)
            ·
              refine ⟨87879497869166702084623649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58586331912777801389749099 87879497869166702084623649)
              ·
                refine ⟨65909623401875026563467737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87879497869166702084623649 65909623401875026563467737)
                ·
                  refine ⟨49432217551406269922600803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65909623401875026563467737 49432217551406269922600803)
                  ·
                    refine ⟨74148326327109404883901205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49432217551406269922600803 74148326327109404883901205)
                    ·
                      refine ⟨3475702796583253353932869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74148326327109404883901205 3475702796583253353932869)
                      ·
                        rfl

theorem cell23_6768907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_6768907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768907 prefixEnd_6768907 := by exact prefixLift 6768907
  have htrace : WordTrace (prefixWord ++ tailWord_6768907) baseStart_6768907 baseEnd_6768907 := by
    simpa [prefixWord, tailWord_6768907, baseEnd_6768907] using wordTrace_append hprefix tailTrace_6768907
  have hstable : (prefixWord ++ tailWord_6768907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768907).length < 2 ^ (prefixWord ++ tailWord_6768907).sum := by decide
  have hdescent : baseEnd_6768907 < baseStart_6768907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768948 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_6768948 : Nat := 118140960795 + 6768948 * 2 ^ 59
def prefixEnd_6768948 : Nat := 4983230072969 + 3 ^ 40 * 6768948 * 2
def baseEnd_6768948 : Nat := 3475723849290087693520181

theorem tailTrace_6768948 : CollatzResearch.WordTrace tailWord_6768948 prefixEnd_6768948 3475723849290087693520181 := by
  unfold tailWord_6768948
  simp only [CollatzResearch.WordTrace]
  refine ⟨123441907940632457563061749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164589210587509943417415665 123441907940632457563061749)
  ·
    refine ⟨11572678869434292896537039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123441907940632457563061749 11572678869434292896537039)
    ·
      refine ⟨17359018304151439344805559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11572678869434292896537039 17359018304151439344805559)
      ·
        refine ⟨26038527456227159017208339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17359018304151439344805559 26038527456227159017208339)
        ·
          refine ⟨39057791184340738525812509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26038527456227159017208339 39057791184340738525812509)
          ·
            refine ⟨14646671694127776947179691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39057791184340738525812509 14646671694127776947179691)
            ·
              refine ⟨21970007541191665420769537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646671694127776947179691 21970007541191665420769537)
              ·
                refine ⟨16477505655893749065577153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21970007541191665420769537 16477505655893749065577153)
                ·
                  refine ⟨12358129241920311799182865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16477505655893749065577153 12358129241920311799182865)
                  ·
                    refine ⟨9268596931440233849387149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12358129241920311799182865 9268596931440233849387149)
                    ·
                      refine ⟨3475723849290087693520181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9268596931440233849387149 3475723849290087693520181)
                      ·
                        rfl

theorem cell23_6768948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_6768948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768948 prefixEnd_6768948 := by exact prefixLift 6768948
  have htrace : WordTrace (prefixWord ++ tailWord_6768948) baseStart_6768948 baseEnd_6768948 := by
    simpa [prefixWord, tailWord_6768948, baseEnd_6768948] using wordTrace_append hprefix tailTrace_6768948
  have hstable : (prefixWord ++ tailWord_6768948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768948).length < 2 ^ (prefixWord ++ tailWord_6768948).sum := by decide
  have hdescent : baseEnd_6768948 < baseStart_6768948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768981 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_6768981 : Nat := 118140960795 + 6768981 * 2 ^ 59
def prefixEnd_6768981 : Nat := 4983230072969 + 3 ^ 40 * 6768981 * 2
def baseEnd_6768981 : Nat := 1158580264717228688135843

theorem tailTrace_6768981 : CollatzResearch.WordTrace tailWord_6768981 prefixEnd_6768981 1158580264717228688135843 := by
  unfold tailWord_6768981
  simp only [CollatzResearch.WordTrace]
  refine ⟨246885019490145361762074797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164590012993430241174716531 246885019490145361762074797)
  ·
    refine ⟨92581882308804510660778049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246885019490145361762074797 92581882308804510660778049)
    ·
      refine ⟨69436411731603382995583537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92581882308804510660778049 69436411731603382995583537)
      ·
        refine ⟨52077308798702537246687653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69436411731603382995583537 52077308798702537246687653)
        ·
          refine ⟨9764495399756725733753935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52077308798702537246687653 9764495399756725733753935)
          ·
            refine ⟨14646743099635088600630903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764495399756725733753935 14646743099635088600630903)
            ·
              refine ⟨21970114649452632900946355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14646743099635088600630903 21970114649452632900946355)
              ·
                refine ⟨32955171974178949351419533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21970114649452632900946355 32955171974178949351419533)
                ·
                  refine ⟨12358189490317106006782325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32955171974178949351419533 12358189490317106006782325)
                  ·
                    refine ⟨1158580264717228688135843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12358189490317106006782325 1158580264717228688135843)
                    ·
                      rfl

theorem cell23_6768981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_6768981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6768981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6768981 prefixEnd_6768981 := by exact prefixLift 6768981
  have htrace : WordTrace (prefixWord ++ tailWord_6768981) baseStart_6768981 baseEnd_6768981 := by
    simpa [prefixWord, tailWord_6768981, baseEnd_6768981] using wordTrace_append hprefix tailTrace_6768981
  have hstable : (prefixWord ++ tailWord_6768981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768981).length < 2 ^ (prefixWord ++ tailWord_6768981).sum := by decide
  have hdescent : baseEnd_6768981 < baseStart_6768981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769021 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_6769021 : Nat := 118140960795 + 6769021 * 2 ^ 59
def prefixEnd_6769021 : Nat := 4983230072969 + 3 ^ 40 * 6769021 * 2
def baseEnd_6769021 : Nat := 3475761333377865907907345

theorem tailTrace_6769021 : CollatzResearch.WordTrace tailWord_6769021 prefixEnd_6769021 3475761333377865907907345 := by
  unfold tailWord_6769021
  simp only [CollatzResearch.WordTrace]
  refine ⟨246886478410000448593530917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164590985606666965729020611 246886478410000448593530917)
  ·
    refine ⟨46291214701875084111287047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246886478410000448593530917 46291214701875084111287047)
    ·
      refine ⟨69436822052812626166930571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46291214701875084111287047 69436822052812626166930571)
      ·
        refine ⟨104155233079218939250395857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69436822052812626166930571 104155233079218939250395857)
        ·
          refine ⟨78116424809414204437796893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104155233079218939250395857 78116424809414204437796893)
          ·
            refine ⟨29293659303530326664173835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78116424809414204437796893 29293659303530326664173835)
            ·
              refine ⟨43940488955295489996260753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29293659303530326664173835 43940488955295489996260753)
              ·
                refine ⟨32955366716471617497195565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43940488955295489996260753 32955366716471617497195565)
                ·
                  refine ⟨12358262518676856561448337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32955366716471617497195565 12358262518676856561448337)
                  ·
                    refine ⟨9268696889007642421086253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12358262518676856561448337 9268696889007642421086253)
                    ·
                      refine ⟨3475761333377865907907345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9268696889007642421086253 3475761333377865907907345)
                      ·
                        rfl

theorem cell23_6769021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_6769021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769021 prefixEnd_6769021 := by exact prefixLift 6769021
  have htrace : WordTrace (prefixWord ++ tailWord_6769021) baseStart_6769021 baseEnd_6769021 := by
    simpa [prefixWord, tailWord_6769021, baseEnd_6769021] using wordTrace_append hprefix tailTrace_6769021
  have hstable : (prefixWord ++ tailWord_6769021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769021).length < 2 ^ (prefixWord ++ tailWord_6769021).sum := by decide
  have hdescent : baseEnd_6769021 < baseStart_6769021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769031 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_6769031 : Nat := 118140960795 + 6769031 * 2 ^ 59
def prefixEnd_6769031 : Nat := 4983230072969 + 3 ^ 40 * 6769031 * 2
def baseEnd_6769031 : Nat := 3475766468184410868782299

theorem tailTrace_6769031 : CollatzResearch.WordTrace tailWord_6769031 prefixEnd_6769031 3475766468184410868782299 := by
  unfold tailWord_6769031
  simp only [CollatzResearch.WordTrace]
  refine ⟨246886843139964220301394947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164591228759976146867596631 246886843139964220301394947)
  ·
    refine ⟨370330264709946330452092421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246886843139964220301394947 370330264709946330452092421)
    ·
      refine ⟨69436924633114936959767329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370330264709946330452092421 69436924633114936959767329)
      ·
        refine ⟨52077693474836202719825497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69436924633114936959767329 52077693474836202719825497)
        ·
          refine ⟨39058270106127152039869123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52077693474836202719825497 39058270106127152039869123)
          ·
            refine ⟨58587405159190728059803685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39058270106127152039869123 58587405159190728059803685)
            ·
              refine ⟨10985138467348261511213191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58587405159190728059803685 10985138467348261511213191)
              ·
                refine ⟨16477707701022392266819787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10985138467348261511213191 16477707701022392266819787)
                ·
                  refine ⟨24716561551533588400229681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16477707701022392266819787 24716561551533588400229681)
                  ·
                    refine ⟨18537421163650191300172261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24716561551533588400229681 18537421163650191300172261)
                    ·
                      refine ⟨3475766468184410868782299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18537421163650191300172261 3475766468184410868782299)
                      ·
                        rfl

theorem cell23_6769031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_6769031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769031 prefixEnd_6769031 := by exact prefixLift 6769031
  have htrace : WordTrace (prefixWord ++ tailWord_6769031) baseStart_6769031 baseEnd_6769031 := by
    simpa [prefixWord, tailWord_6769031, baseEnd_6769031] using wordTrace_append hprefix tailTrace_6769031
  have hstable : (prefixWord ++ tailWord_6769031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769031).length < 2 ^ (prefixWord ++ tailWord_6769031).sum := by decide
  have hdescent : baseEnd_6769031 < baseStart_6769031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769038 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6769038 : Nat := 118140960795 + 6769038 * 2 ^ 59
def prefixEnd_6769038 : Nat := 4983230072969 + 3 ^ 40 * 6769038 * 2
def baseEnd_6769038 : Nat := 3475770062548992341394767

theorem tailTrace_6769038 : CollatzResearch.WordTrace tailWord_6769038 prefixEnd_6769038 3475770062548992341394767 := by
  unfold tailWord_6769038
  simp only [CollatzResearch.WordTrace]
  refine ⟨30860887306367357562112471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164591398967292573664599845 30860887306367357562112471)
  ·
    refine ⟨46291330959551036343168707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30860887306367357562112471 46291330959551036343168707)
    ·
      refine ⟨69436996439326554514753061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46291330959551036343168707 69436996439326554514753061)
      ·
        refine ⟨13019436832373728971516199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69436996439326554514753061 13019436832373728971516199)
        ·
          refine ⟨19529155248560593457274299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13019436832373728971516199 19529155248560593457274299)
          ·
            refine ⟨29293732872840890185911449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19529155248560593457274299 29293732872840890185911449)
            ·
              refine ⟨21970299654630667639433587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29293732872840890185911449 21970299654630667639433587)
              ·
                refine ⟨32955449481946001459150381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21970299654630667639433587 32955449481946001459150381)
                ·
                  refine ⟨12358293555729750547181393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32955449481946001459150381 12358293555729750547181393)
                  ·
                    refine ⟨9268720166797312910386045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12358293555729750547181393 9268720166797312910386045)
                    ·
                      refine ⟨3475770062548992341394767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9268720166797312910386045 3475770062548992341394767)
                      ·
                        rfl

theorem cell23_6769038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6769038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769038 prefixEnd_6769038 := by exact prefixLift 6769038
  have htrace : WordTrace (prefixWord ++ tailWord_6769038) baseStart_6769038 baseEnd_6769038 := by
    simpa [prefixWord, tailWord_6769038, baseEnd_6769038] using wordTrace_append hprefix tailTrace_6769038
  have hstable : (prefixWord ++ tailWord_6769038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769038).length < 2 ^ (prefixWord ++ tailWord_6769038).sum := by decide
  have hdescent : baseEnd_6769038 < baseStart_6769038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769089 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6769089 : Nat := 118140960795 + 6769089 * 2 ^ 59
def prefixEnd_6769089 : Nat := 4983230072969 + 3 ^ 40 * 6769089 * 2
def baseEnd_6769089 : Nat := 3475796250062371641857033

theorem tailTrace_6769089 : CollatzResearch.WordTrace tailWord_6769089 prefixEnd_6769089 3475796250062371641857033 := by
  unfold tailWord_6769089
  simp only [CollatzResearch.WordTrace]
  refine ⟨246888958573754096207006321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164592639049169397471337547 246888958573754096207006321)
  ·
    refine ⟨185166718930315572155254741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246888958573754096207006321 185166718930315572155254741)
    ·
      refine ⟨4339844974929271222388783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 185166718930315572155254741 4339844974929271222388783)
      ·
        refine ⟨6509767462393906833583175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339844974929271222388783 6509767462393906833583175)
        ·
          refine ⟨9764651193590860250374763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509767462393906833583175 9764651193590860250374763)
          ·
            refine ⟨14646976790386290375562145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764651193590860250374763 14646976790386290375562145)
            ·
              refine ⟨10985232592789717781671609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14646976790386290375562145 10985232592789717781671609)
              ·
                refine ⟨8238924444592288336253707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985232592789717781671609 8238924444592288336253707)
                ·
                  refine ⟨12358386666888432504380561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238924444592288336253707 12358386666888432504380561)
                  ·
                    refine ⟨9268790000166324378285421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12358386666888432504380561 9268790000166324378285421)
                    ·
                      refine ⟨3475796250062371641857033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9268790000166324378285421 3475796250062371641857033)
                      ·
                        rfl

theorem cell23_6769089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6769089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769089 prefixEnd_6769089 := by exact prefixLift 6769089
  have htrace : WordTrace (prefixWord ++ tailWord_6769089) baseStart_6769089 baseEnd_6769089 := by
    simpa [prefixWord, tailWord_6769089, baseEnd_6769089] using wordTrace_append hprefix tailTrace_6769089
  have hstable : (prefixWord ++ tailWord_6769089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769089).length < 2 ^ (prefixWord ++ tailWord_6769089).sum := by decide
  have hdescent : baseEnd_6769089 < baseStart_6769089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769095 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_6769095 : Nat := 118140960795 + 6769095 * 2 ^ 59
def prefixEnd_6769095 : Nat := 4983230072969 + 3 ^ 40 * 6769095 * 2
def baseEnd_6769095 : Nat := 3475799330946298618382005

theorem tailTrace_6769095 : CollatzResearch.WordTrace tailWord_6769095 prefixEnd_6769095 3475799330946298618382005 := by
  unfold tailWord_6769095
  simp only [CollatzResearch.WordTrace]
  refine ⟨246889177411732359231724739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164592784941154906154483159 246889177411732359231724739)
  ·
    refine ⟨370333766117598538847587109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246889177411732359231724739 370333766117598538847587109)
    ·
      refine ⟨69437581147049726033922583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 370333766117598538847587109 69437581147049726033922583)
      ·
        refine ⟨104156371720574589050883875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69437581147049726033922583 104156371720574589050883875)
        ·
          refine ⟨156234557580861883576325813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104156371720574589050883875 156234557580861883576325813)
          ·
            refine ⟨14646989773205801585280545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156234557580861883576325813 14646989773205801585280545)
            ·
              refine ⟨10985242329904351188960409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14646989773205801585280545 10985242329904351188960409)
              ·
                refine ⟨8238931747428263391720307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985242329904351188960409 8238931747428263391720307)
                ·
                  refine ⟨12358397621142395087580461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238931747428263391720307 12358397621142395087580461)
                  ·
                    refine ⟨4634399107928398157842673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12358397621142395087580461 4634399107928398157842673)
                    ·
                      refine ⟨3475799330946298618382005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634399107928398157842673 3475799330946298618382005)
                      ·
                        rfl

theorem cell23_6769095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_6769095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769095 prefixEnd_6769095 := by exact prefixLift 6769095
  have htrace : WordTrace (prefixWord ++ tailWord_6769095) baseStart_6769095 baseEnd_6769095 := by
    simpa [prefixWord, tailWord_6769095, baseEnd_6769095] using wordTrace_append hprefix tailTrace_6769095
  have hstable : (prefixWord ++ tailWord_6769095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769095).length < 2 ^ (prefixWord ++ tailWord_6769095).sum := by decide
  have hdescent : baseEnd_6769095 < baseStart_6769095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769142 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6769142 : Nat := 118140960795 + 6769142 * 2 ^ 59
def prefixEnd_6769142 : Nat := 4983230072969 + 3 ^ 40 * 6769142 * 2
def baseEnd_6769142 : Nat := 3475823464537059934494289

theorem tailTrace_6769142 : CollatzResearch.WordTrace tailWord_6769142 prefixEnd_6769142 3475823464537059934494289 := by
  unfold tailWord_6769142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430680727660130391167855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164593927761708057505790453 15430680727660130391167855)
  ·
    refine ⟨23146021091490195586751783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15430680727660130391167855 23146021091490195586751783)
    ·
      refine ⟨34719031637235293380127675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23146021091490195586751783 34719031637235293380127675)
      ·
        refine ⟨52078547455852940070191513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34719031637235293380127675 52078547455852940070191513)
        ·
          refine ⟨39058910591889705052643635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52078547455852940070191513 39058910591889705052643635)
          ·
            refine ⟨58588365887834557578965453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39058910591889705052643635 58588365887834557578965453)
            ·
              refine ⟨21970637207937959092112045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58588365887834557578965453 21970637207937959092112045)
              ·
                refine ⟨8238988952976734659542017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21970637207937959092112045 8238988952976734659542017)
                ·
                  refine ⟨6179241714732550994656513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238988952976734659542017 6179241714732550994656513)
                  ·
                    refine ⟨4634431286049413245992385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6179241714732550994656513 4634431286049413245992385)
                    ·
                      refine ⟨3475823464537059934494289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634431286049413245992385 3475823464537059934494289)
                      ·
                        rfl

theorem cell23_6769142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6769142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769142 prefixEnd_6769142 := by exact prefixLift 6769142
  have htrace : WordTrace (prefixWord ++ tailWord_6769142) baseStart_6769142 baseEnd_6769142 := by
    simpa [prefixWord, tailWord_6769142, baseEnd_6769142] using wordTrace_append hprefix tailTrace_6769142
  have hstable : (prefixWord ++ tailWord_6769142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769142).length < 2 ^ (prefixWord ++ tailWord_6769142).sum := by decide
  have hdescent : baseEnd_6769142 < baseStart_6769142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769208 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_6769208 : Nat := 118140960795 + 6769208 * 2 ^ 59
def prefixEnd_6769208 : Nat := 4983230072969 + 3 ^ 40 * 6769208 * 2
def baseEnd_6769208 : Nat := 1158619118086752225422995

theorem tailTrace_6769208 : CollatzResearch.WordTrace tailWord_6769208 prefixEnd_6769208 1158619118086752225422995 := by
  unfold tailWord_6769208
  simp only [CollatzResearch.WordTrace]
  refine ⟨123446649430161489765294139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164595532573548653020392185 123446649430161489765294139)
  ·
    refine ⟨185169974145242234647941209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123446649430161489765294139 185169974145242234647941209)
    ·
      refine ⟨138877480608931675985955907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185169974145242234647941209 138877480608931675985955907)
      ·
        refine ⟨208316220913397513978933861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138877480608931675985955907 208316220913397513978933861)
        ·
          refine ⟨39059291421262033871050099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208316220913397513978933861 39059291421262033871050099)
          ·
            refine ⟨58588937131893050806575149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39059291421262033871050099 58588937131893050806575149)
            ·
              refine ⟨21970851424459894052465681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58588937131893050806575149 21970851424459894052465681)
              ·
                refine ⟨16478138568344920539349261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21970851424459894052465681 16478138568344920539349261)
                ·
                  refine ⟨6179301963129345202255973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16478138568344920539349261 6179301963129345202255973)
                  ·
                    refine ⟨1158619118086752225422995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179301963129345202255973 1158619118086752225422995)
                    ·
                      rfl

theorem cell23_6769208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_6769208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769208 prefixEnd_6769208 := by exact prefixLift 6769208
  have htrace : WordTrace (prefixWord ++ tailWord_6769208) baseStart_6769208 baseEnd_6769208 := by
    simpa [prefixWord, tailWord_6769208, baseEnd_6769208] using wordTrace_append hprefix tailTrace_6769208
  have hstable : (prefixWord ++ tailWord_6769208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769208).length < 2 ^ (prefixWord ++ tailWord_6769208).sum := by decide
  have hdescent : baseEnd_6769208 < baseStart_6769208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769319 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6769319 : Nat := 118140960795 + 6769319 * 2 ^ 59
def prefixEnd_6769319 : Nat := 4983230072969 + 3 ^ 40 * 6769319 * 2
def baseEnd_6769319 : Nat := 1158638116870968580660325

theorem tailTrace_6769319 : CollatzResearch.WordTrace tailWord_6769319 prefixEnd_6769319 1158638116870968580660325 := by
  unfold tailWord_6769319
  simp only [CollatzResearch.WordTrace]
  refine ⟨246897347362920845487879011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164598231575280563658586007 246897347362920845487879011)
  ·
    refine ⟨370346021044381268231818517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246897347362920845487879011 370346021044381268231818517)
    ·
      refine ⟨17359969736455371948366493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 370346021044381268231818517 17359969736455371948366493)
      ·
        refine ⟨6509988651170764480637435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17359969736455371948366493 6509988651170764480637435)
        ·
          refine ⟨9764982976756146720956153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509988651170764480637435 9764982976756146720956153)
          ·
            refine ⟨7323737232567110040717115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9764982976756146720956153 7323737232567110040717115)
            ·
              refine ⟨10985605848850665061075673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323737232567110040717115 10985605848850665061075673)
              ·
                refine ⟨8239204386637998795806755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985605848850665061075673 8239204386637998795806755)
                ·
                  refine ⟨12358806579956998193710133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8239204386637998795806755 12358806579956998193710133)
                  ·
                    refine ⟨1158638116870968580660325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12358806579956998193710133 1158638116870968580660325)
                    ·
                      rfl

theorem cell23_6769319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6769319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769319 prefixEnd_6769319 := by exact prefixLift 6769319
  have htrace : WordTrace (prefixWord ++ tailWord_6769319) baseStart_6769319 baseEnd_6769319 := by
    simpa [prefixWord, tailWord_6769319, baseEnd_6769319] using wordTrace_append hprefix tailTrace_6769319
  have hstable : (prefixWord ++ tailWord_6769319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769319).length < 2 ^ (prefixWord ++ tailWord_6769319).sum := by decide
  have hdescent : baseEnd_6769319 < baseStart_6769319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769335 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_6769335 : Nat := 118140960795 + 6769335 * 2 ^ 59
def prefixEnd_6769335 : Nat := 4983230072969 + 3 ^ 40 * 6769335 * 2
def baseEnd_6769335 : Nat := 3475922566303377679380901

theorem tailTrace_6769335 : CollatzResearch.WordTrace tailWord_6769335 prefixEnd_6769335 3475922566303377679380901 := by
  unfold tailWord_6769335
  simp only [CollatzResearch.WordTrace]
  refine ⟨246897930930862880220461459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164598620620575253480307639 246897930930862880220461459)
  ·
    refine ⟨370346896396294320330692189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246897930930862880220461459 370346896396294320330692189)
    ·
      refine ⟨138880086148610370124009571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370346896396294320330692189 138880086148610370124009571)
      ·
        refine ⟨208320129222915555186014357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138880086148610370124009571 208320129222915555186014357)
        ·
          refine ⟨9765006057324166649344423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208320129222915555186014357 9765006057324166649344423)
          ·
            refine ⟨14647509085986249974016635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765006057324166649344423 14647509085986249974016635)
            ·
              refine ⟨21971263628979374961024953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14647509085986249974016635 21971263628979374961024953)
              ·
                refine ⟨16478447721734531220768715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21971263628979374961024953 16478447721734531220768715)
                ·
                  refine ⟨24717671582601796831153073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16478447721734531220768715 24717671582601796831153073)
                  ·
                    refine ⟨18538253686951347623364805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24717671582601796831153073 18538253686951347623364805)
                    ·
                      refine ⟨3475922566303377679380901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18538253686951347623364805 3475922566303377679380901)
                      ·
                        rfl

theorem cell23_6769335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_6769335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769335 prefixEnd_6769335 := by exact prefixLift 6769335
  have htrace : WordTrace (prefixWord ++ tailWord_6769335) baseStart_6769335 baseEnd_6769335 := by
    simpa [prefixWord, tailWord_6769335, baseEnd_6769335] using wordTrace_append hprefix tailTrace_6769335
  have hstable : (prefixWord ++ tailWord_6769335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769335).length < 2 ^ (prefixWord ++ tailWord_6769335).sum := by decide
  have hdescent : baseEnd_6769335 < baseStart_6769335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769345 : List Nat := [1, 2, 6, 2, 1, 11]
def baseStart_6769345 : Nat := 118140960795 + 6769345 * 2 ^ 59
def prefixEnd_6769345 : Nat := 4983230072969 + 3 ^ 40 * 6769345 * 2
def baseEnd_6769345 : Nat := 14304229222674578766485

theorem tailTrace_6769345 : CollatzResearch.WordTrace tailWord_6769345 prefixEnd_6769345 14304229222674578766485 := by
  unfold tailWord_6769345
  simp only [CollatzResearch.WordTrace]
  refine ⟨246898295660826651928325489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164598863773884434618883659 246898295660826651928325489)
  ·
    refine ⟨185173721745619988946244117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246898295660826651928325489 185173721745619988946244117)
    ·
      refine ⟨8680018206825936981855193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185173721745619988946244117 8680018206825936981855193)
      ·
        refine ⟨6510013655119452736391395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8680018206825936981855193 6510013655119452736391395)
        ·
          refine ⟨9765020482679179104587093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510013655119452736391395 9765020482679179104587093)
          ·
            refine ⟨14304229222674578766485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9765020482679179104587093 14304229222674578766485)
            ·
              rfl

theorem cell23_6769345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 11].length) (baseStart_6769345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769345 prefixEnd_6769345 := by exact prefixLift 6769345
  have htrace : WordTrace (prefixWord ++ tailWord_6769345) baseStart_6769345 baseEnd_6769345 := by
    simpa [prefixWord, tailWord_6769345, baseEnd_6769345] using wordTrace_append hprefix tailTrace_6769345
  have hstable : (prefixWord ++ tailWord_6769345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769345).length < 2 ^ (prefixWord ++ tailWord_6769345).sum := by decide
  have hdescent : baseEnd_6769345 < baseStart_6769345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769356 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6769356 : Nat := 118140960795 + 6769356 * 2 ^ 59
def prefixEnd_6769356 : Nat := 4983230072969 + 3 ^ 40 * 6769356 * 2
def baseEnd_6769356 : Nat := 3475933349397122097218305

theorem tailTrace_6769356 : CollatzResearch.WordTrace tailWord_6769356 prefixEnd_6769356 3475933349397122097218305 := by
  unfold tailWord_6769356
  simp only [CollatzResearch.WordTrace]
  refine ⟨123449348431893400403487961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164599131242524533871317281 123449348431893400403487961)
  ·
    refine ⟨92587011323920050302615971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123449348431893400403487961 92587011323920050302615971)
    ·
      refine ⟨138880516985880075453923957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92587011323920050302615971 138880516985880075453923957)
      ·
        refine ⟨13020048467426257073805371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138880516985880075453923957 13020048467426257073805371)
        ·
          refine ⟨19530072701139385610708057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13020048467426257073805371 19530072701139385610708057)
          ·
            refine ⟨14647554525854539208031043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19530072701139385610708057 14647554525854539208031043)
            ·
              refine ⟨21971331788781808812046565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14647554525854539208031043 21971331788781808812046565)
              ·
                refine ⟨4119624710396589152258731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21971331788781808812046565 4119624710396589152258731)
                ·
                  refine ⟨6179437065594883728388097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119624710396589152258731 6179437065594883728388097)
                  ·
                    refine ⟨4634577799196162796291073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6179437065594883728388097 4634577799196162796291073)
                    ·
                      refine ⟨3475933349397122097218305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634577799196162796291073 3475933349397122097218305)
                      ·
                        rfl

theorem cell23_6769356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6769356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769356 prefixEnd_6769356 := by exact prefixLift 6769356
  have htrace : WordTrace (prefixWord ++ tailWord_6769356) baseStart_6769356 baseEnd_6769356 := by
    simpa [prefixWord, tailWord_6769356, baseEnd_6769356] using wordTrace_append hprefix tailTrace_6769356
  have hstable : (prefixWord ++ tailWord_6769356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769356).length < 2 ^ (prefixWord ++ tailWord_6769356).sum := by decide
  have hdescent : baseEnd_6769356 < baseStart_6769356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769358 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_6769358 : Nat := 118140960795 + 6769358 * 2 ^ 59
def prefixEnd_6769358 : Nat := 4983230072969 + 3 ^ 40 * 6769358 * 2
def baseEnd_6769358 : Nat := 1158644792119477029797765

theorem tailTrace_6769358 : CollatzResearch.WordTrace tailWord_6769358 prefixEnd_6769358 1158644792119477029797765 := by
  unfold tailWord_6769358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862346226222444393568591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164599179873186370099032485 30862346226222444393568591)
  ·
    refine ⟨46293519339333666590352887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30862346226222444393568591 46293519339333666590352887)
    ·
      refine ⟨69440279009000499885529331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46293519339333666590352887 69440279009000499885529331)
      ·
        refine ⟨104160418513500749828293997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69440279009000499885529331 104160418513500749828293997)
        ·
          refine ⟨39060156942562781185610249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104160418513500749828293997 39060156942562781185610249)
          ·
            refine ⟨29295117706922085889207687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39060156942562781185610249 29295117706922085889207687)
            ·
              refine ⟨43942676560383128833811531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29295117706922085889207687 43942676560383128833811531)
              ·
                refine ⟨65914014840574693250717297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43942676560383128833811531 65914014840574693250717297)
                ·
                  refine ⟨49435511130431019938037973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65914014840574693250717297 49435511130431019938037973)
                  ·
                    refine ⟨1158644792119477029797765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49435511130431019938037973 1158644792119477029797765)
                    ·
                      rfl

theorem cell23_6769358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_6769358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769358 prefixEnd_6769358 := by exact prefixLift 6769358
  have htrace : WordTrace (prefixWord ++ tailWord_6769358) baseStart_6769358 baseEnd_6769358 := by
    simpa [prefixWord, tailWord_6769358, baseEnd_6769358] using wordTrace_append hprefix tailTrace_6769358
  have hstable : (prefixWord ++ tailWord_6769358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769358).length < 2 ^ (prefixWord ++ tailWord_6769358).sum := by decide
  have hdescent : baseEnd_6769358 < baseStart_6769358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769362 : List Nat := [3, 2, 2, 2, 4, 1, 1, 8]
def baseStart_6769362 : Nat := 118140960795 + 6769362 * 2 ^ 59
def prefixEnd_6769362 : Nat := 4983230072969 + 3 ^ 40 * 6769362 * 2
def baseEnd_6769362 : Nat := 128738386306705521249751

theorem tailTrace_6769362 : CollatzResearch.WordTrace tailWord_6769362 prefixEnd_6769362 128738386306705521249751 := by
  unfold tailWord_6769362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61724728925441265957923585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164599277134510042554462893 61724728925441265957923585)
  ·
    refine ⟨46293546694080949468442689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61724728925441265957923585 46293546694080949468442689)
    ·
      refine ⟨34720160020560712101332017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46293546694080949468442689 34720160020560712101332017)
      ·
        refine ⟨26040120015420534075999013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34720160020560712101332017 26040120015420534075999013)
        ·
          refine ⟨4882522502891350139249815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26040120015420534075999013 4882522502891350139249815)
          ·
            refine ⟨7323783754337025208874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882522502891350139249815 7323783754337025208874723)
            ·
              refine ⟨10985675631505537813312085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323783754337025208874723 10985675631505537813312085)
              ·
                refine ⟨128738386306705521249751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10985675631505537813312085 128738386306705521249751)
                ·
                  rfl

theorem cell23_6769362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_6769362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769362 prefixEnd_6769362 := by exact prefixLift 6769362
  have htrace : WordTrace (prefixWord ++ tailWord_6769362) baseStart_6769362 baseEnd_6769362 := by
    simpa [prefixWord, tailWord_6769362, baseEnd_6769362] using wordTrace_append hprefix tailTrace_6769362
  have hstable : (prefixWord ++ tailWord_6769362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769362).length < 2 ^ (prefixWord ++ tailWord_6769362).sum := by decide
  have hdescent : baseEnd_6769362 < baseStart_6769362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769372 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6769372 : Nat := 118140960795 + 6769372 * 2 ^ 59
def prefixEnd_6769372 : Nat := 4983230072969 + 3 ^ 40 * 6769372 * 2
def baseEnd_6769372 : Nat := 3475941565087594034618231

theorem tailTrace_6769372 : CollatzResearch.WordTrace tailWord_6769372 prefixEnd_6769372 3475941565087594034618231 := by
  unfold tailWord_6769372
  simp only [CollatzResearch.WordTrace]
  refine ⟨123449640215864417769779185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164599520287819223693038913 123449640215864417769779185)
  ·
    refine ⟨92587230161898313327334389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123449640215864417769779185 92587230161898313327334389)
    ·
      refine ⟨8680052827677966874437599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92587230161898313327334389 8680052827677966874437599)
      ·
        refine ⟨13020079241516950311656399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8680052827677966874437599 13020079241516950311656399)
        ·
          refine ⟨19530118862275425467484599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13020079241516950311656399 19530118862275425467484599)
          ·
            refine ⟨29295178293413138201226899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19530118862275425467484599 29295178293413138201226899)
            ·
              refine ⟨43942767440119707301840349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29295178293413138201226899 43942767440119707301840349)
              ·
                refine ⟨16478537790044890238190131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43942767440119707301840349 16478537790044890238190131)
                ·
                  refine ⟨24717806685067335357285197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16478537790044890238190131 24717806685067335357285197)
                  ·
                    refine ⟨9269177506900250758981949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24717806685067335357285197 9269177506900250758981949)
                    ·
                      refine ⟨3475941565087594034618231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9269177506900250758981949 3475941565087594034618231)
                      ·
                        rfl

theorem cell23_6769372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6769372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769372 prefixEnd_6769372 := by exact prefixLift 6769372
  have htrace : WordTrace (prefixWord ++ tailWord_6769372) baseStart_6769372 baseEnd_6769372 := by
    simpa [prefixWord, tailWord_6769372, baseEnd_6769372] using wordTrace_append hprefix tailTrace_6769372
  have hstable : (prefixWord ++ tailWord_6769372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769372).length < 2 ^ (prefixWord ++ tailWord_6769372).sum := by decide
  have hdescent : baseEnd_6769372 < baseStart_6769372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769406 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6769406 : Nat := 118140960795 + 6769406 * 2 ^ 59
def prefixEnd_6769406 : Nat := 4983230072969 + 3 ^ 40 * 6769406 * 2
def baseEnd_6769406 : Nat := 3475959023429846901593075

theorem tailTrace_6769406 : CollatzResearch.WordTrace tailWord_6769406 prefixEnd_6769406 3475959023429846901593075 := by
  unfold tailWord_6769406
  simp only [CollatzResearch.WordTrace]
  refine ⟨30862565064200707418287009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164600347009070439564197381 30862565064200707418287009)
  ·
    refine ⟨23146923798150530563715257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30862565064200707418287009 23146923798150530563715257)
    ·
      refine ⟨17360192848612897922786443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23146923798150530563715257 17360192848612897922786443)
      ·
        refine ⟨26040289272919346884179665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17360192848612897922786443 26040289272919346884179665)
        ·
          refine ⟨19530216954689510163134749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26040289272919346884179665 19530216954689510163134749)
          ·
            refine ⟨7323831358008566311175531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19530216954689510163134749 7323831358008566311175531)
            ·
              refine ⟨10985747037012849466763297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323831358008566311175531 10985747037012849466763297)
              ·
                refine ⟨8239310277759637100072473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985747037012849466763297 8239310277759637100072473)
                ·
                  refine ⟨6179482708319727825054355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239310277759637100072473 6179482708319727825054355)
                  ·
                    refine ⟨9269224062479591737581533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6179482708319727825054355 9269224062479591737581533)
                    ·
                      refine ⟨3475959023429846901593075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9269224062479591737581533 3475959023429846901593075)
                      ·
                        rfl

theorem cell23_6769406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6769406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769406 prefixEnd_6769406 := by exact prefixLift 6769406
  have htrace : WordTrace (prefixWord ++ tailWord_6769406) baseStart_6769406 baseEnd_6769406 := by
    simpa [prefixWord, tailWord_6769406, baseEnd_6769406] using wordTrace_append hprefix tailTrace_6769406
  have hstable : (prefixWord ++ tailWord_6769406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769406).length < 2 ^ (prefixWord ++ tailWord_6769406).sum := by decide
  have hdescent : baseEnd_6769406 < baseStart_6769406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769469 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 7]
def baseStart_6769469 : Nat := 118140960795 + 6769469 * 2 ^ 59
def prefixEnd_6769469 : Nat := 4983230072969 + 3 ^ 40 * 6769469 * 2
def baseEnd_6769469 : Nat := 386221263634564461678365

theorem tailTrace_6769469 : CollatzResearch.WordTrace tailWord_6769469 prefixEnd_6769469 386221263634564461678365 := by
  unfold tailWord_6769469
  simp only [CollatzResearch.WordTrace]
  refine ⟨246902818312377421105839461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164601878874918280737226307 246902818312377421105839461)
  ·
    refine ⟨46294278433570766457344899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246902818312377421105839461 46294278433570766457344899)
    ·
      refine ⟨69441417650356149686017349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46294278433570766457344899 69441417650356149686017349)
      ·
        refine ⟨13020265809441778066128253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69441417650356149686017349 13020265809441778066128253)
        ·
          refine ⟨4882599678540666774798095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13020265809441778066128253 4882599678540666774798095)
          ·
            refine ⟨7323899517811000162197143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882599678540666774798095 7323899517811000162197143)
            ·
              refine ⟨10985849276716500243295715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323899517811000162197143 10985849276716500243295715)
              ·
                refine ⟨16478773915074750364943573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10985849276716500243295715 16478773915074750364943573)
                ·
                  refine ⟨386221263634564461678365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16478773915074750364943573 386221263634564461678365)
                  ·
                    rfl

theorem cell23_6769469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_6769469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769469 prefixEnd_6769469 := by exact prefixLift 6769469
  have htrace : WordTrace (prefixWord ++ tailWord_6769469) baseStart_6769469 baseEnd_6769469 := by
    simpa [prefixWord, tailWord_6769469, baseEnd_6769469] using wordTrace_append hprefix tailTrace_6769469
  have hstable : (prefixWord ++ tailWord_6769469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769469).length < 2 ^ (prefixWord ++ tailWord_6769469).sum := by decide
  have hdescent : baseEnd_6769469 < baseStart_6769469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769522 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_6769522 : Nat := 118140960795 + 6769522 * 2 ^ 59
def prefixEnd_6769522 : Nat := 4983230072969 + 3 ^ 40 * 6769522 * 2
def baseEnd_6769522 : Nat := 3476018587185768447742541

theorem tailTrace_6769522 : CollatzResearch.WordTrace tailWord_6769522 prefixEnd_6769522 3476018587185768447742541 := by
  unfold tailWord_6769522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61726187845296352789379705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164603167587456940771679213 61726187845296352789379705)
  ·
    refine ⟨46294640883972264592034779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61726187845296352789379705 46294640883972264592034779)
    ·
      refine ⟨69441961325958396888052169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46294640883972264592034779 69441961325958396888052169)
      ·
        refine ⟨52081470994468797666039127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69441961325958396888052169 52081470994468797666039127)
        ·
          refine ⟨78122206491703196499058691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52081470994468797666039127 78122206491703196499058691)
          ·
            refine ⟨117183309737554794748588037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78122206491703196499058691 117183309737554794748588037)
            ·
              refine ⟨21971870575791524015360257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117183309737554794748588037 21971870575791524015360257)
              ·
                refine ⟨16478902931843643011520193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21971870575791524015360257 16478902931843643011520193)
                ·
                  refine ⟨12359177198882732258640145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16478902931843643011520193 12359177198882732258640145)
                  ·
                    refine ⟨9269382899162049193980109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12359177198882732258640145 9269382899162049193980109)
                    ·
                      refine ⟨3476018587185768447742541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9269382899162049193980109 3476018587185768447742541)
                      ·
                        rfl

theorem cell23_6769522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_6769522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769522 prefixEnd_6769522 := by exact prefixLift 6769522
  have htrace : WordTrace (prefixWord ++ tailWord_6769522) baseStart_6769522 baseEnd_6769522 := by
    simpa [prefixWord, tailWord_6769522, baseEnd_6769522] using wordTrace_append hprefix tailTrace_6769522
  have hstable : (prefixWord ++ tailWord_6769522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769522).length < 2 ^ (prefixWord ++ tailWord_6769522).sum := by decide
  have hdescent : baseEnd_6769522 < baseStart_6769522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769529 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 1, 4]
def baseStart_6769529 : Nat := 118140960795 + 6769529 * 2 ^ 59
def prefixEnd_6769529 : Nat := 4983230072969 + 3 ^ 40 * 6769529 * 2
def baseEnd_6769529 : Nat := 1158674060516783306785003

theorem tailTrace_6769529 : CollatzResearch.WordTrace tailWord_6769529 prefixEnd_6769529 1158674060516783306785003 := by
  unfold tailWord_6769529
  simp only [CollatzResearch.WordTrace]
  refine ⟨246905006692160051353023641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164603337794773367568682427 246905006692160051353023641)
  ·
    refine ⟨185178755019120038514767731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246905006692160051353023641 185178755019120038514767731)
    ·
      refine ⟨277768132528680057772151597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185178755019120038514767731 277768132528680057772151597)
      ·
        refine ⟨104163049698255021664556849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277768132528680057772151597 104163049698255021664556849)
        ·
          refine ⟨78122287273691266248417637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104163049698255021664556849 78122287273691266248417637)
          ·
            refine ⟨14647928863817112421578307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78122287273691266248417637 14647928863817112421578307)
            ·
              refine ⟨21971893295725668632367461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14647928863817112421578307 21971893295725668632367461)
              ·
                refine ⟨4119729992948562868568899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21971893295725668632367461 4119729992948562868568899)
                ·
                  refine ⟨6179594989422844302853349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119729992948562868568899 6179594989422844302853349)
                  ·
                    refine ⟨1158674060516783306785003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179594989422844302853349 1158674060516783306785003)
                    ·
                      rfl

theorem cell23_6769529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 4].length) (baseStart_6769529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769529 prefixEnd_6769529 := by exact prefixLift 6769529
  have htrace : WordTrace (prefixWord ++ tailWord_6769529) baseStart_6769529 baseEnd_6769529 := by
    simpa [prefixWord, tailWord_6769529, baseEnd_6769529] using wordTrace_append hprefix tailTrace_6769529
  have hstable : (prefixWord ++ tailWord_6769529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769529).length < 2 ^ (prefixWord ++ tailWord_6769529).sum := by decide
  have hdescent : baseEnd_6769529 < baseStart_6769529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769572 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_6769572 : Nat := 118140960795 + 6769572 * 2 ^ 59
def prefixEnd_6769572 : Nat := 4983230072969 + 3 ^ 40 * 6769572 * 2
def baseEnd_6769572 : Nat := 1158681420406164417372437

theorem tailTrace_6769572 : CollatzResearch.WordTrace tailWord_6769572 prefixEnd_6769572 1158681420406164417372437 := by
  unfold tailWord_6769572
  simp only [CollatzResearch.WordTrace]
  refine ⟨123453287515502134848419485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164604383354002846464559313 123453287515502134848419485)
  ·
    refine ⟨46294982818313300568157307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123453287515502134848419485 46294982818313300568157307)
    ·
      refine ⟨69442474227469950852235961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46294982818313300568157307 69442474227469950852235961)
      ·
        refine ⟨52081855670602463139176971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69442474227469950852235961 52081855670602463139176971)
        ·
          refine ⟨78122783505903694708765457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52081855670602463139176971 78122783505903694708765457)
          ·
            refine ⟨58592087629427771031574093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78122783505903694708765457 58592087629427771031574093)
            ·
              refine ⟨21972032861035414136840285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58592087629427771031574093 21972032861035414136840285)
              ·
                refine ⟨8239512322888280301315107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21972032861035414136840285 8239512322888280301315107)
                ·
                  refine ⟨12359268484332420451972661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8239512322888280301315107 12359268484332420451972661)
                  ·
                    refine ⟨1158681420406164417372437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12359268484332420451972661 1158681420406164417372437)
                    ·
                      rfl

theorem cell23_6769572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_6769572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769572 prefixEnd_6769572 := by exact prefixLift 6769572
  have htrace : WordTrace (prefixWord ++ tailWord_6769572) baseStart_6769572 baseEnd_6769572 := by
    simpa [prefixWord, tailWord_6769572, baseEnd_6769572] using wordTrace_append hprefix tailTrace_6769572
  have hstable : (prefixWord ++ tailWord_6769572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769572).length < 2 ^ (prefixWord ++ tailWord_6769572).sum := by decide
  have hdescent : baseEnd_6769572 < baseStart_6769572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769615 : List Nat := [1, 1, 2, 1, 1, 7, 1, 9]
def baseStart_6769615 : Nat := 118140960795 + 6769615 * 2 ^ 59
def prefixEnd_6769615 : Nat := 4983230072969 + 3 ^ 40 * 6769615 * 2
def baseEnd_6769615 : Nat := 128743197810616169773319

theorem tailTrace_6769615 : CollatzResearch.WordTrace tailWord_6769615 prefixEnd_6769615 128743197810616169773319 := by
  unfold tailWord_6769615
  simp only [CollatzResearch.WordTrace]
  refine ⟨246908143369848488040654299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164605428913232325360436199 246908143369848488040654299)
  ·
    refine ⟨370362215054772732060981449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246908143369848488040654299 370362215054772732060981449)
    ·
      refine ⟨277771661291079549045736087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370362215054772732060981449 277771661291079549045736087)
      ·
        refine ⟨416657491936619323568604131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277771661291079549045736087 416657491936619323568604131)
        ·
          refine ⟨624986237904928985352906197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416657491936619323568604131 624986237904928985352906197)
          ·
            refine ⟨14648114950896773094208739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 624986237904928985352906197 14648114950896773094208739)
            ·
              refine ⟨21972172426345159641313109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14648114950896773094208739 21972172426345159641313109)
              ·
                refine ⟨128743197810616169773319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21972172426345159641313109 128743197810616169773319)
                ·
                  rfl

theorem cell23_6769615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 9].length) (baseStart_6769615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769615 prefixEnd_6769615 := by exact prefixLift 6769615
  have htrace : WordTrace (prefixWord ++ tailWord_6769615) baseStart_6769615 baseEnd_6769615 := by
    simpa [prefixWord, tailWord_6769615, baseEnd_6769615] using wordTrace_append hprefix tailTrace_6769615
  have hstable : (prefixWord ++ tailWord_6769615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769615).length < 2 ^ (prefixWord ++ tailWord_6769615).sum := by decide
  have hdescent : baseEnd_6769615 < baseStart_6769615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769629 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_6769629 : Nat := 118140960795 + 6769629 * 2 ^ 59
def prefixEnd_6769629 : Nat := 4983230072969 + 3 ^ 40 * 6769629 * 2
def baseEnd_6769629 : Nat := 3476073529615799529104549

theorem tailTrace_6769629 : CollatzResearch.WordTrace tailWord_6769629 prefixEnd_6769629 3476073529615799529104549 := by
  unfold tailWord_6769629
  simp only [CollatzResearch.WordTrace]
  refine ⟨246908653991797768431663941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164605769327865178954442627 246908653991797768431663941)
  ·
    refine ⟨46295372623462081580936989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246908653991797768431663941 46295372623462081580936989)
    ·
      refine ⟨17360764733798280592851371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46295372623462081580936989 17360764733798280592851371)
      ·
        refine ⟨26041147100697420889277057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17360764733798280592851371 26041147100697420889277057)
        ·
          refine ⟨19530860325523065666957793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26041147100697420889277057 19530860325523065666957793)
          ·
            refine ⟨14648145244142299250218345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19530860325523065666957793 14648145244142299250218345)
            ·
              refine ⟨10986108933106724437663759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14648145244142299250218345 10986108933106724437663759)
              ·
                refine ⟨16479163399660086656495639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986108933106724437663759 16479163399660086656495639)
                ·
                  refine ⟨24718745099490129984743459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16479163399660086656495639 24718745099490129984743459)
                  ·
                    refine ⟨37078117649235194977115189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24718745099490129984743459 37078117649235194977115189)
                    ·
                      refine ⟨3476073529615799529104549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37078117649235194977115189 3476073529615799529104549)
                      ·
                        rfl

theorem cell23_6769629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_6769629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769629 prefixEnd_6769629 := by exact prefixLift 6769629
  have htrace : WordTrace (prefixWord ++ tailWord_6769629) baseStart_6769629 baseEnd_6769629 := by
    simpa [prefixWord, tailWord_6769629, baseEnd_6769629] using wordTrace_append hprefix tailTrace_6769629
  have hstable : (prefixWord ++ tailWord_6769629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769629).length < 2 ^ (prefixWord ++ tailWord_6769629).sum := by decide
  have hdescent : baseEnd_6769629 < baseStart_6769629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769653 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6769653 : Nat := 118140960795 + 6769653 * 2 ^ 59
def prefixEnd_6769653 : Nat := 4983230072969 + 3 ^ 40 * 6769653 * 2
def baseEnd_6769653 : Nat := 1158695284383835811734813

theorem tailTrace_6769653 : CollatzResearch.WordTrace tailWord_6769653 prefixEnd_6769653 1158695284383835811734813 := by
  unfold tailWord_6769653
  simp only [CollatzResearch.WordTrace]
  refine ⟨246909529343710820530537613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164606352895807213687025075 246909529343710820530537613)
  ·
    refine ⟨92591073503891557698951605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246909529343710820530537613 92591073503891557698951605)
    ·
      refine ⟨8680413140989833534276713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92591073503891557698951605 8680413140989833534276713)
      ·
        refine ⟨6510309855742375150707535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8680413140989833534276713 6510309855742375150707535)
        ·
          refine ⟨9765464783613562726061303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510309855742375150707535 9765464783613562726061303)
          ·
            refine ⟨14648197175420344089091955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765464783613562726061303 14648197175420344089091955)
            ·
              refine ⟨21972295763130516133637933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14648197175420344089091955 21972295763130516133637933)
              ·
                refine ⟨8239610911173943550114225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21972295763130516133637933 8239610911173943550114225)
                ·
                  refine ⟨6179708183380457662585669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239610911173943550114225 6179708183380457662585669)
                  ·
                    refine ⟨1158695284383835811734813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179708183380457662585669 1158695284383835811734813)
                    ·
                      rfl

theorem cell23_6769653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6769653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769653 prefixEnd_6769653 := by exact prefixLift 6769653
  have htrace : WordTrace (prefixWord ++ tailWord_6769653) baseStart_6769653 baseEnd_6769653 := by
    simpa [prefixWord, tailWord_6769653, baseEnd_6769653] using wordTrace_append hprefix tailTrace_6769653
  have hstable : (prefixWord ++ tailWord_6769653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769653).length < 2 ^ (prefixWord ++ tailWord_6769653).sum := by decide
  have hdescent : baseEnd_6769653 < baseStart_6769653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769669 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_6769669 : Nat := 118140960795 + 6769669 * 2 ^ 59
def prefixEnd_6769669 : Nat := 4983230072969 + 3 ^ 40 * 6769669 * 2
def baseEnd_6769669 : Nat := 3476094068841979372604365

theorem tailTrace_6769669 : CollatzResearch.WordTrace tailWord_6769669 prefixEnd_6769669 3476094068841979372604365 := by
  unfold tailWord_6769669
  simp only [CollatzResearch.WordTrace]
  refine ⟨246910112911652855263120061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164606741941101903508746707 246910112911652855263120061)
  ·
    refine ⟨92591292341869820723670023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246910112911652855263120061 92591292341869820723670023)
    ·
      refine ⟨138886938512804731085505035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92591292341869820723670023 138886938512804731085505035)
      ·
        refine ⟨208330407769207096628257553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138886938512804731085505035 208330407769207096628257553)
        ·
          refine ⟨156247805826905322471193165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208330407769207096628257553 156247805826905322471193165)
          ·
            refine ⟨58592927185089495926697437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156247805826905322471193165 58592927185089495926697437)
            ·
              refine ⟨21972347694408560972511539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58592927185089495926697437 21972347694408560972511539)
              ·
                refine ⟨32958521541612841458767309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21972347694408560972511539 32958521541612841458767309)
                ·
                  refine ⟨12359445578104815547037741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32958521541612841458767309 12359445578104815547037741)
                  ·
                    refine ⟨4634792091789305830139153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12359445578104815547037741 4634792091789305830139153)
                    ·
                      refine ⟨3476094068841979372604365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4634792091789305830139153 3476094068841979372604365)
                      ·
                        rfl

theorem cell23_6769669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_6769669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769669 prefixEnd_6769669 := by exact prefixLift 6769669
  have htrace : WordTrace (prefixWord ++ tailWord_6769669) baseStart_6769669 baseEnd_6769669 := by
    simpa [prefixWord, tailWord_6769669, baseEnd_6769669] using wordTrace_append hprefix tailTrace_6769669
  have hstable : (prefixWord ++ tailWord_6769669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769669).length < 2 ^ (prefixWord ++ tailWord_6769669).sum := by decide
  have hdescent : baseEnd_6769669 < baseStart_6769669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769693 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_6769693 : Nat := 118140960795 + 6769693 * 2 ^ 59
def prefixEnd_6769693 : Nat := 4983230072969 + 3 ^ 40 * 6769693 * 2
def baseEnd_6769693 : Nat := 3476106392377687278704255

theorem tailTrace_6769693 : CollatzResearch.WordTrace tailWord_6769693 prefixEnd_6769693 3476106392377687278704255 := by
  unfold tailWord_6769693
  simp only [CollatzResearch.WordTrace]
  refine ⟨246910988263565907361993733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164607325509043938241329155 246910988263565907361993733)
  ·
    refine ⟨46295810299418607630373825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246910988263565907361993733 46295810299418607630373825)
    ·
      refine ⟨34721857724563955722780369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46295810299418607630373825 34721857724563955722780369)
      ·
        refine ⟨26041393293422966792085277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34721857724563955722780369 26041393293422966792085277)
        ·
          refine ⟨9765522485033612547031979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26041393293422966792085277 9765522485033612547031979)
          ·
            refine ⟨14648283727550418820547969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765522485033612547031979 14648283727550418820547969)
            ·
              refine ⟨10986212795662814115410977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14648283727550418820547969 10986212795662814115410977)
              ·
                refine ⟨8239659596747110586558233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10986212795662814115410977 8239659596747110586558233)
                ·
                  refine ⟨6179744697560332939918675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239659596747110586558233 6179744697560332939918675)
                  ·
                    refine ⟨9269617046340499409878013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6179744697560332939918675 9269617046340499409878013)
                    ·
                      refine ⟨3476106392377687278704255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9269617046340499409878013 3476106392377687278704255)
                      ·
                        rfl

theorem cell23_6769693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_6769693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769693 prefixEnd_6769693 := by exact prefixLift 6769693
  have htrace : WordTrace (prefixWord ++ tailWord_6769693) baseStart_6769693 baseEnd_6769693 := by
    simpa [prefixWord, tailWord_6769693, baseEnd_6769693] using wordTrace_append hprefix tailTrace_6769693
  have hstable : (prefixWord ++ tailWord_6769693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769693).length < 2 ^ (prefixWord ++ tailWord_6769693).sum := by decide
  have hdescent : baseEnd_6769693 < baseStart_6769693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769712 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_6769712 : Nat := 118140960795 + 6769712 * 2 ^ 59
def prefixEnd_6769712 : Nat := 4983230072969 + 3 ^ 40 * 6769712 * 2
def baseEnd_6769712 : Nat := 3476116148510122704366667

theorem tailTrace_6769712 : CollatzResearch.WordTrace tailWord_6769712 prefixEnd_6769712 3476116148510122704366667 := by
  unfold tailWord_6769712
  simp only [CollatzResearch.WordTrace]
  refine ⟨123455840625248536803467695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164607787500331382404623593 123455840625248536803467695)
  ·
    refine ⟨185183760937872805205201543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123455840625248536803467695 185183760937872805205201543)
    ·
      refine ⟨277775641406809207807802315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185183760937872805205201543 277775641406809207807802315)
      ·
        refine ⟨416663462110213811711703473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277775641406809207807802315 416663462110213811711703473)
        ·
          refine ⟨312497596582660358783777605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416663462110213811711703473 312497596582660358783777605)
          ·
            refine ⟨58593299359248817271958301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312497596582660358783777605 58593299359248817271958301)
            ·
              refine ⟨21972487259718306476984363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58593299359248817271958301 21972487259718306476984363)
              ·
                refine ⟨32958730889577459715476545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21972487259718306476984363 32958730889577459715476545)
                ·
                  refine ⟨24719048167183094786607409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32958730889577459715476545 24719048167183094786607409)
                  ·
                    refine ⟨18539286125387321089955557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24719048167183094786607409 18539286125387321089955557)
                    ·
                      refine ⟨3476116148510122704366667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18539286125387321089955557 3476116148510122704366667)
                      ·
                        rfl

theorem cell23_6769712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_6769712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769712 prefixEnd_6769712 := by exact prefixLift 6769712
  have htrace : WordTrace (prefixWord ++ tailWord_6769712) baseStart_6769712 baseEnd_6769712 := by
    simpa [prefixWord, tailWord_6769712, baseEnd_6769712] using wordTrace_append hprefix tailTrace_6769712
  have hstable : (prefixWord ++ tailWord_6769712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769712).length < 2 ^ (prefixWord ++ tailWord_6769712).sum := by decide
  have hdescent : baseEnd_6769712 < baseStart_6769712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769752 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_6769752 : Nat := 118140960795 + 6769752 * 2 ^ 59
def prefixEnd_6769752 : Nat := 4983230072969 + 3 ^ 40 * 6769752 * 2
def baseEnd_6769752 : Nat := 1158712229245434182622161

theorem tailTrace_6769752 : CollatzResearch.WordTrace tailWord_6769752 prefixEnd_6769752 1158712229245434182622161 := by
  unfold tailWord_6769752
  simp only [CollatzResearch.WordTrace]
  refine ⟨123456570085176080219195755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164608760113568106958927673 123456570085176080219195755)
  ·
    refine ⟨185184855127764120328793633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123456570085176080219195755 185184855127764120328793633)
    ·
      refine ⟨138888641345823090246595225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185184855127764120328793633 138888641345823090246595225)
      ·
        refine ⟨104166481009367317684946419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138888641345823090246595225 104166481009367317684946419)
        ·
          refine ⟨156249721514050976527419629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104166481009367317684946419 156249721514050976527419629)
          ·
            refine ⟨58593645567769116197782361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156249721514050976527419629 58593645567769116197782361)
            ·
              refine ⟨43945234175826837148336771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58593645567769116197782361 43945234175826837148336771)
              ·
                refine ⟨65917851263740255722505157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43945234175826837148336771 65917851263740255722505157)
                ·
                  refine ⟨12359597111951297947969717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65917851263740255722505157 12359597111951297947969717)
                  ·
                    refine ⟨1158712229245434182622161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12359597111951297947969717 1158712229245434182622161)
                    ·
                      rfl

theorem cell23_6769752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_6769752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769752 prefixEnd_6769752 := by exact prefixLift 6769752
  have htrace : WordTrace (prefixWord ++ tailWord_6769752) baseStart_6769752 baseEnd_6769752 := by
    simpa [prefixWord, tailWord_6769752, baseEnd_6769752] using wordTrace_append hprefix tailTrace_6769752
  have hstable : (prefixWord ++ tailWord_6769752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769752).length < 2 ^ (prefixWord ++ tailWord_6769752).sum := by decide
  have hdescent : baseEnd_6769752 < baseStart_6769752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769772 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_6769772 : Nat := 118140960795 + 6769772 * 2 ^ 59
def prefixEnd_6769772 : Nat := 4983230072969 + 3 ^ 40 * 6769772 * 2
def baseEnd_6769772 : Nat := 3476146957349392469616391

theorem tailTrace_6769772 : CollatzResearch.WordTrace tailWord_6769772 prefixEnd_6769772 3476146957349392469616391 := by
  unfold tailWord_6769772
  simp only [CollatzResearch.WordTrace]
  refine ⟨123456934815139851927059785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164609246420186469236079713 123456934815139851927059785)
  ·
    refine ⟨92592701111354888945294839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123456934815139851927059785 92592701111354888945294839)
    ·
      refine ⟨138889051667032333417942259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92592701111354888945294839 138889051667032333417942259)
      ·
        refine ⟨208333577500548500126913389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138889051667032333417942259 208333577500548500126913389)
        ·
          refine ⟨78125091562705687547592521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208333577500548500126913389 78125091562705687547592521)
          ·
            refine ⟨58593818672029265660694391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78125091562705687547592521 58593818672029265660694391)
            ·
              refine ⟨87890728008043898491041587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58593818672029265660694391 87890728008043898491041587)
              ·
                refine ⟨131836092012065847736562381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87890728008043898491041587 131836092012065847736562381)
                ·
                  refine ⟨49438534504524692901210893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131836092012065847736562381 49438534504524692901210893)
                  ·
                    refine ⟨18539450439196759837954085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49438534504524692901210893 18539450439196759837954085)
                    ·
                      refine ⟨3476146957349392469616391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18539450439196759837954085 3476146957349392469616391)
                      ·
                        rfl

theorem cell23_6769772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_6769772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769772 prefixEnd_6769772 := by exact prefixLift 6769772
  have htrace : WordTrace (prefixWord ++ tailWord_6769772) baseStart_6769772 baseEnd_6769772 := by
    simpa [prefixWord, tailWord_6769772, baseEnd_6769772] using wordTrace_append hprefix tailTrace_6769772
  have hstable : (prefixWord ++ tailWord_6769772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769772).length < 2 ^ (prefixWord ++ tailWord_6769772).sum := by decide
  have hdescent : baseEnd_6769772 < baseStart_6769772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769789 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_6769789 : Nat := 118140960795 + 6769789 * 2 ^ 59
def prefixEnd_6769789 : Nat := 4983230072969 + 3 ^ 40 * 6769789 * 2
def baseEnd_6769789 : Nat := 3476155686520518903103813

theorem tailTrace_6769789 : CollatzResearch.WordTrace tailWord_6769789 prefixEnd_6769789 3476155686520518903103813 := by
  unfold tailWord_6769789
  simp only [CollatzResearch.WordTrace]
  refine ⟨246914489671218115757488421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164609659780812077171658947 246914489671218115757488421)
  ·
    refine ⟨46296466813353396704529079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246914489671218115757488421 46296466813353396704529079)
    ·
      refine ⟨69444700220030095056793619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46296466813353396704529079 69444700220030095056793619)
      ·
        refine ⟨104167050330045142585190429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69444700220030095056793619 104167050330045142585190429)
        ·
          refine ⟨39062643873766928469446411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104167050330045142585190429 39062643873766928469446411)
          ·
            refine ⟨58593965810650392704169617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39062643873766928469446411 58593965810650392704169617)
            ·
              refine ⟨43945474357987794528127213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58593965810650392704169617 43945474357987794528127213)
              ·
                refine ⟨16479552884245422948047705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43945474357987794528127213 16479552884245422948047705)
                ·
                  refine ⟨12359664663184067211035779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16479552884245422948047705 12359664663184067211035779)
                  ·
                    refine ⟨18539496994776100816553669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12359664663184067211035779 18539496994776100816553669)
                    ·
                      refine ⟨3476155686520518903103813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18539496994776100816553669 3476155686520518903103813)
                      ·
                        rfl

theorem cell23_6769789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_6769789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769789 prefixEnd_6769789 := by exact prefixLift 6769789
  have htrace : WordTrace (prefixWord ++ tailWord_6769789) baseStart_6769789 baseEnd_6769789 := by
    simpa [prefixWord, tailWord_6769789, baseEnd_6769789] using wordTrace_append hprefix tailTrace_6769789
  have hstable : (prefixWord ++ tailWord_6769789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769789).length < 2 ^ (prefixWord ++ tailWord_6769789).sum := by decide
  have hdescent : baseEnd_6769789 < baseStart_6769789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769806 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6769806 : Nat := 118140960795 + 6769806 * 2 ^ 59
def prefixEnd_6769806 : Nat := 4983230072969 + 3 ^ 40 * 6769806 * 2
def baseEnd_6769806 : Nat := 3476164415691645336591235

theorem tailTrace_6769806 : CollatzResearch.WordTrace tailWord_6769806 prefixEnd_6769806 3476164415691645336591235 := by
  unfold tailWord_6769806
  simp only [CollatzResearch.WordTrace]
  refine ⟨30864388714019565957607159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164610073141437685107238181 30864388714019565957607159)
  ·
    refine ⟨46296583071029348936410739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30864388714019565957607159 46296583071029348936410739)
    ·
      refine ⟨69444874606544023404616109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46296583071029348936410739 69444874606544023404616109)
      ·
        refine ⟨26041827977454008776731041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69444874606544023404616109 26041827977454008776731041)
        ·
          refine ⟨19531370983090506582548281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26041827977454008776731041 19531370983090506582548281)
          ·
            refine ⟨14648528237317879936911211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19531370983090506582548281 14648528237317879936911211)
            ·
              refine ⟨21972792355976819905366817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14648528237317879936911211 21972792355976819905366817)
              ·
                refine ⟨16479594266982614929025113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21972792355976819905366817 16479594266982614929025113)
                ·
                  refine ⟨12359695700236961196768835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16479594266982614929025113 12359695700236961196768835)
                  ·
                    refine ⟨18539543550355441795153253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12359695700236961196768835 18539543550355441795153253)
                    ·
                      refine ⟨3476164415691645336591235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18539543550355441795153253 3476164415691645336591235)
                      ·
                        rfl

theorem cell23_6769806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6769806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769806 prefixEnd_6769806 := by exact prefixLift 6769806
  have htrace : WordTrace (prefixWord ++ tailWord_6769806) baseStart_6769806 baseEnd_6769806 := by
    simpa [prefixWord, tailWord_6769806, baseEnd_6769806] using wordTrace_append hprefix tailTrace_6769806
  have hstable : (prefixWord ++ tailWord_6769806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769806).length < 2 ^ (prefixWord ++ tailWord_6769806).sum := by decide
  have hdescent : baseEnd_6769806 < baseStart_6769806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769816 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_6769816 : Nat := 118140960795 + 6769816 * 2 ^ 59
def prefixEnd_6769816 : Nat := 4983230072969 + 3 ^ 40 * 6769816 * 2
def baseEnd_6769816 : Nat := 1158723183499396765822063

theorem tailTrace_6769816 : CollatzResearch.WordTrace tailWord_6769816 prefixEnd_6769816 1158723183499396765822063 := by
  unfold tailWord_6769816
  simp only [CollatzResearch.WordTrace]
  refine ⟨123457737221060149684360651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164610316294746866245814201 123457737221060149684360651)
  ·
    refine ⟨185186605831590224526540977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123457737221060149684360651 185186605831590224526540977)
    ·
      refine ⟨138889954373692668394905733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185186605831590224526540977 138889954373692668394905733)
      ·
        refine ⟨26041866445067375324044825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138889954373692668394905733 26041866445067375324044825)
        ·
          refine ⟨19531399833800531493033619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26041866445067375324044825 19531399833800531493033619)
          ·
            refine ⟨29297099750700797239550429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19531399833800531493033619 29297099750700797239550429)
            ·
              refine ⟨10986412406512798964831411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29297099750700797239550429 10986412406512798964831411)
              ·
                refine ⟨16479618609769198447247117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986412406512798964831411 16479618609769198447247117)
                ·
                  refine ⟨6179856978663449417717669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16479618609769198447247117 6179856978663449417717669)
                  ·
                    refine ⟨1158723183499396765822063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179856978663449417717669 1158723183499396765822063)
                    ·
                      rfl

theorem cell23_6769816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_6769816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769816 prefixEnd_6769816 := by exact prefixLift 6769816
  have htrace : WordTrace (prefixWord ++ tailWord_6769816) baseStart_6769816 baseEnd_6769816 := by
    simpa [prefixWord, tailWord_6769816, baseEnd_6769816] using wordTrace_append hprefix tailTrace_6769816
  have hstable : (prefixWord ++ tailWord_6769816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769816).length < 2 ^ (prefixWord ++ tailWord_6769816).sum := by decide
  have hdescent : baseEnd_6769816 < baseStart_6769816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769829 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 6]
def baseStart_6769829 : Nat := 118140960795 + 6769829 * 2 ^ 59
def prefixEnd_6769829 : Nat := 4983230072969 + 3 ^ 40 * 6769829 * 2
def baseEnd_6769829 : Nat := 386241802860744305178181

theorem tailTrace_6769829 : CollatzResearch.WordTrace tailWord_6769829 prefixEnd_6769829 386241802860744305178181 := by
  unfold tailWord_6769829
  simp only [CollatzResearch.WordTrace]
  refine ⟨246915948591073202588944541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164610632394048801725963027 246915948591073202588944541)
  ·
    refine ⟨92593480721652450970854203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246915948591073202588944541 92593480721652450970854203)
    ·
      refine ⟨138890221082478676456281305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92593480721652450970854203 138890221082478676456281305)
      ·
        refine ⟨104167665811859007342210979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138890221082478676456281305 104167665811859007342210979)
        ·
          refine ⟨156251498717788511013316469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104167665811859007342210979 156251498717788511013316469)
          ·
            refine ⟨14648578004792672907498419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156251498717788511013316469 14648578004792672907498419)
            ·
              refine ⟨21972867007189009361247629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14648578004792672907498419 21972867007189009361247629)
              ·
                refine ⟨8239825127695878510467861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21972867007189009361247629 8239825127695878510467861)
                ·
                  refine ⟨386241802860744305178181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8239825127695878510467861 386241802860744305178181)
                  ·
                    rfl

theorem cell23_6769829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_6769829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769829 prefixEnd_6769829 := by exact prefixLift 6769829
  have htrace : WordTrace (prefixWord ++ tailWord_6769829) baseStart_6769829 baseEnd_6769829 := by
    simpa [prefixWord, tailWord_6769829, baseEnd_6769829] using wordTrace_append hprefix tailTrace_6769829
  have hstable : (prefixWord ++ tailWord_6769829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769829).length < 2 ^ (prefixWord ++ tailWord_6769829).sum := by decide
  have hdescent : baseEnd_6769829 < baseStart_6769829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769879 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_6769879 : Nat := 118140960795 + 6769879 * 2 ^ 59
def prefixEnd_6769879 : Nat := 4983230072969 + 3 ^ 40 * 6769879 * 2
def baseEnd_6769879 : Nat := 3476201899779423550978399

theorem tailTrace_6769879 : CollatzResearch.WordTrace tailWord_6769879 prefixEnd_6769879 3476201899779423550978399 := by
  unfold tailWord_6769879
  simp only [CollatzResearch.WordTrace]
  refine ⟨246917772240892061128264691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164611848160594707418843127 246917772240892061128264691)
  ·
    refine ⟨370376658361338091692397037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246917772240892061128264691 370376658361338091692397037)
    ·
      refine ⟨138891246885501784384648889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370376658361338091692397037 138891246885501784384648889)
      ·
        refine ⟨104168435164126338288486667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138891246885501784384648889 104168435164126338288486667)
        ·
          refine ⟨156252652746189507432730001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104168435164126338288486667 156252652746189507432730001)
          ·
            refine ⟨117189489559642130574547501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156252652746189507432730001 117189489559642130574547501)
            ·
              refine ⟨43946058584865798965455313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117189489559642130574547501 43946058584865798965455313)
              ·
                refine ⟨32959543938649349224091485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43946058584865798965455313 32959543938649349224091485)
                ·
                  refine ⟨12359828976993505959034307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32959543938649349224091485 12359828976993505959034307)
                  ·
                    refine ⟨18539743465490258938551461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12359828976993505959034307 18539743465490258938551461)
                    ·
                      refine ⟨3476201899779423550978399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18539743465490258938551461 3476201899779423550978399)
                      ·
                        rfl

theorem cell23_6769879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_6769879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769879 prefixEnd_6769879 := by exact prefixLift 6769879
  have htrace : WordTrace (prefixWord ++ tailWord_6769879) baseStart_6769879 baseEnd_6769879 := by
    simpa [prefixWord, tailWord_6769879, baseEnd_6769879] using wordTrace_append hprefix tailTrace_6769879
  have hstable : (prefixWord ++ tailWord_6769879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769879).length < 2 ^ (prefixWord ++ tailWord_6769879).sum := by decide
  have hdescent : baseEnd_6769879 < baseStart_6769879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769889 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_6769889 : Nat := 118140960795 + 6769889 * 2 ^ 59
def prefixEnd_6769889 : Nat := 4983230072969 + 3 ^ 40 * 6769889 * 2
def baseEnd_6769889 : Nat := 1158735678195322837284451

theorem tailTrace_6769889 : CollatzResearch.WordTrace tailWord_6769889 prefixEnd_6769889 1158735678195322837284451 := by
  unfold tailWord_6769889
  simp only [CollatzResearch.WordTrace]
  refine ⟨246918136970855832836128721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164612091313903888557419147 246918136970855832836128721)
  ·
    refine ⟨185188602728141874627096541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246918136970855832836128721 185188602728141874627096541)
    ·
      refine ⟨69445726023053202985161203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185188602728141874627096541 69445726023053202985161203)
      ·
        refine ⟨104168589034579804477741805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69445726023053202985161203 104168589034579804477741805)
        ·
          refine ⟨39063220887967426679153177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104168589034579804477741805 39063220887967426679153177)
          ·
            refine ⟨29297415665975570009364883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39063220887967426679153177 29297415665975570009364883)
            ·
              refine ⟨43946123498963355014047325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29297415665975570009364883 43946123498963355014047325)
              ·
                refine ⟨16479796312111258130267747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43946123498963355014047325 16479796312111258130267747)
                ·
                  refine ⟨24719694468166887195401621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16479796312111258130267747 24719694468166887195401621)
                  ·
                    refine ⟨1158735678195322837284451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24719694468166887195401621 1158735678195322837284451)
                    ·
                      rfl

theorem cell23_6769889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_6769889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769889 prefixEnd_6769889 := by exact prefixLift 6769889
  have htrace : WordTrace (prefixWord ++ tailWord_6769889) baseStart_6769889 baseEnd_6769889 := by
    simpa [prefixWord, tailWord_6769889, baseEnd_6769889] using wordTrace_append hprefix tailTrace_6769889
  have hstable : (prefixWord ++ tailWord_6769889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769889).length < 2 ^ (prefixWord ++ tailWord_6769889).sum := by decide
  have hdescent : baseEnd_6769889 < baseStart_6769889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769896 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6769896 : Nat := 118140960795 + 6769896 * 2 ^ 59
def prefixEnd_6769896 : Nat := 4983230072969 + 3 ^ 40 * 6769896 * 2
def baseEnd_6769896 : Nat := 3476210628950549984465821

theorem tailTrace_6769896 : CollatzResearch.WordTrace tailWord_6769896 prefixEnd_6769896 3476210628950549984465821 := by
  unfold tailWord_6769896
  simp only [CollatzResearch.WordTrace]
  refine ⟨123459196140915236515816771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164612261521220315354422361 123459196140915236515816771)
  ·
    refine ⟨185188794211372854773725157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123459196140915236515816771 185188794211372854773725157)
    ·
      refine ⟨34722898914632410270073467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185188794211372854773725157 34722898914632410270073467)
      ·
        refine ⟨52084348371948615405110201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34722898914632410270073467 52084348371948615405110201)
        ·
          refine ⟨39063261278961461553832651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52084348371948615405110201 39063261278961461553832651)
          ·
            refine ⟨58594891918442192330748977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39063261278961461553832651 58594891918442192330748977)
            ·
              refine ⟨43946168938831644248061733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58594891918442192330748977 43946168938831644248061733)
              ·
                refine ⟨8239906676030933296511575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43946168938831644248061733 8239906676030933296511575)
                ·
                  refine ⟨12359860014046399944767363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8239906676030933296511575 12359860014046399944767363)
                  ·
                    refine ⟨18539790021069599917151045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12359860014046399944767363 18539790021069599917151045)
                    ·
                      refine ⟨3476210628950549984465821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18539790021069599917151045 3476210628950549984465821)
                      ·
                        rfl

theorem cell23_6769896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6769896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769896 prefixEnd_6769896 := by exact prefixLift 6769896
  have htrace : WordTrace (prefixWord ++ tailWord_6769896) baseStart_6769896 baseEnd_6769896 := by
    simpa [prefixWord, tailWord_6769896, baseEnd_6769896] using wordTrace_append hprefix tailTrace_6769896
  have hstable : (prefixWord ++ tailWord_6769896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769896).length < 2 ^ (prefixWord ++ tailWord_6769896).sum := by decide
  have hdescent : baseEnd_6769896 < baseStart_6769896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769923 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 2, 4]
def baseStart_6769923 : Nat := 118140960795 + 6769923 * 2 ^ 59
def prefixEnd_6769923 : Nat := 4983230072969 + 3 ^ 40 * 6769923 * 2
def baseEnd_6769923 : Nat := 1158741497642740459609399

theorem tailTrace_6769923 : CollatzResearch.WordTrace tailWord_6769923 prefixEnd_6769923 1158741497642740459609399 := by
  unfold tailWord_6769923
  simp only [CollatzResearch.WordTrace]
  refine ⟨246919377052732656642866423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164612918035155104428577615 246919377052732656642866423)
  ·
    refine ⟨370379065579098984964299635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246919377052732656642866423 370379065579098984964299635)
    ·
      refine ⟨555568598368648477446449453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370379065579098984964299635 555568598368648477446449453)
      ·
        refine ⟨208338224388243179042418545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555568598368648477446449453 208338224388243179042418545)
        ·
          refine ⟨156253668291182384281813909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208338224388243179042418545 156253668291182384281813909)
          ·
            refine ⟨7324390701149174263210027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156253668291182384281813909 7324390701149174263210027)
            ·
              refine ⟨10986586051723761394815041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324390701149174263210027 10986586051723761394815041)
              ·
                refine ⟨8239939538792821046111281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10986586051723761394815041 8239939538792821046111281)
                ·
                  refine ⟨6179954654094615784583461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239939538792821046111281 6179954654094615784583461)
                  ·
                    refine ⟨1158741497642740459609399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179954654094615784583461 1158741497642740459609399)
                    ·
                      rfl

theorem cell23_6769923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 4].length) (baseStart_6769923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769923 prefixEnd_6769923 := by exact prefixLift 6769923
  have htrace : WordTrace (prefixWord ++ tailWord_6769923) baseStart_6769923 baseEnd_6769923 := by
    simpa [prefixWord, tailWord_6769923, baseEnd_6769923] using wordTrace_append hprefix tailTrace_6769923
  have hstable : (prefixWord ++ tailWord_6769923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769923).length < 2 ^ (prefixWord ++ tailWord_6769923).sum := by decide
  have hdescent : baseEnd_6769923 < baseStart_6769923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769981 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6769981 : Nat := 118140960795 + 6769981 * 2 ^ 59
def prefixEnd_6769981 : Nat := 4983230072969 + 3 ^ 40 * 6769981 * 2
def baseEnd_6769981 : Nat := 3476254274806182151902931

theorem tailTrace_6769981 : CollatzResearch.WordTrace tailWord_6769981 prefixEnd_6769981 3476254274806182151902931 := by
  unfold tailWord_6769981
  simp only [CollatzResearch.WordTrace]
  refine ⟨246921492486522532548477797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164614328324348355032318531 246921492486522532548477797)
  ·
    refine ⟨46297779841222974852839587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246921492486522532548477797 46297779841222974852839587)
    ·
      refine ⟨69446669761834462279259381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46297779841222974852839587 69446669761834462279259381)
      ·
        refine ⟨6510625290171980838680567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69446669761834462279259381 6510625290171980838680567)
        ·
          refine ⟨9765937935257971258020851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510625290171980838680567 9765937935257971258020851)
          ·
            refine ⟨14648906902886956887031277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9765937935257971258020851 14648906902886956887031277)
            ·
              refine ⟨5493340088582608832636729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14648906902886956887031277 5493340088582608832636729)
              ·
                refine ⟨4120005066436956624477547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493340088582608832636729 4120005066436956624477547)
                ·
                  refine ⟨6180007599655434936716321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120005066436956624477547 6180007599655434936716321)
                  ·
                    refine ⟨4635005699741576202537241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6180007599655434936716321 4635005699741576202537241)
                    ·
                      refine ⟨3476254274806182151902931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635005699741576202537241 3476254274806182151902931)
                      ·
                        rfl

theorem cell23_6769981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6769981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769981 prefixEnd_6769981 := by exact prefixLift 6769981
  have htrace : WordTrace (prefixWord ++ tailWord_6769981) baseStart_6769981 baseEnd_6769981 := by
    simpa [prefixWord, tailWord_6769981, baseEnd_6769981] using wordTrace_append hprefix tailTrace_6769981
  have hstable : (prefixWord ++ tailWord_6769981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769981).length < 2 ^ (prefixWord ++ tailWord_6769981).sum := by decide
  have hdescent : baseEnd_6769981 < baseStart_6769981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6769999 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_6769999 : Nat := 118140960795 + 6769999 * 2 ^ 59
def prefixEnd_6769999 : Nat := 4983230072969 + 3 ^ 40 * 6769999 * 2
def baseEnd_6769999 : Nat := 3476263517457963081477847

theorem tailTrace_6769999 : CollatzResearch.WordTrace tailWord_6769999 prefixEnd_6769999 3476263517457963081477847 := by
  unfold tailWord_6769999
  simp only [CollatzResearch.WordTrace]
  refine ⟨246922149000457321622633051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164614766000304881081755367 246922149000457321622633051)
  ·
    refine ⟨370383223500685982433949577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246922149000457321622633051 370383223500685982433949577)
    ·
      refine ⟨277787417625514486825462183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370383223500685982433949577 277787417625514486825462183)
      ·
        refine ⟨416681126438271730238193275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277787417625514486825462183 416681126438271730238193275)
        ·
          refine ⟨625021689657407595357289913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416681126438271730238193275 625021689657407595357289913)
          ·
            refine ⟨468766267243055696517967435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625021689657407595357289913 468766267243055696517967435)
            ·
              refine ⟨703149400864583544776951153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468766267243055696517967435 703149400864583544776951153)
              ·
                refine ⟨527362050648437658582713365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703149400864583544776951153 527362050648437658582713365)
                ·
                  refine ⟨24720096124145515246064689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 527362050648437658582713365 24720096124145515246064689)
                  ·
                    refine ⟨18540072093109136434548517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24720096124145515246064689 18540072093109136434548517)
                    ·
                      refine ⟨3476263517457963081477847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18540072093109136434548517 3476263517457963081477847)
                      ·
                        rfl

theorem cell23_6769999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_6769999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6769999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6769999 prefixEnd_6769999 := by exact prefixLift 6769999
  have htrace : WordTrace (prefixWord ++ tailWord_6769999) baseStart_6769999 baseEnd_6769999 := by
    simpa [prefixWord, tailWord_6769999, baseEnd_6769999] using wordTrace_append hprefix tailTrace_6769999
  have hstable : (prefixWord ++ tailWord_6769999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6769999).length < 2 ^ (prefixWord ++ tailWord_6769999).sum := by decide
  have hdescent : baseEnd_6769999 < baseStart_6769999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6769999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770009 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 7]
def baseStart_6770009 : Nat := 118140960795 + 6770009 * 2 ^ 59
def prefixEnd_6770009 : Nat := 4983230072969 + 3 ^ 40 * 6770009 * 2
def baseEnd_6770009 : Nat := 386252072473834226928089

theorem tailTrace_6770009 : CollatzResearch.WordTrace tailWord_6770009 prefixEnd_6770009 386252072473834226928089 := by
  unfold tailWord_6770009
  simp only [CollatzResearch.WordTrace]
  refine ⟨246922513730421093330497081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164615009153614062220331387 246922513730421093330497081)
  ·
    refine ⟨185191885297815819997872811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246922513730421093330497081 185191885297815819997872811)
    ·
      refine ⟨277787827946723729996809217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185191885297815819997872811 277787827946723729996809217)
      ·
        refine ⟨208340870960042797497606913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277787827946723729996809217 208340870960042797497606913)
        ·
          refine ⟨156255653220032098123205185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208340870960042797497606913 156255653220032098123205185)
          ·
            refine ⟨117191739915024073592403889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156255653220032098123205185 117191739915024073592403889)
            ·
              refine ⟨87893804936268055194302917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117191739915024073592403889 87893804936268055194302917)
              ·
                refine ⟨16480088425550260348931797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87893804936268055194302917 16480088425550260348931797)
                ·
                  refine ⟨386252072473834226928089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16480088425550260348931797 386252072473834226928089)
                  ·
                    rfl

theorem cell23_6770009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_6770009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770009 prefixEnd_6770009 := by exact prefixLift 6770009
  have htrace : WordTrace (prefixWord ++ tailWord_6770009) baseStart_6770009 baseEnd_6770009 := by
    simpa [prefixWord, tailWord_6770009, baseEnd_6770009] using wordTrace_append hprefix tailTrace_6770009
  have hstable : (prefixWord ++ tailWord_6770009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770009).length < 2 ^ (prefixWord ++ tailWord_6770009).sum := by decide
  have hdescent : baseEnd_6770009 < baseStart_6770009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770050 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6770050 : Nat := 118140960795 + 6770050 * 2 ^ 59
def prefixEnd_6770050 : Nat := 4983230072969 + 3 ^ 40 * 6770050 * 2
def baseEnd_6770050 : Nat := 3476289704971342381940113

theorem tailTrace_6770050 : CollatzResearch.WordTrace tailWord_6770050 prefixEnd_6770050 3476289704971342381940113 := by
  unfold tailWord_6770050
  simp only [CollatzResearch.WordTrace]
  refine ⟨61731002280818139333184901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164616006082181704888493069 61731002280818139333184901)
  ·
    refine ⟨11574562927653401124972169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61731002280818139333184901 11574562927653401124972169)
    ·
      refine ⟨8680922195740050843729127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11574562927653401124972169 8680922195740050843729127)
      ·
        refine ⟨13021383293610076265593691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8680922195740050843729127 13021383293610076265593691)
        ·
          refine ⟨19532074940415114398390537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13021383293610076265593691 19532074940415114398390537)
          ·
            refine ⟨14649056205311335798792903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19532074940415114398390537 14649056205311335798792903)
            ·
              refine ⟨21973584307967003698189355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14649056205311335798792903 21973584307967003698189355)
              ·
                refine ⟨32960376461950505547284033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21973584307967003698189355 32960376461950505547284033)
                ·
                  refine ⟨24720282346462879160463025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32960376461950505547284033 24720282346462879160463025)
                  ·
                    refine ⟨18540211759847159370347269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24720282346462879160463025 18540211759847159370347269)
                    ·
                      refine ⟨3476289704971342381940113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18540211759847159370347269 3476289704971342381940113)
                      ·
                        rfl

theorem cell23_6770050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6770050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770050 prefixEnd_6770050 := by exact prefixLift 6770050
  have htrace : WordTrace (prefixWord ++ tailWord_6770050) baseStart_6770050 baseEnd_6770050 := by
    simpa [prefixWord, tailWord_6770050, baseEnd_6770050] using wordTrace_append hprefix tailTrace_6770050
  have hstable : (prefixWord ++ tailWord_6770050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770050).length < 2 ^ (prefixWord ++ tailWord_6770050).sum := by decide
  have hdescent : baseEnd_6770050 < baseStart_6770050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770073 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_6770073 : Nat := 118140960795 + 6770073 * 2 ^ 59
def prefixEnd_6770073 : Nat := 4983230072969 + 3 ^ 40 * 6770073 * 2
def baseEnd_6770073 : Nat := 1158767171675465263984169

theorem tailTrace_6770073 : CollatzResearch.WordTrace tailWord_6770073 prefixEnd_6770073 1158767171675465263984169 := by
  unfold tailWord_6770073
  simp only [CollatzResearch.WordTrace]
  refine ⟨246924848002189232260826873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164616565334792821507217915 246924848002189232260826873)
  ·
    refine ⟨185193636001641924195620155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246924848002189232260826873 185193636001641924195620155)
    ·
      refine ⟨277790454002462886293430233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185193636001641924195620155 277790454002462886293430233)
      ·
        refine ⟨208342840501847164720072675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277790454002462886293430233 208342840501847164720072675)
        ·
          refine ⟨312514260752770747080109013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208342840501847164720072675 312514260752770747080109013)
          ·
            refine ⟨7324552986393064384690055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312514260752770747080109013 7324552986393064384690055)
            ·
              refine ⟨10986829479589596577035083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324552986393064384690055 10986829479589596577035083)
              ·
                refine ⟨16480244219384394865552625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986829479589596577035083 16480244219384394865552625)
                ·
                  refine ⟨12360183164538296149164469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16480244219384394865552625 12360183164538296149164469)
                  ·
                    refine ⟨1158767171675465263984169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12360183164538296149164469 1158767171675465263984169)
                    ·
                      rfl

theorem cell23_6770073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_6770073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770073 prefixEnd_6770073 := by exact prefixLift 6770073
  have htrace : WordTrace (prefixWord ++ tailWord_6770073) baseStart_6770073 baseEnd_6770073 := by
    simpa [prefixWord, tailWord_6770073, baseEnd_6770073] using wordTrace_append hprefix tailTrace_6770073
  have hstable : (prefixWord ++ tailWord_6770073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770073).length < 2 ^ (prefixWord ++ tailWord_6770073).sum := by decide
  have hdescent : baseEnd_6770073 < baseStart_6770073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770103 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 3, 4]
def baseStart_6770103 : Nat := 118140960795 + 6770103 * 2 ^ 59
def prefixEnd_6770103 : Nat := 4983230072969 + 3 ^ 40 * 6770103 * 2
def baseEnd_6770103 : Nat := 1158772306482010224859123

theorem tailTrace_6770103 : CollatzResearch.WordTrace tailWord_6770103 prefixEnd_6770103 1158772306482010224859123 := by
  unfold tailWord_6770103
  simp only [CollatzResearch.WordTrace]
  refine ⟨246925942192080547384418963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164617294794720364922945975 246925942192080547384418963)
  ·
    refine ⟨370388913288120821076628445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246925942192080547384418963 370388913288120821076628445)
    ·
      refine ⟨138895842483045307903735667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370388913288120821076628445 138895842483045307903735667)
      ·
        refine ⟨208343763724567961855603501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138895842483045307903735667 208343763724567961855603501)
        ·
          refine ⟨78128911396712985695851313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208343763724567961855603501 78128911396712985695851313)
          ·
            refine ⟨58596683547534739271888485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78128911396712985695851313 58596683547534739271888485)
            ·
              refine ⟨10986878165162763613479091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58596683547534739271888485 10986878165162763613479091)
              ·
                refine ⟨16480317247744145420218637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986878165162763613479091 16480317247744145420218637)
                ·
                  refine ⟨6180118967904054532581989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16480317247744145420218637 6180118967904054532581989)
                  ·
                    refine ⟨1158772306482010224859123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180118967904054532581989 1158772306482010224859123)
                    ·
                      rfl

theorem cell23_6770103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_6770103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770103 prefixEnd_6770103 := by exact prefixLift 6770103
  have htrace : WordTrace (prefixWord ++ tailWord_6770103) baseStart_6770103 baseEnd_6770103 := by
    simpa [prefixWord, tailWord_6770103, baseEnd_6770103] using wordTrace_append hprefix tailTrace_6770103
  have hstable : (prefixWord ++ tailWord_6770103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770103).length < 2 ^ (prefixWord ++ tailWord_6770103).sum := by decide
  have hdescent : baseEnd_6770103 < baseStart_6770103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770137 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 1, 4]
def baseStart_6770137 : Nat := 118140960795 + 6770137 * 2 ^ 59
def prefixEnd_6770137 : Nat := 4983230072969 + 3 ^ 40 * 6770137 * 2
def baseEnd_6770137 : Nat := 1158778125929427847184071

theorem tailTrace_6770137 : CollatzResearch.WordTrace tailWord_6770137 prefixEnd_6770137 1158778125929427847184071 := by
  unfold tailWord_6770137
  simp only [CollatzResearch.WordTrace]
  refine ⟨246927182273957371191156665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164618121515971580794104443 246927182273957371191156665)
  ·
    refine ⟨185195386705468028393367499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246927182273957371191156665 185195386705468028393367499)
    ·
      refine ⟨277793080058202042590051249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185195386705468028393367499 277793080058202042590051249)
      ·
        refine ⟨208344810043651531942538437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277793080058202042590051249 208344810043651531942538437)
        ·
          refine ⟨39064651883184662239225957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208344810043651531942538437 39064651883184662239225957)
          ·
            refine ⟨7324622228097124169854867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39064651883184662239225957 7324622228097124169854867)
            ·
              refine ⟨10986933342145686254782301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7324622228097124169854867 10986933342145686254782301)
              ·
                refine ⟨4120100003304632345543363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10986933342145686254782301 4120100003304632345543363)
                ·
                  refine ⟨6180150004956948518315045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120100003304632345543363 6180150004956948518315045)
                  ·
                    refine ⟨1158778125929427847184071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180150004956948518315045 1158778125929427847184071)
                    ·
                      rfl

theorem cell23_6770137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 4].length) (baseStart_6770137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770137 prefixEnd_6770137 := by exact prefixLift 6770137
  have htrace : WordTrace (prefixWord ++ tailWord_6770137) baseStart_6770137 baseEnd_6770137 := by
    simpa [prefixWord, tailWord_6770137, baseEnd_6770137] using wordTrace_append hprefix tailTrace_6770137
  have hstable : (prefixWord ++ tailWord_6770137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770137).length < 2 ^ (prefixWord ++ tailWord_6770137).sum := by decide
  have hdescent : baseEnd_6770137 < baseStart_6770137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770154 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_6770154 : Nat := 118140960795 + 6770154 * 2 ^ 59
def prefixEnd_6770154 : Nat := 4983230072969 + 3 ^ 40 * 6770154 * 2
def baseEnd_6770154 : Nat := 1158781035653136658346545

theorem tailTrace_6770154 : CollatzResearch.WordTrace tailWord_6770154 prefixEnd_6770154 1158781035653136658346545 := by
  unfold tailWord_6770154
  simp only [CollatzResearch.WordTrace]
  refine ⟨61731950578723945773631379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164618534876597188729683677 61731950578723945773631379)
  ·
    refine ⟨92597925868085918660447069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61731950578723945773631379 92597925868085918660447069)
    ·
      refine ⟨34724222200532219497667651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92597925868085918660447069 34724222200532219497667651)
      ·
        refine ⟨52086333300798329246501477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34724222200532219497667651 52086333300798329246501477)
        ·
          refine ⟨9766187493899686733719027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52086333300798329246501477 9766187493899686733719027)
          ·
            refine ⟨14649281240849530100578541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766187493899686733719027 14649281240849530100578541)
            ·
              refine ⟨5493480465318573787716953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14649281240849530100578541 5493480465318573787716953)
              ·
                refine ⟨4120110348988930340787715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493480465318573787716953 4120110348988930340787715)
                ·
                  refine ⟨6180165523483395511181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120110348988930340787715 6180165523483395511181573)
                  ·
                    refine ⟨1158781035653136658346545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180165523483395511181573 1158781035653136658346545)
                    ·
                      rfl

theorem cell23_6770154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_6770154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770154 prefixEnd_6770154 := by exact prefixLift 6770154
  have htrace : WordTrace (prefixWord ++ tailWord_6770154) baseStart_6770154 baseEnd_6770154 := by
    simpa [prefixWord, tailWord_6770154, baseEnd_6770154] using wordTrace_append hprefix tailTrace_6770154
  have hstable : (prefixWord ++ tailWord_6770154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770154).length < 2 ^ (prefixWord ++ tailWord_6770154).sum := by decide
  have hdescent : baseEnd_6770154 < baseStart_6770154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770160 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3]
def baseStart_6770160 : Nat := 118140960795 + 6770160 * 2 ^ 59
def prefixEnd_6770160 : Nat := 4983230072969 + 3 ^ 40 * 6770160 * 2
def baseEnd_6770160 : Nat := 3476346187843336951564607

theorem tailTrace_6770160 : CollatzResearch.WordTrace tailWord_6770160 prefixEnd_6770160 3476346187843336951564607 := by
  unfold tailWord_6770160
  simp only [CollatzResearch.WordTrace]
  refine ⟨123464010576437023059621967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164618680768582697412829289 123464010576437023059621967)
  ·
    refine ⟨185196015864655534589432951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123464010576437023059621967 185196015864655534589432951)
    ·
      refine ⟨277794023796983301884149427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185196015864655534589432951 277794023796983301884149427)
      ·
        refine ⟨416691035695474952826224141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277794023796983301884149427 416691035695474952826224141)
        ·
          refine ⟨156259138385803107309834053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416691035695474952826224141 156259138385803107309834053)
          ·
            refine ⟨29298588447338082620593885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156259138385803107309834053 29298588447338082620593885)
            ·
              refine ⟨10986970667751780982722707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29298588447338082620593885 10986970667751780982722707)
              ·
                refine ⟨16480456001627671474084061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10986970667751780982722707 16480456001627671474084061)
                ·
                  refine ⟨6180171000610376802781523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16480456001627671474084061 6180171000610376802781523)
                  ·
                    refine ⟨9270256500915565204172285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180171000610376802781523 9270256500915565204172285)
                    ·
                      refine ⟨3476346187843336951564607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270256500915565204172285 3476346187843336951564607)
                      ·
                        rfl

theorem cell23_6770160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_6770160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770160 prefixEnd_6770160 := by exact prefixLift 6770160
  have htrace : WordTrace (prefixWord ++ tailWord_6770160) baseStart_6770160 baseEnd_6770160 := by
    simpa [prefixWord, tailWord_6770160, baseEnd_6770160] using wordTrace_append hprefix tailTrace_6770160
  have hstable : (prefixWord ++ tailWord_6770160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770160).length < 2 ^ (prefixWord ++ tailWord_6770160).sum := by decide
  have hdescent : baseEnd_6770160 < baseStart_6770160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770180 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6770180 : Nat := 118140960795 + 6770180 * 2 ^ 59
def prefixEnd_6770180 : Nat := 4983230072969 + 3 ^ 40 * 6770180 * 2
def baseEnd_6770180 : Nat := 1158785485818808957771505

theorem tailTrace_6770180 : CollatzResearch.WordTrace tailWord_6770180 prefixEnd_6770180 1158785485818808957771505 := by
  unfold tailWord_6770180
  simp only [CollatzResearch.WordTrace]
  refine ⟨123464375306400794767485997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164619167075201059689981329 123464375306400794767485997)
  ·
    refine ⟨46299140739900298037807249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123464375306400794767485997 46299140739900298037807249)
    ·
      refine ⟨34724355554925223528355437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46299140739900298037807249 34724355554925223528355437)
      ·
        refine ⟨13021633333096958823133289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34724355554925223528355437 13021633333096958823133289)
        ·
          refine ⟨9766224999822719117349967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021633333096958823133289 9766224999822719117349967)
          ·
            refine ⟨14649337499734078676024951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766224999822719117349967 14649337499734078676024951)
            ·
              refine ⟨21974006249601118014037427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14649337499734078676024951 21974006249601118014037427)
              ·
                refine ⟨32961009374401677021056141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21974006249601118014037427 32961009374401677021056141)
                ·
                  refine ⟨12360378515400628882896053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32961009374401677021056141 12360378515400628882896053)
                  ·
                    refine ⟨1158785485818808957771505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12360378515400628882896053 1158785485818808957771505)
                    ·
                      rfl

theorem cell23_6770180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6770180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770180 prefixEnd_6770180 := by exact prefixLift 6770180
  have htrace : WordTrace (prefixWord ++ tailWord_6770180) baseStart_6770180 baseEnd_6770180 := by
    simpa [prefixWord, tailWord_6770180, baseEnd_6770180] using wordTrace_append hprefix tailTrace_6770180
  have hstable : (prefixWord ++ tailWord_6770180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770180).length < 2 ^ (prefixWord ++ tailWord_6770180).sum := by decide
  have hdescent : baseEnd_6770180 < baseStart_6770180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770187 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 2, 3, 2]
def baseStart_6770187 : Nat := 118140960795 + 6770187 * 2 ^ 59
def prefixEnd_6770187 : Nat := 4983230072969 + 3 ^ 40 * 6770187 * 2
def baseEnd_6770187 : Nat := 3476360051821008345926983

theorem tailTrace_6770187 : CollatzResearch.WordTrace tailWord_6770187 prefixEnd_6770187 3476360051821008345926983 := by
  unfold tailWord_6770187
  simp only [CollatzResearch.WordTrace]
  refine ⟨246929005923776229730476815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164619337282517486486984543 246929005923776229730476815)
  ·
    refine ⟨370393508885664344595715223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246929005923776229730476815 370393508885664344595715223)
    ·
      refine ⟨555590263328496516893572835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370393508885664344595715223 555590263328496516893572835)
      ·
        refine ⟨833385394992744775340359253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555590263328496516893572835 833385394992744775340359253)
        ·
          refine ⟨9766235097571227836019835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 833385394992744775340359253 9766235097571227836019835)
          ·
            refine ⟨14649352646356841754029753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766235097571227836019835 14649352646356841754029753)
            ·
              refine ⟨10987014484767631315522315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14649352646356841754029753 10987014484767631315522315)
              ·
                refine ⟨16480521727151446973283473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987014484767631315522315 16480521727151446973283473)
                ·
                  refine ⟨12360391295363585229962605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16480521727151446973283473 12360391295363585229962605)
                  ·
                    refine ⟨4635146735761344461235977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12360391295363585229962605 4635146735761344461235977)
                    ·
                      refine ⟨3476360051821008345926983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635146735761344461235977 3476360051821008345926983)
                      ·
                        rfl

theorem cell23_6770187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3, 2].length) (baseStart_6770187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770187 prefixEnd_6770187 := by exact prefixLift 6770187
  have htrace : WordTrace (prefixWord ++ tailWord_6770187) baseStart_6770187 baseEnd_6770187 := by
    simpa [prefixWord, tailWord_6770187, baseEnd_6770187] using wordTrace_append hprefix tailTrace_6770187
  have hstable : (prefixWord ++ tailWord_6770187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770187).length < 2 ^ (prefixWord ++ tailWord_6770187).sum := by decide
  have hdescent : baseEnd_6770187 < baseStart_6770187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770210 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6770210 : Nat := 118140960795 + 6770210 * 2 ^ 59
def prefixEnd_6770210 : Nat := 4983230072969 + 3 ^ 40 * 6770210 * 2
def baseEnd_6770210 : Nat := 1158790620625353918646459

theorem tailTrace_6770210 : CollatzResearch.WordTrace tailWord_6770210 prefixEnd_6770210 1158790620625353918646459 := by
  unfold tailWord_6770210
  simp only [CollatzResearch.WordTrace]
  refine ⟨61732461200673226164641021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164619896535128603105709389 61732461200673226164641021)
  ·
    refine ⟨23149672950252459811740383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61732461200673226164641021 23149672950252459811740383)
    ·
      refine ⟨34724509425378689717610575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23149672950252459811740383 34724509425378689717610575)
      ·
        refine ⟨52086764138068034576415863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34724509425378689717610575 52086764138068034576415863)
        ·
          refine ⟨78130146207102051864623795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52086764138068034576415863 78130146207102051864623795)
          ·
            refine ⟨117195219310653077796935693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78130146207102051864623795 117195219310653077796935693)
            ·
              refine ⟨43948207241494904173850885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117195219310653077796935693 43948207241494904173850885)
              ·
                refine ⟨8240288857780294532597041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43948207241494904173850885 8240288857780294532597041)
                ·
                  refine ⟨6180216643335220899447781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240288857780294532597041 6180216643335220899447781)
                  ·
                    refine ⟨1158790620625353918646459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180216643335220899447781 1158790620625353918646459)
                    ·
                      rfl

theorem cell23_6770210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6770210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770210 prefixEnd_6770210 := by exact prefixLift 6770210
  have htrace : WordTrace (prefixWord ++ tailWord_6770210) baseStart_6770210 baseEnd_6770210 := by
    simpa [prefixWord, tailWord_6770210, baseEnd_6770210] using wordTrace_append hprefix tailTrace_6770210
  have hstable : (prefixWord ++ tailWord_6770210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770210).length < 2 ^ (prefixWord ++ tailWord_6770210).sum := by decide
  have hdescent : baseEnd_6770210 < baseStart_6770210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770211 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 1, 1, 3]
def baseStart_6770211 : Nat := 118140960795 + 6770211 * 2 ^ 59
def prefixEnd_6770211 : Nat := 4983230072969 + 3 ^ 40 * 6770211 * 2
def baseEnd_6770211 : Nat := 3476372375356716252026873

theorem tailTrace_6770211 : CollatzResearch.WordTrace tailWord_6770211 prefixEnd_6770211 3476372375356716252026873 := by
  unfold tailWord_6770211
  simp only [CollatzResearch.WordTrace]
  refine ⟨246929881275689281829350487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164619920850459521219566991 246929881275689281829350487)
  ·
    refine ⟨370394821913533922744025731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246929881275689281829350487 370394821913533922744025731)
    ·
      refine ⟨555592232870300884116038597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370394821913533922744025731 555592232870300884116038597)
      ·
        refine ⟨104173543663181415771757237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 555592232870300884116038597 104173543663181415771757237)
        ·
          refine ⟨9766269718423257728602241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104173543663181415771757237 9766269718423257728602241)
          ·
            refine ⟨7324702288817443296451681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9766269718423257728602241 7324702288817443296451681)
            ·
              refine ⟨5493526716613082472338761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7324702288817443296451681 5493526716613082472338761)
              ·
                refine ⟨4120145037459811854254071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493526716613082472338761 4120145037459811854254071)
                ·
                  refine ⟨6180217556189717781381107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120145037459811854254071 6180217556189717781381107)
                  ·
                    refine ⟨9270326334284576672071661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180217556189717781381107 9270326334284576672071661)
                    ·
                      refine ⟨3476372375356716252026873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270326334284576672071661 3476372375356716252026873)
                      ·
                        rfl

theorem cell23_6770211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_6770211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770211 prefixEnd_6770211 := by exact prefixLift 6770211
  have htrace : WordTrace (prefixWord ++ tailWord_6770211) baseStart_6770211 baseEnd_6770211 := by
    simpa [prefixWord, tailWord_6770211, baseEnd_6770211] using wordTrace_append hprefix tailTrace_6770211
  have hstable : (prefixWord ++ tailWord_6770211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770211).length < 2 ^ (prefixWord ++ tailWord_6770211).sum := by decide
  have hdescent : baseEnd_6770211 < baseStart_6770211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770250 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_6770250 : Nat := 118140960795 + 6770250 * 2 ^ 59
def prefixEnd_6770250 : Nat := 4983230072969 + 3 ^ 40 * 6770250 * 2
def baseEnd_6770250 : Nat := 3476392401102241599439193

theorem tailTrace_6770250 : CollatzResearch.WordTrace tailWord_6770250 prefixEnd_6770250 3476392401102241599439193 := by
  unfold tailWord_6770250
  simp only [CollatzResearch.WordTrace]
  refine ⟨61732825930636997872505051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164620869148365327660013469 61732825930636997872505051)
  ·
    refine ⟨92599238895955496808757577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61732825930636997872505051 92599238895955496808757577)
    ·
      refine ⟨69449429171966622606568183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92599238895955496808757577 69449429171966622606568183)
      ·
        refine ⟨104174143757949933909852275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69449429171966622606568183 104174143757949933909852275)
        ·
          refine ⟨156261215636924900864778413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104174143757949933909852275 156261215636924900864778413)
          ·
            refine ⟨58597955863846837824291905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156261215636924900864778413 58597955863846837824291905)
            ·
              refine ⟨43948466897885128368218929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58597955863846837824291905 43948466897885128368218929)
              ·
                refine ⟨32961350173413846276164197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43948466897885128368218929 32961350173413846276164197)
                ·
                  refine ⟨6180253157515096176780787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32961350173413846276164197 6180253157515096176780787)
                  ·
                    refine ⟨9270379736272644265171181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180253157515096176780787 9270379736272644265171181)
                    ·
                      refine ⟨3476392401102241599439193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270379736272644265171181 3476392401102241599439193)
                      ·
                        rfl

theorem cell23_6770250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_6770250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770250 prefixEnd_6770250 := by exact prefixLift 6770250
  have htrace : WordTrace (prefixWord ++ tailWord_6770250) baseStart_6770250 baseEnd_6770250 := by
    simpa [prefixWord, tailWord_6770250, baseEnd_6770250] using wordTrace_append hprefix tailTrace_6770250
  have hstable : (prefixWord ++ tailWord_6770250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770250).length < 2 ^ (prefixWord ++ tailWord_6770250).sum := by decide
  have hdescent : baseEnd_6770250 < baseStart_6770250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770294 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6770294 : Nat := 118140960795 + 6770294 * 2 ^ 59
def prefixEnd_6770294 : Nat := 4983230072969 + 3 ^ 40 * 6770294 * 2
def baseEnd_6770294 : Nat := 3476414994251039427288991

theorem tailTrace_6770294 : CollatzResearch.WordTrace tailWord_6770294 prefixEnd_6770294 3476414994251039427288991 := by
  unfold tailWord_6770294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433306783399286687788871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164621939022925724669747957 15433306783399286687788871)
  ·
    refine ⟨23149960175098930031683307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15433306783399286687788871 23149960175098930031683307)
    ·
      refine ⟨34724940262648395047524961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23149960175098930031683307 34724940262648395047524961)
      ·
        refine ⟨26043705196986296285643721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34724940262648395047524961 26043705196986296285643721)
        ·
          refine ⟨19532778897739722214232791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26043705196986296285643721 19532778897739722214232791)
          ·
            refine ⟨29299168346609583321349187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19532778897739722214232791 29299168346609583321349187)
            ·
              refine ⟨43948752519914374982023781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29299168346609583321349187 43948752519914374982023781)
              ·
                refine ⟨8240391097483945309129459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43948752519914374982023781 8240391097483945309129459)
                ·
                  refine ⟨12360586646225917963694189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8240391097483945309129459 12360586646225917963694189)
                  ·
                    refine ⟨4635219992334719236385321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12360586646225917963694189 4635219992334719236385321)
                    ·
                      refine ⟨3476414994251039427288991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4635219992334719236385321 3476414994251039427288991)
                      ·
                        rfl

theorem cell23_6770294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6770294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770294 prefixEnd_6770294 := by exact prefixLift 6770294
  have htrace : WordTrace (prefixWord ++ tailWord_6770294) baseStart_6770294 baseEnd_6770294 := by
    simpa [prefixWord, tailWord_6770294, baseEnd_6770294] using wordTrace_append hprefix tailTrace_6770294
  have hstable : (prefixWord ++ tailWord_6770294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770294).length < 2 ^ (prefixWord ++ tailWord_6770294).sum := by decide
  have hdescent : baseEnd_6770294 < baseStart_6770294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770363 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_6770363 : Nat := 118140960795 + 6770363 * 2 ^ 59
def prefixEnd_6770363 : Nat := 4983230072969 + 3 ^ 40 * 6770363 * 2
def baseEnd_6770363 : Nat := 3476450424416199657326173

theorem tailTrace_6770363 : CollatzResearch.WordTrace tailWord_6770363 prefixEnd_6770363 3476450424416199657326173 := by
  unfold tailWord_6770363
  simp only [CollatzResearch.WordTrace]
  refine ⟨246935425171138611788883743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164623616780759074525922495 246935425171138611788883743)
  ·
    refine ⟨370403137756707917683325615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246935425171138611788883743 370403137756707917683325615)
    ·
      refine ⟨555604706635061876524988423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370403137756707917683325615 555604706635061876524988423)
      ·
        refine ⟨833407059952592814787482635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555604706635061876524988423 833407059952592814787482635)
        ·
          refine ⟨1250110589928889222181223953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833407059952592814787482635 1250110589928889222181223953)
          ·
            refine ⟨937582942446666916635917965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250110589928889222181223953 937582942446666916635917965)
            ·
              refine ⟨351593603417500093738469237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937582942446666916635917965 351593603417500093738469237)
              ·
                refine ⟨32961900320390633787981491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351593603417500093738469237 32961900320390633787981491)
                ·
                  refine ⟨49442850480585950681972237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32961900320390633787981491 49442850480585950681972237)
                  ·
                    refine ⟨18541068930219731505739589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49442850480585950681972237 18541068930219731505739589)
                    ·
                      refine ⟨3476450424416199657326173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18541068930219731505739589 3476450424416199657326173)
                      ·
                        rfl

theorem cell23_6770363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_6770363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770363 prefixEnd_6770363 := by exact prefixLift 6770363
  have htrace : WordTrace (prefixWord ++ tailWord_6770363) baseStart_6770363 baseEnd_6770363 := by
    simpa [prefixWord, tailWord_6770363, baseEnd_6770363] using wordTrace_append hprefix tailTrace_6770363
  have hstable : (prefixWord ++ tailWord_6770363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770363).length < 2 ^ (prefixWord ++ tailWord_6770363).sum := by decide
  have hdescent : baseEnd_6770363 < baseStart_6770363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770381 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 5]
def baseStart_6770381 : Nat := 118140960795 + 6770381 * 2 ^ 59
def prefixEnd_6770381 : Nat := 4983230072969 + 3 ^ 40 * 6770381 * 2
def baseEnd_6770381 : Nat := 386273296340886731877899

theorem tailTrace_6770381 : CollatzResearch.WordTrace tailWord_6770381 prefixEnd_6770381 386273296340886731877899 := by
  unfold tailWord_6770381
  simp only [CollatzResearch.WordTrace]
  refine ⟨246936081685073400863038997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164624054456715600575359331 246936081685073400863038997)
  ·
    refine ⟨11575128828987815665454953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246936081685073400863038997 11575128828987815665454953)
    ·
      refine ⟨8681346621740861749091215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11575128828987815665454953 8681346621740861749091215)
      ·
        refine ⟨13022019932611292623636823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681346621740861749091215 13022019932611292623636823)
        ·
          refine ⟨19533029898916938935455235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13022019932611292623636823 19533029898916938935455235)
          ·
            refine ⟨29299544848375408403182853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19533029898916938935455235 29299544848375408403182853)
            ·
              refine ⟨5493664659070389075596785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29299544848375408403182853 5493664659070389075596785)
              ·
                refine ⟨4120248494302791806697589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493664659070389075596785 4120248494302791806697589)
                ·
                  refine ⟨386273296340886731877899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4120248494302791806697589 386273296340886731877899)
                  ·
                    rfl

theorem cell23_6770381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_6770381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770381 prefixEnd_6770381 := by exact prefixLift 6770381
  have htrace : WordTrace (prefixWord ++ tailWord_6770381) baseStart_6770381 baseEnd_6770381 := by
    simpa [prefixWord, tailWord_6770381, baseEnd_6770381] using wordTrace_append hprefix tailTrace_6770381
  have hstable : (prefixWord ++ tailWord_6770381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770381).length < 2 ^ (prefixWord ++ tailWord_6770381).sum := by decide
  have hdescent : baseEnd_6770381 < baseStart_6770381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770400 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_6770400 : Nat := 118140960795 + 6770400 * 2 ^ 59
def prefixEnd_6770400 : Nat := 4983230072969 + 3 ^ 40 * 6770400 * 2
def baseEnd_6770400 : Nat := 3476469423200416012563503

theorem tailTrace_6770400 : CollatzResearch.WordTrace tailWord_6770400 prefixEnd_6770400 3476469423200416012563503 := by
  unfold tailWord_6770400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123468387336002283553990327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164624516448003044738653769 123468387336002283553990327)
  ·
    refine ⟨185202581004003425330985491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123468387336002283553990327 185202581004003425330985491)
    ·
      refine ⟨277803871506005137996478237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185202581004003425330985491 277803871506005137996478237)
      ·
        refine ⟨104176451814751926748679339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277803871506005137996478237 104176451814751926748679339)
        ·
          refine ⟨156264677722127890123019009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104176451814751926748679339 156264677722127890123019009)
          ·
            refine ⟨117198508291595917592264257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156264677722127890123019009 117198508291595917592264257)
            ·
              refine ⟨87898881218696938194198193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117198508291595917592264257 87898881218696938194198193)
              ·
                refine ⟨65924160914022703645648645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87898881218696938194198193 65924160914022703645648645)
                ·
                  refine ⟨12360780171379256933559121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65924160914022703645648645 12360780171379256933559121)
                  ·
                    refine ⟨9270585128534442700169341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12360780171379256933559121 9270585128534442700169341)
                    ·
                      refine ⟨3476469423200416012563503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270585128534442700169341 3476469423200416012563503)
                      ·
                        rfl

theorem cell23_6770400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_6770400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770400 prefixEnd_6770400 := by exact prefixLift 6770400
  have htrace : WordTrace (prefixWord ++ tailWord_6770400) baseStart_6770400 baseEnd_6770400 := by
    simpa [prefixWord, tailWord_6770400, baseEnd_6770400] using wordTrace_append hprefix tailTrace_6770400
  have hstable : (prefixWord ++ tailWord_6770400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770400).length < 2 ^ (prefixWord ++ tailWord_6770400).sum := by decide
  have hdescent : baseEnd_6770400 < baseStart_6770400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770417 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_6770417 : Nat := 118140960795 + 6770417 * 2 ^ 59
def prefixEnd_6770417 : Nat := 4983230072969 + 3 ^ 40 * 6770417 * 2
def baseEnd_6770417 : Nat := 3476478152371542446050925

theorem tailTrace_6770417 : CollatzResearch.WordTrace tailWord_6770417 prefixEnd_6770417 3476478152371542446050925 := by
  unfold tailWord_6770417
  simp only [CollatzResearch.WordTrace]
  refine ⟨246937394712942979011349505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164624929808628652674233003 246937394712942979011349505)
  ·
    refine ⟨185203046034707234258512129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246937394712942979011349505 185203046034707234258512129)
    ·
      refine ⟨138902284526030425693884097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185203046034707234258512129 138902284526030425693884097)
      ·
        refine ⟨104176713394522819270413073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138902284526030425693884097 104176713394522819270413073)
        ·
          refine ⟨78132535045892114452809805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104176713394522819270413073 78132535045892114452809805)
          ·
            refine ⟨29299700642209542919803677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78132535045892114452809805 29299700642209542919803677)
            ·
              refine ⟨10987387740828578594926379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29299700642209542919803677 10987387740828578594926379)
              ·
                refine ⟨16481081611242867892389569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987387740828578594926379 16481081611242867892389569)
                ·
                  refine ⟨12360811208432150919292177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16481081611242867892389569 12360811208432150919292177)
                  ·
                    refine ⟨9270608406324113189469133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12360811208432150919292177 9270608406324113189469133)
                    ·
                      refine ⟨3476478152371542446050925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270608406324113189469133 3476478152371542446050925)
                      ·
                        rfl

theorem cell23_6770417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_6770417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770417 prefixEnd_6770417 := by exact prefixLift 6770417
  have htrace : WordTrace (prefixWord ++ tailWord_6770417) baseStart_6770417 baseEnd_6770417 := by
    simpa [prefixWord, tailWord_6770417, baseEnd_6770417] using wordTrace_append hprefix tailTrace_6770417
  have hstable : (prefixWord ++ tailWord_6770417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770417).length < 2 ^ (prefixWord ++ tailWord_6770417).sum := by decide
  have hdescent : baseEnd_6770417 < baseStart_6770417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770481 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 1, 1, 3]
def baseStart_6770481 : Nat := 118140960795 + 6770481 * 2 ^ 59
def prefixEnd_6770481 : Nat := 4983230072969 + 3 ^ 40 * 6770481 * 2
def baseEnd_6770481 : Nat := 3476511015133430195650631

theorem tailTrace_6770481 : CollatzResearch.WordTrace tailWord_6770481 prefixEnd_6770481 3476511015133430195650631 := by
  unfold tailWord_6770481
  simp only [CollatzResearch.WordTrace]
  refine ⟨246939728984711117941679297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164626485989807411961119531 246939728984711117941679297)
  ·
    refine ⟨185204796738533338456259473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246939728984711117941679297 185204796738533338456259473)
    ·
      refine ⟨138903597553900003842194605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185204796738533338456259473 138903597553900003842194605)
      ·
        refine ⟨52088849082712501440822977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138903597553900003842194605 52088849082712501440822977)
        ·
          refine ⟨39066636812034376080617233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52088849082712501440822977 39066636812034376080617233)
          ·
            refine ⟨29299977609025782060462925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39066636812034376080617233 29299977609025782060462925)
            ·
              refine ⟨10987491603384668272673597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29299977609025782060462925 10987491603384668272673597)
              ·
                refine ⟨4120309351269250602252599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10987491603384668272673597 4120309351269250602252599)
                ·
                  refine ⟨6180464026903875903378899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120309351269250602252599 6180464026903875903378899)
                  ·
                    refine ⟨9270696040355813855068349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180464026903875903378899 9270696040355813855068349)
                    ·
                      refine ⟨3476511015133430195650631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270696040355813855068349 3476511015133430195650631)
                      ·
                        rfl

theorem cell23_6770481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_6770481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770481 prefixEnd_6770481 := by exact prefixLift 6770481
  have htrace : WordTrace (prefixWord ++ tailWord_6770481) baseStart_6770481 baseEnd_6770481 := by
    simpa [prefixWord, tailWord_6770481, baseEnd_6770481] using wordTrace_append hprefix tailTrace_6770481
  have hstable : (prefixWord ++ tailWord_6770481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770481).length < 2 ^ (prefixWord ++ tailWord_6770481).sum := by decide
  have hdescent : baseEnd_6770481 < baseStart_6770481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770484 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_6770484 : Nat := 118140960795 + 6770484 * 2 ^ 59
def prefixEnd_6770484 : Nat := 4983230072969 + 3 ^ 40 * 6770484 * 2
def baseEnd_6770484 : Nat := 1158837518525131227971039

theorem tailTrace_6770484 : CollatzResearch.WordTrace tailWord_6770484 prefixEnd_6770484 1158837518525131227971039 := by
  unfold tailWord_6770484
  simp only [CollatzResearch.WordTrace]
  refine ⟨123469919201850124727019253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164626558935800166302692337 123469919201850124727019253)
  ·
    refine ⟨11575304925173449193158055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123469919201850124727019253 11575304925173449193158055)
    ·
      refine ⟨17362957387760173789737083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575304925173449193158055 17362957387760173789737083)
      ·
        refine ⟨26044436081640260684605625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362957387760173789737083 26044436081640260684605625)
        ·
          refine ⟨19533327061230195513454219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26044436081640260684605625 19533327061230195513454219)
          ·
            refine ⟨29299990591845293270181329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19533327061230195513454219 29299990591845293270181329)
            ·
              refine ⟨21974992943883969952635997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29299990591845293270181329 21974992943883969952635997)
              ·
                refine ⟨8240622353956488732238499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21974992943883969952635997 8240622353956488732238499)
                ·
                  refine ⟨12360933530934733098357749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8240622353956488732238499 12360933530934733098357749)
                  ·
                    refine ⟨1158837518525131227971039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12360933530934733098357749 1158837518525131227971039)
                    ·
                      rfl

theorem cell23_6770484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_6770484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770484 prefixEnd_6770484 := by exact prefixLift 6770484
  have htrace : WordTrace (prefixWord ++ tailWord_6770484) baseStart_6770484 baseEnd_6770484 := by
    simpa [prefixWord, tailWord_6770484, baseEnd_6770484] using wordTrace_append hprefix tailTrace_6770484
  have hstable : (prefixWord ++ tailWord_6770484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770484).length < 2 ^ (prefixWord ++ tailWord_6770484).sum := by decide
  have hdescent : baseEnd_6770484 < baseStart_6770484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770514 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_6770514 : Nat := 118140960795 + 6770514 * 2 ^ 59
def prefixEnd_6770514 : Nat := 4983230072969 + 3 ^ 40 * 6770514 * 2
def baseEnd_6770514 : Nat := 1158842653331676188845993

theorem tailTrace_6770514 : CollatzResearch.WordTrace tailWord_6770514 prefixEnd_6770514 1158842653331676188845993 := by
  unfold tailWord_6770514
  simp only [CollatzResearch.WordTrace]
  refine ⟨61735233148397891144407649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164627288395727709718420397 61735233148397891144407649)
  ·
    refine ⟨46301424861298418358305737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61735233148397891144407649 46301424861298418358305737)
    ·
      refine ⟨34726068645973813768729303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46301424861298418358305737 34726068645973813768729303)
      ·
        refine ⟨52089102968960720653093955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34726068645973813768729303 52089102968960720653093955)
        ·
          refine ⟨78133654453441080979640933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52089102968960720653093955 78133654453441080979640933)
          ·
            refine ⟨14650060210020202683682675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78133654453441080979640933 14650060210020202683682675)
            ·
              refine ⟨21975090315030304025524013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14650060210020202683682675 21975090315030304025524013)
              ·
                refine ⟨8240658868136364009571505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21975090315030304025524013 8240658868136364009571505)
                ·
                  refine ⟨6180494151102273007178629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8240658868136364009571505 6180494151102273007178629)
                  ·
                    refine ⟨1158842653331676188845993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180494151102273007178629 1158842653331676188845993)
                    ·
                      rfl

theorem cell23_6770514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_6770514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770514 prefixEnd_6770514 := by exact prefixLift 6770514
  have htrace : WordTrace (prefixWord ++ tailWord_6770514) baseStart_6770514 baseEnd_6770514 := by
    simpa [prefixWord, tailWord_6770514, baseEnd_6770514] using wordTrace_append hprefix tailTrace_6770514
  have hstable : (prefixWord ++ tailWord_6770514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770514).length < 2 ^ (prefixWord ++ tailWord_6770514).sum := by decide
  have hdescent : baseEnd_6770514 < baseStart_6770514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6770537 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 3]
def baseStart_6770537 : Nat := 118140960795 + 6770537 * 2 ^ 59
def prefixEnd_6770537 : Nat := 4983230072969 + 3 ^ 40 * 6770537 * 2
def baseEnd_6770537 : Nat := 3476539770050081976550373

theorem tailTrace_6770537 : CollatzResearch.WordTrace tailWord_6770537 prefixEnd_6770537 3476539770050081976550373 := by
  unfold tailWord_6770537
  simp only [CollatzResearch.WordTrace]
  refine ⟨246941771472508239505717865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164627847648338826337145243 246941771472508239505717865)
  ·
    refine ⟨185206328604381179629288399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246941771472508239505717865 185206328604381179629288399)
    ·
      refine ⟨277809492906571769443932599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185206328604381179629288399 277809492906571769443932599)
      ·
        refine ⟨416714239359857654165898899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277809492906571769443932599 416714239359857654165898899)
        ·
          refine ⟨625071359039786481248848349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416714239359857654165898899 625071359039786481248848349)
          ·
            refine ⟨234401759639919930468318131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625071359039786481248848349 234401759639919930468318131)
            ·
              refine ⟨351602639459879895702477197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234401759639919930468318131 351602639459879895702477197)
              ·
                refine ⟨131850989797454960888428949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351602639459879895702477197 131850989797454960888428949)
                ·
                  refine ⟨6180515146755701291645107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131850989797454960888428949 6180515146755701291645107)
                  ·
                    refine ⟨9270772720133551937467661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6180515146755701291645107 9270772720133551937467661)
                    ·
                      refine ⟨3476539770050081976550373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9270772720133551937467661 3476539770050081976550373)
                      ·
                        rfl

theorem cell23_6770537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_6770537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6770537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6770537 prefixEnd_6770537 := by exact prefixLift 6770537
  have htrace : WordTrace (prefixWord ++ tailWord_6770537) baseStart_6770537 baseEnd_6770537 := by
    simpa [prefixWord, tailWord_6770537, baseEnd_6770537] using wordTrace_append hprefix tailTrace_6770537
  have hstable : (prefixWord ++ tailWord_6770537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6770537).length < 2 ^ (prefixWord ++ tailWord_6770537).sum := by decide
  have hdescent : baseEnd_6770537 < baseStart_6770537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6770537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
